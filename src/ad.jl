struct InstructionList
    instructions::OrderedDict{Symbol,Any}
    var::Symbol
    n::Base.RefValue{Int}
end

function InstructionList(; var::Symbol = :ι, n::Base.RefValue{Int} = Ref(0))
    InstructionList(OrderedDict{Symbol,Any}(), var, n)
end

function Base.push!(v::InstructionList, x)
    id = Symbol(v.var, v.n[] += 1)
    push!(v.instructions, id => x)
    id
end
function Base.push!(v::InstructionList, x::Pair{Symbol,<:Any})
    push!(v.instructions, x)
    first(x)
end

Base.length(v::InstructionList) = v.n[]

function Base.show(io::IO, v::InstructionList)
    for (id, arg) in v.instructions
        println(io, :($id = $(Expr(:call, arg...))))
    end
end


function InstructionList(ex::Expression)
    v = InstructionList()
    flat_expr!(v, ex)
    v
end
function flat_expr!(v, ex::Expression)
    t = ModelKit.type(ex)
    if t == :Symbol
        return Symbol(SE.toString(ex))
    elseif t == :Integer
        return to_smallest_integer(ex)
    elseif t == :RealDouble
        return convert(Cdouble, SE.BasicType{Val{:RealDouble}}(ex))
    elseif t in ModelKit.NUMBER_TYPES || (t == :Constant)
        return SE.N(ex)
    elseif t == :Pow
        x, k = ModelKit.args(ex)
        return push!(v, (:^, flat_expr!(v, x), convert(Int, k)))
    elseif t == :Add || t == :Mul
        op = t == :Add ? :+ : :*
        vec = ModelKit.args(ex)
        e_prev = flat_expr!(v, vec[1])
        e_new = :none
        for i = 2:length(vec)
            e = flat_expr!(v, vec[i])
            e_new = push!(v, (op, e_prev, e))
            e_prev, e = e, e_new
        end
        return e_new
    else
        error("Not supported: ", ex)
    end
end



function to_smallest_integer(ex)
    x = convert(BigInt, SE.BasicType{Val{:Integer}}(ex))
    if typemin(Int32) ≤ x ≤ typemax(Int32)
        return convert(Int32, x)
    elseif typemin(Int64) ≤ x ≤ typemax(Int64)
        return convert(Int64, x)
    elseif typemin(Int128) ≤ x ≤ typemax(Int128)
        return convert(Int128, x)
    else
        return x
    end
end



function diff_list(list::InstructionList, N::Int, diff_map)
    n = length(list)
    v = InstructionList(n = Ref(n))
    for (id, el) in list.instructions
        (op, arg1, arg2) = el

        for ∂i in 1:N
            if op == :^
                arg2::Int
                if haskey(diff_map, (arg1, ∂i))
                    e1 = push!(v, (:^, arg1, arg2 - 1))
                    ∂i == 1 && push!(v, id => (:*, e1, arg1))
                    e2 = push!(v, (:*, arg2, e1))

                    ∂el = diff_map[(arg1, ∂i)]
                    if ∂el != 1
                        diff_map[(id, ∂i)] = push!(v, (:*, e2, ∂el))
                    else
                        diff_map[(id, ∂i)] = e2
                    end
                else ∂i == 1
                    push!(v, id => el)
                end
            elseif op == :*
                ∂i == 1 && push!(v, id => el)

                has_∂1 = haskey(diff_map, (arg1, ∂i))
                has_∂2 = haskey(diff_map, (arg2, ∂i))

                if has_∂2
                    ∂arg2 = diff_map[(arg2, ∂i)]
                    if ∂arg2 != 1
                        e1 = push!(v, (:*, arg1, ∂arg2))
                    else
                        e1 = arg1
                    end
                end

                if has_∂1
                    ∂arg1 = diff_map[(arg1, ∂i)]
                    if ∂arg1 != 1
                        e2 = push!(v, (:*, ∂arg1, arg2))
                    else
                        e2 = arg2
                    end
                end

                if has_∂1 && has_∂2
                    diff_map[(id, ∂i)] = push!(v, (:+, e1, e2))
                elseif has_∂1
                    diff_map[(id, ∂i)] = e2
                elseif has_∂2
                    diff_map[(id, ∂i)] = e1
                end
            elseif op == :+
                ∂i == 1 && push!(v, id => el)

                has_∂1 = haskey(diff_map, (arg1, ∂i))
                has_∂2 = haskey(diff_map, (arg2, ∂i))

                if has_∂1 && has_∂2
                    diff_map[(id, ∂i)] = push!(v, (:+, diff_map[(arg1, ∂i)], diff_map[(arg2, ∂i)]))
                elseif has_∂1
                    diff_map[(id, ∂i)] = diff_map[(arg1, ∂i)]
                elseif has_∂2
                    diff_map[(id, ∂i)] = diff_map[(arg2, ∂i)]
                end
            end
        end
    end
    v
end
