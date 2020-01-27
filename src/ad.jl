struct InstructionList
    instructions::Vector{Pair{Symbol,<:Any}}
    var::Symbol
    n::Base.RefValue{Int}
end

function InstructionList(; var::Symbol = :ι, n::Base.RefValue{Int} = Ref(0))
    InstructionList(Pair{Symbol,<:Any}[], var, n)
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


function InstructionList(exprs::Vector{Expression}; perform_cse = true)
    v = InstructionList()
    PSE = Set{Symbol}()
    if perform_cse
        exprs, CSE = cse(exprs)
    else
        CSE = Dict{Expression,Expression}()
    end
    v, map(ex -> flat_expr!(v, ex, CSE, PSE), exprs)
end

function InstructionList(
    ex::Expression,
    common_subexpression = Dict{Expression,Expression}(),
)
    v = InstructionList()
    flat_expr!(v, ex, common_subexpression)
    v
end


function flat_expr!(
    v,
    ex::Expression,
    # common sub expression
    CSE::Dict{Expression,Expression},
    # processed sub expression
    PSE::Set{Symbol} = Set{Symbol}(),
)
    t = ModelKit.type(ex)
    if t == :Symbol
        s = Symbol(SE.toString(ex))
        if haskey(CSE, ex) && s ∉ PSE
            push!(PSE, s)
            val = flat_expr!(v, CSE[ex], CSE, PSE)
            if val isa Symbol
                v.instructions[end] = s => last(v.instructions[end])
            else
                push!(v, s => val)
            end
        end
        return Symbol(SE.toString(ex))
    elseif t == :Integer
        return to_smallest_integer(ex)
    elseif t == :RealDouble
        return convert(Cdouble, SE.BasicType{Val{:RealDouble}}(ex))
    elseif t in ModelKit.NUMBER_TYPES || (t == :Constant)
        return SE.N(ex)
    elseif t == :Pow
        x, k = ModelKit.args(ex)
        return push!(v, (:^, flat_expr!(v, x, CSE, PSE), convert(Int, k)))
    elseif t == :Add || t == :Mul
        op = t == :Add ? :+ : :*
        vec = ModelKit.args(ex)
        op_arg = flat_expr!(v, vec[1], CSE, PSE)
        for i = 2:length(vec)
            op_arg = push!(v, (op, op_arg, flat_expr!(v, vec[i], CSE, PSE)))
        end
        return op_arg
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


function Base.diff(
    list::InstructionList,
    vars::Vector{Symbol},
    f::Vector{Symbol},
)
    seed = Dict{Tuple{Symbol,Int},Any}()
    for (i, v) in enumerate(vars)
        seed[(v, i)] = 1
    end
    dlist = diff!(list, length(vars), seed)

    J = Matrix{Union{Nothing,Symbol}}(undef, length(f), length(vars))
    for (j, v) in enumerate(vars), (i, fi) in enumerate(f)
        if haskey(seed, (fi, j))
            J[i, j] = seed[(fi, j)]::Symbol
        else
            J[i, j] = nothing
        end
    end
    dlist, J
end

function diff!(list::InstructionList, N::Int, diff_map)
    n = length(list)
    v = InstructionList(n = Ref(n))
    for (id, el::Tuple{Symbol,Any,Any}) in list.instructions
        (op, arg1, arg2) = el

        if op == :^
            p1 = p2 = :NONE
            instr_added = false
            for ∂i = 1:N
                exp::Int = arg2
                if haskey(diff_map, (arg1, ∂i))
                    if p2 == :NONE
                        if exp == 2
                            p2 = push!(v, (:*, 2, arg1))
                        else
                            p1 = push!(v, (:^, arg1, exp - 1))
                            p2 = push!(v, (:*, exp, p1))
                        end
                    end
                    if !instr_added
                        if exp == 2
                            push!(v, id => (:*, arg1, arg1))
                        else
                            push!(v, id => (:*, p1, arg1))
                        end
                        instr_added = true
                    end
                    ∂el = diff_map[(arg1, ∂i)]
                    if ∂el != 1
                        diff_map[(id, ∂i)] = push!(v, (:*, p2, ∂el))
                    else
                        diff_map[(id, ∂i)] = p2
                    end
                elseif p2 != :NONE && !instr_added
                    push!(v, id => el)
                    instr_added = true
                end
            end
            if !instr_added
                push!(v, id => el)
            end
        elseif op == :*
            for ∂i = 1:N
                ∂i == 1 && push!(v, id => el)

                has_∂1 = haskey(diff_map, (arg1, ∂i))
                has_∂2 = haskey(diff_map, (arg2, ∂i))

                if has_∂2
                    a2::Symbol = arg2
                    ∂arg2 = diff_map[(a2, ∂i)]
                    if ∂arg2 != 1
                        e1 = push!(v, (:*, arg1, ∂arg2))
                    else
                        e1 = arg1
                    end
                end

                if has_∂1
                    a1::Symbol = arg1
                    ∂arg1 = diff_map[(a1, ∂i)]
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
            end
        elseif op == :+
            for ∂i = 1:N
                ∂i == 1 && push!(v, id => el)

                has_∂1 = haskey(diff_map, (arg1, ∂i))
                has_∂2 = haskey(diff_map, (arg2, ∂i))

                if has_∂1 && has_∂2
                    diff_map[(id, ∂i)] = push!(
                        v,
                        (:+, diff_map[(arg1, ∂i)], diff_map[(arg2, ∂i)]),
                    )
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
