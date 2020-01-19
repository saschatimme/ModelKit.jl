const TSYSTEM_TABLE = Dict{
    UInt,
    Vector{Tuple{Vector{Expression},Vector{Variable},Vector{Variable}}},
}()

struct TSystem{H,I} end

function TSystem(
    exprs::Vector{Expression},
    var_order::Vector{Variable},
    param_order::Vector{Variable} = Variable[],
)
    val = (exprs, var_order, param_order)
    h = hash(val)
    if haskey(TSYSTEM_TABLE, h)
        # check that it is identical
        for (i, vi) in enumerate(TSYSTEM_TABLE[h])
            if vi == val
                return TSystem{h,i}()
            end
        end
        push!(TSYSTEM_TABLE[h], val)
        return TSystem{h,length(TSYSTEM_TABLE[h])}()
    else
        TSYSTEM_TABLE[h] = [val]
        return TSystem{h,1}()
    end
end

function Base.show(io::IO, TS::TSystem)
    print(io, "TSystem encoding: ")
    show(io, interpret(TS))
end

interpret(TS::TSystem) = interpret(typeof(TS))
interpret(::Type{TSystem{H,I}}) where {H,I} = System(TSYSTEM_TABLE[H][I]...)

const THOMOTOPY_TABLE = Dict{
    UInt,
    Vector{Tuple{Vector{Expression},Vector{Variable},Variable,Vector{Variable}}},
}()

struct THomotopy{H,I} end

function THomotopy(
    exprs::Vector{<:Expression},
    var_order::AbstractVector{<:Variable},
    t::Variable,
    param_order::AbstractVector{<:Variable} = Variable[],
)
    val = (exprs, var_order, t, param_order)
    h = hash(val)
    if haskey(THOMOTOPY_TABLE, h)
    # check that it is identical
        for (i, vi) in enumerate(THOMOTOPY_TABLE[h])
            if vi == val
                return THomotopy{h,i}()
            end
        end
        push!(THOMOTOPY_TABLE[h], val)
        return THomotopy{h,length(TSYSTEM_TABLE[h])}()
    else
        THOMOTOPY_TABLE[h] = [val]
        return THomotopy{h,1}()
    end
end

function Base.show(io::IO, TH::THomotopy)
    print(io, "THomotopy encoding: ")
    show(io, interpret(TH))
end

interpret(TH::THomotopy) = interpret(typeof(TH))
interpret(::Type{THomotopy{H,I}}) where {H,I} = Homotopy(THOMOTOPY_TABLE[H][I]...)

type_level(sys::System) = TSystem(sys.expressions, sys.variables, sys.parameters)
type_level(sys::Homotopy) = THomotopy(sys.expressions, sys.variables, sys.t, sys.parameters)

#############
## Helpers ##
#############

@inline sqr(x::Real) = x * x
@inline function sqr(z::Complex)
    x, y = reim(z)
    Complex((x + y) * (x - y), (x + x) * y)
end

function _unrolled_pow_impl(n)
    n == 0 && return :(one(x1))
    n == 1 && return :x1
    n == 2 && return :(sqr(x1))
    n == 3 && return :(x1 * sqr(x1))
    n == 4 && return :(sqr(sqr(x1)))
    n == 5 && return :(x1 * sqr(sqr(x1)))

    d = digits(n, base = 2)
    exprs = map(2:length(d)) do i
        :($(Symbol(:x, 1 << (i - 1))) = sqr($(Symbol(:x, 1 << (i - 2)))))
    end
    prods = Symbol[]
    for (i, di) in enumerate(d)
        if !iszero(di)
            push!(prods, Symbol(:x, 1 << (i - 1)))
        end
    end
    Expr(:block, exprs..., Expr(:call, :*, prods...))
end

@generated function unrolled_pow(x1::Number, ::Val{N}) where {N}
    quote
        Base.@_inline_meta
        $(_unrolled_pow_impl(N))
    end
end

## Map symengine classes to function names
const TYPE_CALL_DICT = Dict(
    :Add => :+,
    :Sub => :-,
    :Mul => :*,
    :Div => :/,
    :Pow => :^,
    :re => :real,
    :im => :imag,
)

function type_to_call(t)
    if haskey(TYPE_CALL_DICT, t)
        TYPE_CALL_DICT[t]
    else
        v = Symbol(lowercase(string(t)))
        TYPE_CALL_DICT[t] = v
        v
    end
end

to_expr(var::Variable) = Symbol(SE.toString(var))
function to_expr(ex::Expression, var_dict = Dict{Expression,Symbol}())
    t = type(ex)
    if t == :Symbol
        if !isnothing(var_dict) && haskey(var_dict, ex)
            return var_dict[ex]
        else
            s = Symbol(SE.toString(ex))
            if !isnothing(var_dict)
                var_dict[copy(ex)] = s
            end
            return s
        end
    elseif t == :Integer
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
    elseif t == :RealDouble
        return convert(Cdouble, SE.BasicType{Val{:RealDouble}}(ex))
    elseif t == :Pow
        vec = UnsafeVecBasicIterator(args(ex))
        v = vec[1]
        if type(v) == :Symbol
            if !isnothing(var_dict) && haskey(var_dict, v)
                x = var_dict[v]
            else
                x = Symbol(SE.toString(v))
                if !isnothing(var_dict)
                    var_dict[copy(v)] = x
                end
            end
        else
            x = to_expr(v, var_dict)
        end
        k = convert(Int, vec[2])
        return Expr(:call, :unrolled_pow, x, :(Val($k)))
    elseif t in NUMBER_TYPES || (t == :Constant)
        return SE.N(ex)
    else
        vec = UnsafeVecBasicIterator(args(ex))
        exprs = map(v -> to_expr(v, var_dict), vec)
        n = length(exprs)
        if n ≥ 32 && (t == :Add || t == :Mul)
            while n ≥ 32
                exprs = map(1:31:n) do i
                    Expr(:call, type_to_call(t), exprs[i:min(n, i + 30)]...)
                end
                n = length(exprs)
            end
        end
        Expr(:call, type_to_call(t), exprs...)
    end
end

function cse(exprs...)
    vec = convert(SE.CVecBasic, exprs...)
    replacement_syms = VecBasic()
    replacement_exprs = VecBasic()
    reduced_exprs = VecBasic()
    ccall(
        (:basic_cse, SE.libsymengine),
        Nothing,
        (Ptr{Cvoid}, Ptr{Cvoid}, Ptr{Cvoid}, Ptr{Cvoid}),
        replacement_syms.ptr,
        replacement_exprs.ptr,
        reduced_exprs.ptr,
        vec.ptr,
    )
    return replacement_syms, replacement_exprs, reduced_exprs
end


boundscheck_var_dict(F::System) =
    boundscheck_var_dict(F.expressions, F.variables, F.parameters)
boundscheck_var_dict(H::Homotopy) =
    boundscheck_var_dict(H.expressions, H.variables, H.parameters, H.t)

function boundscheck_var_dict(exprs, vars, params, t = nothing)
    n = length(exprs)
    m = length(vars)
    l = length(params)
    var_dict = Dict{Expression,Union{Symbol,Expr}}()
    for i = 1:m
        var_dict[Expression(vars[i])] = :(x[$i])
    end
    for i = 1:l
        var_dict[Expression(params[i])] = :(p[$i])
    end
    if t !== nothing
        var_dict[Expression(t)] = :(t)
    end

    checks = quote
        @boundscheck checkbounds(u, 1:$n)
        @boundscheck checkbounds(x, 1:$m)
        @boundscheck p === nothing || checkbounds(p, 1:$l)
    end

    checks, var_dict
end

function codegen(
    exprs::Vector{Expression},
    var_dict = Dict{Expression,Symbol}();
    output_name::Symbol = gensym(:u),
)
    lhs, rhs, out = ModelKit.cse(exprs)
    exprs = map(lhs, rhs) do ai, bi
        :($(ModelKit.to_expr(ai, var_dict)) = $(ModelKit.to_expr(bi, var_dict)))
    end
    for (i, ci) in enumerate(out)
        push!(exprs, :($(output_name)[$i] = $(ModelKit.to_expr(ci, var_dict))))
    end
    Expr(:block, exprs...)
end

function _evaluate!_impl(::Type{T}) where {T<:Union{TSystem, THomotopy}}
    I = interpret(T)
    checks, var_dict = boundscheck_var_dict(I)
    quote
        $checks
        @inbounds $(codegen(I.expressions, var_dict; output_name = :u))
        u
    end
end
@generated function evaluate!(u, ::T, x, p = nothing) where {T<:TSystem}
    _evaluate!_impl(T)
end
@generated function evaluate!(u, ::T, x, t, p = nothing) where {T<:THomotopy}
    _evaluate!_impl(T)
end
