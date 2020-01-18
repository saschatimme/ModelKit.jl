function to_type_level(
    f::Vector{<:Expression},
    var_order::AbstractVector{Variable},
    param_order::AbstractVector{Variable} = Variable[],
)
    Tuple{
        GeneralizedGenerated.NGG.to_typelist(convert.(Expr, f)),
        GeneralizedGenerated.NGG.to_typelist(convert.(Expr, var_order)),
        GeneralizedGenerated.NGG.to_typelist(convert.(Expr, param_order)),
    }
end
function from_type_level(::Type{Tuple{E,V,P}}) where {E,V,P}
    convert.(Expression, GeneralizedGenerated.from_type(E)),
    Variable.(GeneralizedGenerated.from_type(V)),
    Variable.(GeneralizedGenerated.from_type(P))
end

struct TSystem{TS,TE,V,P} end

type_level(sys::System) = typeof(TSystem(sys.expressions, sys.variables, sys.parameters))
function TSystem(
    exprs::Vector{<:Expression},
    var_order::AbstractVector{Variable},
    param_order::AbstractVector{Variable} = Variable[],
)
    TS = Tuple{length(exprs),length(var_order),length(param_order)}
    TE = GeneralizedGenerated.NGG.to_typelist(convert.(Expr, exprs))
    V = GeneralizedGenerated.NGG.to_typelist(Symbol.(var_order))
    P = GeneralizedGenerated.NGG.to_typelist(Symbol.(param_order))
    TSystem{TS,TE,V,P}()
end

Base.show(io::IO, ::Type{T}) where {T<:TSystem} = show_info(io, T)
function Base.show(io::IO, TS::TSystem)
    show_info(io, typeof(TS))
    print(io, "()")
end
function show_info(io::IO, ::Type{TSystem{Tuple{n,N,m},TE,V,P}}) where {n,N,m,TE,V,P}
    print(io, "TSystem{$n,$N,$m,#$(hash(TE))}")
end

interpret(TS::TSystem) = interpret(typeof(TS))
function interpret(::Type{TSystem{TS,TE,V,P}}) where {TS,TE,V,P}
    exprs = convert.(Expression, GeneralizedGenerated.from_type(TE))
    vars = Variable.(GeneralizedGenerated.from_type(V))
    params = convert(Vector{Variable}, collect(GeneralizedGenerated.from_type(P)))
    System(exprs, vars, params)
end


struct THomotopy{TS,TE,V,T,P} end

type_level(sys::Homotopy) =
    typeof(THomotopy(sys.expressions, sys.variables, sys.t, sys.parameters))
function THomotopy(
    exprs::Vector{<:Expression},
    var_order::AbstractVector{<:Variable},
    t::Variable,
    param_order::AbstractVector{<:Variable} = Variable[],
)
    TS = Tuple{length(exprs),length(var_order),length(param_order)}
    TE = GeneralizedGenerated.NGG.to_typelist(convert.(Expr, exprs))
    V = GeneralizedGenerated.NGG.to_typelist(Symbol.(var_order))
    T = Symbol(t)
    P = GeneralizedGenerated.NGG.to_typelist(Symbol.(param_order))
    THomotopy{TS,TE,V,T,P}()
end

Base.show(io::IO, ::Type{T}) where {T<:THomotopy} = show_info(io, T)
function Base.show(io::IO, TS::THomotopy)
    show_info(io, typeof(TS))
    print(io, "()")
end
function show_info(io::IO, ::Type{<:THomotopy{Tuple{n,N,m},TE}}) where {n,N,m,TE}
    print(io, "THomotopy{$n,$N,$m,#$(hash(TE))}")
end

interpret(TS::THomotopy) = interpret(typeof(TS))
function interpret(::Type{THomotopy{TS,TE,V,T,P}}) where {TS,TE,V,T,P}
    exprs = convert.(Expression, GeneralizedGenerated.from_type(TE))
    vars = Variable.(GeneralizedGenerated.from_type(V))
    t = Variable(T)
    params = convert(Vector{Variable}, collect(GeneralizedGenerated.from_type(P)))

    Homotopy(exprs, vars, t, params)
end


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
function to_expr(ex::Expression, var_dict = Dict{UInt,Symbol}())
    t = type(ex)
    if t == :Symbol
        h = hash(ex)
        if haskey(var_dict, h)
            return var_dict[h]
        else
            s = Symbol(SE.toString(ex))
            var_dict[h] = s
            return s
        end
    elseif t == :Integer
        x = convert(BigInt, SE.BasicType{Val{:Integer}}(ex))
        if typemin(Int32) ≤ x ≤ typemax(Int32)
            return :(Int32($x))
        else
            return x
        end
    elseif t == :RealDouble
        return convert(Cdouble, SE.BasicType{Val{:RealDouble}}(ex))
    elseif t == :Pow
        vec = UnsafeVecBasicIterator(args(ex))
        if type(vec[1]) == :Symbol
            h = hash(ex)
            if haskey(var_dict, h)
                x = var_dict[h]
            else
                var_dict[h] = x = Symbol(SE.toString(ex))
            end
        else
            x = to_expr(vec[1], var_dict)
        end
        k = convert(Int, vec[2])
        return :(unroll_pow($x, Val($k)))
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
