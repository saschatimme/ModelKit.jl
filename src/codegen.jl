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

type_level(sys::System) =
    typeof(TSystem(sys.expressions, sys.variables, sys.parameters))
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
function show_info(
    io::IO,
    ::Type{TSystem{Tuple{n,N,m},TE,V,P}},
) where {n,N,m,TE,V,P}
    print(io, "TSystem{$n,$N,$m,#$(hash(TE))}")
end

interpret(TS::TSystem) = interpret(typeof(TS))
function interpret(::Type{TSystem{TS,TE,V,P}}) where {TS,TE,V,P}
    exprs = convert.(Expression, GeneralizedGenerated.from_type(TE))
    vars = Variable.(GeneralizedGenerated.from_type(V))
    params =
        convert(Vector{Variable}, collect(GeneralizedGenerated.from_type(P)))
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
    params =
        convert(Vector{Variable}, collect(GeneralizedGenerated.from_type(P)))

    Homotopy(exprs, vars, t, params)
end
