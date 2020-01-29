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

Base.size(TS::TSystem) = size(interpret(TS))


const THOMOTOPY_TABLE = Dict{
    UInt,
    Vector{
        Tuple{Vector{Expression},Vector{Variable},Variable,Vector{Variable}},
    },
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
interpret(::Type{THomotopy{H,I}}) where {H,I} =
    Homotopy(THOMOTOPY_TABLE[H][I]...)

Base.size(TH::THomotopy) = size(interpret(TH))

type_level(sys::System) =
    TSystem(sys.expressions, sys.variables, sys.parameters)
type_level(sys::Homotopy) =
    THomotopy(sys.expressions, sys.variables, sys.t, sys.parameters)

function to_smallest_type(A::AbstractArray)
    T = typeof(first(A))
    for a in A
        T = promote_type(T, typeof(a))
    end
    convert.(T, A)
end

boundscheck_var_map(F::System; kwargs...) =
    boundscheck_var_map(F.expressions, F.variables, F.parameters; kwargs...)
boundscheck_var_map(H::Homotopy; kwargs...) =
    boundscheck_var_map(H.expressions, H.variables, H.parameters, H.t; kwargs...)

function boundscheck_var_map(
    exprs,
    vars,
    params,
    t = nothing;
    jacobian::Bool = false,
)
    n = length(exprs)
    m = length(vars)
    l = length(params)
    var_map = Dict{Symbol,Union{Symbol,Expr}}()
    for i = 1:m
        var_map[Symbol(vars[i])] = :(x[$i])
    end
    for i = 1:l
        var_map[Symbol(params[i])] = :(p[$i])
    end
    if t !== nothing
        var_map[Symbol(t)] = :(t)
    end

    checks = Expr[]
    if jacobian
        push!(checks, :(@boundscheck checkbounds(U, 1:$n, 1:$m)))
    end
    push!(checks, :(@boundscheck checkbounds(x, 1:$m)))
    push!(checks, :(@boundscheck p === nothing || checkbounds(p, 1:$l)))

    Expr(:block, checks...), var_map
end

function codegen(
    exprs::Vector{Expression},
    var_map;
    output_name::Symbol = gensym(:u),
)
    list, ids = instruction_list(exprs)
    assignements = Dict{Symbol,Expr}()
    for (i, id) in enumerate(ids)
        push!(assignements, id => :($(output_name)[$i] = $id))
    end
    to_expr(list, var_map, assignements)
end

function _evaluate!_impl(::Type{T}) where {T<:Union{TSystem,THomotopy}}
    I = interpret(T)
    checks, var_map = boundscheck_var_map(I)
    slp = let
        list, ids = instruction_list(I.expressions)
        assignements = Dict{Symbol,Expr}()
        for (i, id) in enumerate(ids)
            push!(assignements, id => :(u[$i] = $id))
        end
        to_expr(list, var_map, assignements)
    end

    quote
        $checks
        @inbounds $slp
        u
    end
end

@generated function evaluate!(u, ::T, x, p = nothing) where {T<:TSystem}
    _evaluate!_impl(T)
end
@generated function evaluate!(u, ::T, x, t, p = nothing) where {T<:THomotopy}
    _evaluate!_impl(T)
end

function evaluate(T::TSystem, x, p = nothing)
    to_smallest_type(evaluate!(Vector{Any}(undef, size(T,1)), T, x, p))
end

function _jacobian!_impl(::Type{T}) where {T<:Union{TSystem,THomotopy}}
    I = interpret(T)
    checks, var_map = boundscheck_var_map(I; jacobian = true)

    slp = let
        list, ids = instruction_list(I.expressions)
        vars = Symbol.(I.variables)
        dlist, J = diff(list, vars, ids)

        assignements = Dict{Symbol,Expr}()

        U_constants = Expr[]
        for j = 1:size(J, 2), i = 1:size(J, 1)
            if J[i, j] isa Symbol
                push!(assignements, J[i, j] => :(U[$i, $j] = $(J[i, j])))
            elseif J[i,j] isa Number
                push!(U_constants, :(U[$i, $j] = $(J[i, j])))
            end
        end
        expr = to_expr(dlist, var_map, assignements)
        append!(expr.args, U_constants)
        expr
    end
    quote
        $checks
        U .= zero(eltype(x))
        @inbounds $slp
        U
    end
end
@generated function jacobian!(U, ::T, x, p = nothing) where {T<:TSystem}
    _jacobian!_impl(T)
end
@generated function jacobian!(U, ::T, x, t, p = nothing) where {T<:THomotopy}
    _jacobian!_impl(T)
end

function jacobian(T::TSystem, x, p = nothing)
    n, m = size(T)
    U = Matrix{Any}(undef, n, m)
    to_smallest_type(jacobian!(U, T, x, p))
end
function jacobian(T::THomotopy, x, t, p = nothing)
    n, m = size(T)
    U = Vector{Any}(undef, n, m)
    to_smallest_type(jacobian!(U, T, x, t, p))
end


function _evaluate_and_jacobian!_impl(::Type{T}) where {T<:Union{TSystem,THomotopy}}
    I = interpret(T)
    checks, var_map = boundscheck_var_map(I; jacobian = true)

    slp = let
        list, ids = instruction_list(I.expressions)
        vars = Symbol.(I.variables)
        dlist, J = diff(list, vars, ids)

        assignements = Dict{Symbol,Expr}()
        for (i, id) in enumerate(ids)
            push!(assignements, id => :(u[$i] = $id))
        end

        U_constants = Expr[]
        for j = 1:size(J, 2), i = 1:size(J, 1)
            if J[i, j] isa Symbol
                push!(assignements, J[i, j] => :(U[$i, $j] = $(J[i, j])))
            elseif J[i,j] isa Number
                push!(U_constants, :(U[$i, $j] = $(J[i, j])))
            end
        end
        expr = to_expr(dlist, var_map, assignements)
        append!(expr.args, U_constants)
        expr
    end
    quote
        $checks
        U .= zero(eltype(x))
        @inbounds $slp
        nothing
    end
end

@generated function evaluate_and_jacobian!(u, U, ::T, x, p = nothing) where {T<:TSystem}
    _evaluate_and_jacobian!_impl(T)
end
@generated function evaluate_and_jacobian!(u, U, ::T, x, t, p = nothing) where {T<:THomotopy}
    _evaluate_and_jacobian!_impl(T)
end

function evaluate_jacobian(T::TSystem, x, p = nothing)
    n, m = size(T)
    u = Vector{Any}(undef, n)
    U = Matrix{Any}(undef, n, m)
    evaluate_and_jacobian!(u, U, T, x, p)
    to_smallest_type(u), to_smallest_type(U)
end
function evaluate_jacobian(T::THomotopy, x, t, p = nothing)
    n, m = size(T)
    u = Vector{Any}(undef, n)
    U = Matrix{Any}(undef, n, m)
    evaluate_and_jacobian!(u, U, T, x, t, p)
    to_smallest_type(u), to_smallest_type(U)
end
