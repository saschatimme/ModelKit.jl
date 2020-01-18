module ModelKit

export @var,
    @unique_var,
    Variable,
    Expression,
    variables,
    nvariables,
    subs,
    evaluate,
    differentiate,
    monomials,
    expand,
    System,
    Homotopy

import LinearAlgebra, GeneralizedGenerated, SymEngine

include("sym_engine.jl")


## Variable construction

function Variable(name::Union{Symbol,AbstractString})
    SE.BasicType(SE.symbols(name))
end

Variable(name::Union{Symbol,AbstractString}, indices...) =
    Variable("$(name)$(join(map_subscripts.(indices), "₋"))")

const INDEX_MAP = Dict{Char,Char}(
    '0' => '₀',
    '1' => '₁',
    '2' => '₂',
    '3' => '₃',
    '4' => '₄',
    '5' => '₅',
    '6' => '₆',
    '7' => '₇',
    '8' => '₈',
    '9' => '₉',
)
map_subscripts(indices) = join(INDEX_MAP[c] for c in string(indices))

Base.convert(::Type{Variable}, v::Union{AbstractString, Symbol}) = Variable(v)
Base.convert(::Type{Expr}, v::Variable) = Symbol(v)
Symbol(v::Variable) = Symbol(SE.toString(v))
# type piracy here
Base.show(io::IO, v::Type{Variable}) = print(io, "Variable")
Base.show(io::IO, v::Type{Expression}) = print(io, "Expression")


"""
    @var(args...)

Declare variables with the given and automatically create the variable bindings.

## Examples

```julia
julia> @var a b x[1:2] y[1:2,1:3]
(a, b, Variable[x₁, x₂], Variable[y₁₋₁ y₁₋₂ y₁₋₃; y₂₋₁ y₂₋₂ y₂₋₃])

julia> a
a

julia> b
b

julia> x
2-element Array{Variable,1}:
 x₁
 x₂

julia> y
2×3 Array{Variable,2}:
 y₁₋₁  y₁₋₂  y₁₋₃
 y₂₋₁  y₂₋₂  y₂₋₃
```
"""
macro var(args...)
    vars, exprs = buildvars(args; unique = false)
    :($(foldl((x, y) -> :($x; $y), exprs, init = :()));
    $(Expr(:tuple, esc.(vars)...)))
end

"""
    @unique_var(args...)

Declare variables and automatically create the variable bindings to the given names.
This will change the names of the variables to ensure uniqueness.

## Examples

```julia
julia> @unique_var a b
(##a#591, ##b#592)

julia> a
##a#591

julia> b
##b#592
```
"""
macro unique_var(args...)
    vars, exprs = buildvars(args; unique = true)
    :($(foldl((x, y) -> :($x; $y), exprs, init = :()));
    $(Expr(:tuple, esc.(vars)...)))
end

function var_array(prefix, indices...)
    map(i -> Variable(prefix, i...), Iterators.product(indices...))
end

function buildvar(var; unique::Bool = false)
    if isa(var, Symbol)
        varname = unique ? gensym(var) : var
        var, :($(esc(var)) = Variable($"$varname"))
    else
        isa(var, Expr) || error("Expected $var to be a variable name")
        Base.Meta.isexpr(var, :ref) ||
        error("Expected $var to be of the form varname[idxset]")
        (2 ≤ length(var.args)) ||
        error("Expected $var to have at least one index set")
        varname = var.args[1]
        prefix = unique ? string(gensym(varname)) : string(varname)
        varname,
        :($(esc(varname)) = var_array($prefix, $(esc.(var.args[2:end])...)))
    end
end

function buildvars(args; unique::Bool = false)
    vars = Symbol[]
    exprs = []
    for arg in args
        if arg isa Expr && arg.head == :tuple
            for _arg in arg.args
                var, expr = buildvar(_arg; unique = unique)
                push!(vars, var)
                push!(exprs, expr)
            end
        else
            var, expr = buildvar(arg; unique = unique)
            push!(vars, var)
            push!(exprs, expr)
        end
    end
    vars, exprs
end

Base.adjoint(expr::Expression) = expr
Base.conj(expr::Expression) = expr
Base.transpose(expr::Expression) = expr
Base.broadcastable(v::Expression) = Ref(v)

Base.isless(a::Variable, b::Variable) =
    isless(SE.toString(a), SE.toString(b))

"""
    variables(expr::Expression, parameters = Variable[])
    variables(exprs::AbstractVector{<:Expression}, parameters = Variable[])

Obtain all variables used in the given expression.
"""
variables(op::Expression, params = Variable[]) = variables([op], params)
function variables(exprs::AbstractVector{<:Expression}, params = Variable[])
    S = Set{Variable}()
    for expr in exprs, v in SE.free_symbols(expr)
        push!(S, SE.BasicType(v))
    end
    setdiff!(S, params)
    sort!(collect(S))
end
variables(exprs, params = Variable[]) = Variable[]

"""
    nvariables(expr::Expression, parameters = Variable[])
    nvariables(exprs::AbstractVector{<:Expression}, parameters = Variable[])

Obtain the number of variables used in the given expression.
"""
nvariables(E::Union{Expression,AbstractVector{<:Expression}}, p = Variable[]) =
    length(variables(E, p))


"""
    subs(expr::Expression, subs::Pair{Variable,<:Expression}...)
    subs(expr::Expression, subs::Pair{AbstractArray{<:Variable},AbstractArray{<:Expression}}...)

Substitute into the given expression.

## Example

```
@var x y z

julia> subs(x^2, x => y)
y ^ 2

julia> subs(x * y, [x,y] => [x+2,y+2])
(x + 2) * (y + 2)
```
"""
subs(exprs, args...) = map(e -> subs(e, args...), exprs)
function subs(
    expr::Expression,
    sub_pairs::Union{
        Pair{Variable,<:Number},
        Pair{<:AbstractArray{Variable},<:AbstractArray{<:Number}},
    }...,
)
    new_expr = expr
    for sub in sub_pairs
        new_expr = _subs(new_expr, sub)
    end
    new_expr
end
function _subs(expr::Expression, args...)
    SE.subs(expr, args...)
end
function _subs(
    expr::Expression,
    sub_pairs::Pair{<:AbstractArray{Variable},<:AbstractArray{<:Number}},
)
    length(first(sub_pairs)) == length(last(sub_pairs)) ||
    error(ArgumentError("Substitution arguments don't have the same length."))

    list_of_tuples = map(tuple, first(sub_pairs), last(sub_pairs))
    SE.subs(expr, list_of_tuples...)
end

# trait
is_number_type(::Expression) = Val{false}()
for T in SE.number_types
    @eval begin
        is_number_type(::SE.BasicType{Val{$(QuoteNode(T))}}) =
            Val{true}()
    end
end

unpack_number(e::Expression) = unpack_number(e, is_number_type(e))
unpack_number(e::Expression, ::Val{true}) = SE.N(e)
unpack_number(e::Expression, ::Val{false}) = e

"""
    evaluate(expr::Expression, subs::Pair{Variable,<:Any}...)
    evaluate(expr::Expression, subs::Pair{AbstractArray{<:Variable},AbstractArray{<:Any}}...)

Evaluate the given expression.

## Example

```
@var x y

julia> evaluate(x^2, x => 2)
4

julia> evaluate(x * y, [x,y] => [2, 3])
6
"""
function evaluate(
    expr::Union{Expression,AbstractArray{<:Expression}},
    pairs::Union{
        Pair{Variable,<:Number},
        Pair{<:AbstractArray{Variable},<:AbstractArray{<:Number}},
    }...,
)
    unpack_number.(subs(expr, pairs...))
end
(f::Expression)(
    pairs::Union{
        Pair{Variable,<:Number},
        Pair{<:AbstractArray{Variable},<:AbstractArray{<:Number}},
    }...,
) = evaluate(f, pairs...)


function LinearAlgebra.det(A::Matrix{<:Expression})
    LinearAlgebra.det(convert(SE.CDenseMatrix, A))
end
function LinearAlgebra.lu(A::Matrix{<:Expression})
    LinearAlgebra.lu(convert(SE.CDenseMatrix, A))
end


"""
    differentiate(expr::Expression, var::Variable, k = 1)
    differentiate(expr::Expression, var::Vector{Variable})
    differentiate(expr::::Vector{<:Expression}, var::Variable, k = 1)
    differentiate(expr::Vector{<:Expression}, var::Vector{Variable})

Compute the derivative of `expr` with respect to the given variable `var`.
"""
differentiate(expr::Expression, var::Variable) = SE.diff(expr, var)
differentiate(expr::Expression, var::Variable, k) = SE.diff(expr, var, k)
function differentiate(expr::Expression, vars::AbstractVector{Variable})
    [SE.diff(expr, v) for v in vars]
end

function differentiate(exprs::AbstractVector{<:Expression}, var::Variable)
    [differentiate(e, var) for e in exprs]
end
function differentiate(exprs::AbstractVector{<:Expression}, var::Variable, k)
    [differentiate(e, var, k) for e in exprs]
end
function differentiate(
    exprs::AbstractVector{<:Expression},
    vars::AbstractVector{Variable},
)
    [differentiate(e, v) for e in exprs, v in vars]
end

"""
    monomials(vars::Vector{<:Variable}, d; homogeneous::Bool = false)

Create all monomials of a given degree.

```
julia> @var x y
(x, y)

julia> monomials([x,y], 2)
6-element Array{Expression,1}:
   1
   x
   y
 x^2
 x*y
 y^2

julia> monomials([x,y], 2; homogeneous = true)
3-element Array{Operation,1}:
 x ^ 2
 x * y
 y ^ 2
 ```
"""
function monomials(
    vars::AbstractVector{Variable},
    d::Integer;
    homogeneous::Bool = false,
)
    n = length(vars)
    if homogeneous
        pred = x -> sum(x) == d
    else
        pred = x -> sum(x) ≤ d
    end
    exps = collect(Iterators.filter(
        pred,
        Iterators.product(Iterators.repeated(0:d, n)...),
    ))
    sort!(exps, lt = td_order)
    map(exps) do exp
        prod(i -> vars[i]^exp[i], 1:n)
    end
end

function td_order(x, y)
    sx = sum(x)
    sy = sum(y)
    sx == sy ? x > y : sx < sy
end

"""
    expand(e::Expression)

Expand a given expression.

```julia
julia> @var x y
(x, y)

julia> f = (x + y) ^ 2
(x + y)^2

julia> expand(f)
2*x*y + x^2 + y^2
```
"""
expand(e::Expression) = SE.expand(e)


degrees(expr::SE.Basic, vars::Vector{Variable}) =
    degrees(SE.BasicType(expr), vars)
function degrees(expr::SE.BasicType{Val{:Add}}, vars::Vector{Variable})
    ops = UnsafeVecBasicIterator(args(SE.Basic(expr)))
    D = zeros(Int32, length(vars), length(ops))

    b1, b2 = SE.Basic(), SE.Basic()
    mul_args, pow_args = VecBasic(), VecBasic()

    for (j, op) in enumerate(ops)
        op_cls = ModelKit.type(op)
        if op_cls == :Mul
            op_args = UnsafeVecBasicIterator(args!(mul_args, op), b1)
            for arg in op_args
                arg_cls = ModelKit.type(arg)
                if arg_cls == :Symbol
                    for (i, v) in enumerate(vars)
                        if v == arg
                            D[i, j] = 1
                            break
                        end
                    end
                elseif arg_cls == :Pow
                    vec = args!(pow_args, arg)
                    x = vec[1]
                    for (i, v) in enumerate(vars)
                        if x == v
                            D[i, j] = convert(Int, vec[2])
                            break
                        end
                    end
                end
            end
        elseif op_cls == :Symbol
            for (i, v) in enumerate(vars)
                if v == op
                    D[i, j] = 1
                    break
                end
            end
        elseif op_cls == :Pow
            vec = args!(pow_args, op)
            x = vec[1]
            for (i, v) in enumerate(vars)
                if x == v
                    D[i, j] = convert(Int, vec[2])
                    break
                end
            end
        end
    end
    D
end
degrees(expr::SE.BasicType, vars::Vector{Variable}) =
    zeros(Int32, length(vars), 0)


to_dict(expr::SE.Basic, vars::Vector{Variable}) =
    to_dict(SE.BasicType(expr), vars)
function to_dict(expr::SE.BasicType{Val{:Add}}, vars::Vector{Variable})
    ops = UnsafeVecBasicIterator(args(SE.Basic(expr)))
    D = zeros(Int32, length(vars), length(ops))

    b1, b2 = SE.Basic(), SE.Basic()
    mul_args, pow_args = VecBasic(), VecBasic()

    dict = Dict{Vector{Int},Expression}()

    for op in ops
        cls = ModelKit.type(op)
        d = zeros(Int, length(vars))
        coeff = Expression(1)
        if cls == :Mul
            op_args = UnsafeVecBasicIterator(args!(mul_args, op), b1)
            for arg in op_args
                arg_cls = ModelKit.type(arg)
                is_coeff = true
                if arg_cls == :Symbol
                    for (i, v) in enumerate(vars)
                        if v == arg
                            d[i] = 1
                            is_coeff = false
                            break
                        end
                    end
                elseif arg_cls == :Pow
                    vec = args!(pow_args, arg)
                    x = vec[1]
                    for (i, v) in enumerate(vars)
                        if x == v
                            d[i] = convert(Int, vec[2])
                            is_coeff = false
                            break
                        end
                    end
                end
                if is_coeff
                   coeff = coeff * arg
                end
            end
        elseif cls == :Symbol
            for (i, v) in enumerate(vars)
                if v == arg
                    d[i] = 1
                    break
                end
            end
        elseif cls == :Pow
            vec = args!(pow_args, arg)
            x = vec[1]
            for (i, v) in enumerate(vars)
                if x == v
                    d[i] = convert(Int, vec[2])
                    break
                end
            end
        elseif cls ∈ SE.number_types
            coeff = copy(op)
        end
        if haskey(dict, d)
            dict[d] += coeff
        else
            dict[d] = coeff
        end
    end
    dict
end
#
# degrees(expr::SE.BasicType, vars::Vector{Variable}) =
#     zeros(Int32, length(vars), 0)


#########################
## System and Homotopy ##
#########################


############
## System ##
############

function check_vars_params(f, vars, params)
    vars_params = params === nothing ? vars : [vars; params]
    Δ = setdiff(variables(f), vars_params)
    isempty(Δ) || throw(ArgumentError(
        "Not all variables or parameters of the system are given. Missing: " *
        join(Δ, ", "),
    ))
    nothing
end

"""
    System(exprs, vars, parameters = Variable[])

Create a system from the given `exprs`. `vars` are the given variables and determines
the variable ordering.

## Example
```julia
julia> @var x y;
julia> H = System([x^2, y^2], [y, x]);
julia> H([2, 3], 0)
2-element Array{Int64,1}:
 4
 9
```

It is also possible to declare additional variables.
```julia
julia> @var x y t a b;
julia> H = Homotopy([x^2 + a, y^2 + b^2], [x, y], [a, b]);
julia> H([2, 3], [5, 2])
2-element Array{Int64,1}:
 9
 13
```
"""
struct System
    expressions::Vector{Expression}
    variables::Vector{Variable}
    parameters::Vector{Variable}
    # automatically computed
    jacobian::Matrix{Expression}

    function System(
        exprs::Vector{Expression},
        vars::Vector{Variable},
        params::Vector{Variable},
    )
        check_vars_params(exprs, vars, params)
        jacobian = [differentiate(e, v) for e in exprs, v in vars]
        new(exprs, vars, params, jacobian)
    end
end

function System(
    exprs::Vector{<:Expression},
    variables::Vector{Variable},
    parameters::Vector{Variable} = Variable[],
)
    System(convert(Vector{Expression}, exprs), variables, parameters)
end

function Base.show(io::IO, F::System)
    if !get(io, :compact, false)
        println(io, "System")
        print(io, " variables: ", join(F.variables, ", "))
        if !isempty(F.parameters)
            print(io, "\n parameters: ", join(F.parameters, ", "))
        end
        print(io, "\n\n")
        for i = 1:length(F)
            print(io, " ", F.expressions[i])
            i < length(F) && print(io, "\n")
        end
    else
        print(io, "[")
        for i = 1:length(F)
            print(io, F.expressions[i])
            i < length(F) && print(io, ", ")
        end
        print(io, "]")
    end
end

evaluate(F::System, x::AbstractVector) =
    evaluate(F.expressions, F.variables => x)
function evaluate(F::System, x::AbstractVector, p::AbstractVector)
    evaluate(F.expressions, F.variables => x, F.parameters => p)
end
(F::System)(x::AbstractVector) = evaluate(F, x)
(F::System)(x::AbstractVector, p::AbstractVector) = evaluate(F, x, p)

jacobian(F::System, x::AbstractVector) = evaluate(F.jacobian, F.variables => x)
function jacobian(F::System, x::AbstractVector, p::AbstractVector)
    evaluate(F.jacobian, F.variables => x, F.parameters => p)
end


function Base.:(==)(F::System, G::System)
    F.expressions == G.expressions &&
    F.variables == G.variables && F.parameters == G.parameters
end

Base.size(F::System) = (length(F.expressions), length(F.variables))
Base.size(F::System, i::Integer) = size(F)[i]
Base.length(F::System) = length(F.expressions)

variables(F::System, parameters = nothing) = variables(F.variables)

Base.iterate(F::System) = iterate(F.expressions)
Base.iterate(F::System, state) = iterate(F.expressions, state)

##############
## Homotopy ##
##############
"""
    Homotopy(exprs, vars, t, parameters = Variable[])

Create a homotopy from the given `exprs`. `vars` are the given variables and determines
the variable ordering, `t` is the dedicated variable along which is "homotopied".

## Example
```julia
julia> @var x y t;
julia> H = Homotopy([x + t, y + 2t], [y, x], t);
julia> H([2, 3], 0)
2-element Array{Int64,1}:
 3
 2


julia> H([2, 3], 1)
2-element Array{Int64,1}:
 4
 4
```

It is also possible to declare additional variables.
```julia
julia> @var x y t a b;
julia> H = Homotopy([x^2 + t*a, y^2 + t*b], [x, y], t, [a, b]);
julia> H([2, 3], 1, [5, 2])
2-element Array{Int64,1}:
 9
 11
```
"""
struct Homotopy
    expressions::Vector{Expression}
    variables::Vector{Variable}
    t::Variable
    parameters::Vector{Variable}
    # automatically computed
    jacobian::Matrix{Expression}
    dt::Vector{Expression}

    function Homotopy(
        exprs::Vector{Expression},
        vars::Vector{Variable},
        t::Variable,
        params::Vector{Variable},
    )
        check_vars_params(exprs, [vars; t], params)
        jacobian = [differentiate(e, v) for e in exprs, v in vars]
        dt = [differentiate(e, t) for e in exprs]
        new(exprs, vars, t, params, jacobian, dt)
    end
end

function Homotopy(
    exprs::Vector{<:Expression},
    variables::Vector{Variable},
    t::Variable,
    parameters::Vector{Variable} = Variable[],
)
    Homotopy(convert(Vector{Expression}, exprs), variables, t, parameters)
end

function Base.show(io::IO, H::Homotopy)
    if !get(io, :compact, false)
        println(io, "Homotopy in ", H.t)
        print(io, " variables: ", join(H.variables, ", "))
        if !isempty(H.parameters)
            print(io, "\n parameters: ", join(H.parameters, ", "))
        end
        print(io, "\n\n")
        for i = 1:length(H)
            print(io, " ", H.expressions[i])
            i < length(H) && print(io, "\n")
        end
    else
        print(io, "[")
        for i = 1:length(H)
            print(io, H.expressions[i])
            i < length(H) && print(io, ", ")
        end
        print(io, "]")
    end
end

evaluate(H::Homotopy, x::AbstractVector, t) =
    evaluate(H.expressions, H.variables => x, H.t => t)
function evaluate(H::Homotopy, x::AbstractVector, t, p::AbstractVector)
    evaluate(H.expressions, H.variables => x, H.t => t, H.parameters => p)
end
(H::Homotopy)(x::AbstractVector, t) = evaluate(H, x, t)
(H::Homotopy)(x::AbstractVector, t, p::AbstractVector) = evaluate(H, x, t, p)

function jacobian(H::Homotopy, x::AbstractVector, t)
    evaluate(H.jacobian, H.variables => x, H.t => t)
end
function jacobian(H::Homotopy, x::AbstractVector, t, p::AbstractVector)
    evaluate(H.jacobian, H.variables => x, H.t => t, H.parameters => p)
end

function dt(H::Homotopy, x::AbstractVector, t)
    evaluate(H.dt, H.variables => x, H.t => t)
end
function dt(H::Homotopy, x::AbstractVector, t, p::AbstractVector)
    evaluate(H.dt, H.variables => x, H.t => t, H.parameters => p)
end

function Base.:(==)(H::Homotopy, G::Homotopy)
    H.expressions == G.expressions &&
    H.variables == G.variables && H.parameters == G.parameters
end

Base.size(H::Homotopy) = (length(H.expressions), length(H.variables))
Base.size(H::Homotopy, i::Integer) = size(H)[i]
Base.length(H::Homotopy) = length(H.expressions)

#############
## CODEGEN ##
#############

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

end # module
