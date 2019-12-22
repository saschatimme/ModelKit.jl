module ModelKit

export @var,
    @unique_var,
    Variable,
    variables,
    nvariables,
    subs,
    evaluate,
    differentiate,
    monomials,
    expand

import LinearAlgebra
import SymEngine


## From the SymEngine source code
##
## Basic: holds a ptr to a symengine object. Faster, so is default type
##
## BasicType{Val{:XXX}}: types that can be use to control dispatch
##
## SymbolicType: is a type union of the two
##
## Basic(x::BasicType) gives a basic object;
## BasicType(x::Basic) gives a BasicType object.
##

# some useful aliases
const Variable = SymEngine.BasicType{Val{:Symbol}}
const Expression = SymEngine.SymbolicType

Base.promote_rule(::Type{Variable}, ::Type{SymEngine.Basic}) = SymEngine.Basic
Base.promote_rule(::Type{SymEngine.Basic}, ::Type{Variable}) = SymEngine.Basic
## Variable construction

function Variable(name::Union{Symbol,AbstractString})
    SymEngine.BasicType(SymEngine.symbols(name))
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

# type piracy here
Base.show(io::IO, v::Type{Variable}) = print(io, "Variable")
Base.show(io::IO, v::Type{<:Expression}) = print(io, "Expression")

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
    isless(SymEngine.toString(a), SymEngine.toString(b))

"""
    variables(expr::Expression, parameters = Variable[])
    variables(exprs::AbstractVector{<:Expression}, parameters = Variable[])

Obtain all variables used in the given expression.
"""
variables(op::Expression, params = Variable[]) = variables([op], params)
function variables(exprs::AbstractVector{<:Expression}, params = Variable[])
    S = Set{Variable}()
    for expr in exprs, v in SymEngine.free_symbols(expr)
        push!(S, SymEngine.BasicType(v))
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
        Pair{Variable,<:Union{Number,Expression}},
        Pair{
            <:AbstractArray{Variable},
            <:AbstractArray{<:Union{Number,Expression}},
        },
    }...,
)
    new_expr = expr
    for sub in sub_pairs
        new_expr = _subs(new_expr, sub)
    end
    new_expr
end
function _subs(expr::Expression, args...)
    SymEngine.subs(expr, args...)
end
function _subs(
    expr::Expression,
    sub_pairs::Pair{
        <:AbstractArray{Variable},
        <:AbstractArray{<:Union{Number,Expression}},
    },
)
    length(first(sub_pairs)) == length(last(sub_pairs)) ||
    error(ArgumentError("Substitution arguments don't have the same length."))

    list_of_tuples = map(tuple, first(sub_pairs), last(sub_pairs))
    SymEngine.subs(expr, list_of_tuples...)
end

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
    SymEngine.N.(subs(expr, pairs...))
end


function LinearAlgebra.det(A::Matrix{<:Expression})
    LinearAlgebra.det(convert(SymEngine.CDenseMatrix, A))
end
function LinearAlgebra.lu(A::Matrix{<:Expression})
    LinearAlgebra.lu(convert(SymEngine.CDenseMatrix, A))
end


"""
    differentiate(expr::Expression, var::Variable, k = 1)
    differentiate(expr::Expression, var::Vector{Variable})
    differentiate(expr::::Vector{<:Expression}, var::Variable, k = 1)
    differentiate(expr::Vector{<:Expression}, var::Vector{Variable})

Compute the derivative of `expr` with respect to the given variable `var`.
"""
differentiate(expr::Expression, var::Variable) = SymEngine.diff(expr, var)
differentiate(expr::Expression, var::Variable, k) = SymEngine.diff(expr, var, k)
function differentiate(expr::Expression, vars::AbstractVector{Variable})
    [SymEngine.diff(expr, v) for v in vars]
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
expand(e::Expression) = SymEngine.expand(e)

end # module
