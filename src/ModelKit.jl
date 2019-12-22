module ModelKit

export @var, @unique_var, Variable, variables, nvariables


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



end # module