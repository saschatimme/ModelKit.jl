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
    Homotopy,
    evaluate!,
    jacobian!,
    evaluate_and_jacobian!,
    diff_t!,
    evaluate,
    jacobian,
    evaluate_and_jacobian,
    diff_t

import LinearAlgebra

include("symengine.jl")
include("symbolic.jl")
include("instructions.jl")
include("codegen.jl")

end # module
