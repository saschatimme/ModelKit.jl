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
include("symbolic.jl")
include("codegen.jl")

end # module
