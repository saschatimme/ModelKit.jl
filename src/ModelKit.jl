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
using OrderedCollections: OrderedDict

include("sym_engine.jl")
include("symbolic.jl")
include("instructions.jl")
include("codegen.jl")

end # module
