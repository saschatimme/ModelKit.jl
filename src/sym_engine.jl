
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
const SE = SymEngine
const Variable = SE.BasicType{Val{:Symbol}}
const Expression = SE.Basic

# Fixes in SymEngine
Base.promote_rule(::Type{Variable}, ::Type{Expression}) = Expression
Base.promote_rule(::Type{Expression}, ::Type{Variable}) = Expression

Base.hash(x::Variable, h::UInt) = hash(Expression(x), h)
Base.hash(x::Expression, h::UInt) = Base.hash_uint(3h - hash(x))

function Base.copy(x::SE.Basic)
    y = SE.Basic()
    ccall((:basic_assign, SE.libsymengine), Nothing, (Ref{SE.Basic}, Ref{SE.Basic}), y, x)
    y
end

const TYPE_IDS = let
    x = SE.symbols("x")
    types = [
        (x, :Symbol),
        (Expression(1), :Integer),
        (Expression(5 + 3im), :Complex),
        (Expression(0.5), :RealDouble),
        (Expression(0.5 + 0.2im), :ComplexDouble),
        (2x, :Mul),
        (x + 2, :Add),
        (x^2, :Pow),
    ]
    Dict(map(types) do (v, class)
        SE.get_type(v) => class
    end)
end

function type(e::Expression)
    id = SE.get_type(e)
    if haskey(TYPE_IDS, id)
        TYPE_IDS[id]
    else
        # add for futurue fast lookup
        cls = SE.get_class_from_id(id)
        TYPE_IDS[id] = cls
        cls
    end
end

function Base.convert(::Type{Int}, n::SE.Basic)
    ccall((:integer_get_si, SE.libsymengine), Int, (Ref{SE.Basic},), n)
end
function Base.convert(::Type{Int}, n::SE.BasicType{Val{:Integer}})
    ccall((:integer_get_si, SE.libsymengine), Int, (Ref{SE.Basic},), n)
end

mutable struct VecBasic
    ptr::Ptr{Cvoid}
end

function VecBasic()
    z = VecBasic(ccall((:vecbasic_new, SE.libsymengine), Ptr{Cvoid}, ()))
    finalizer(VecBasic_free, z)
    z
end
function VecBasic_free(x::VecBasic)
    if x.ptr != C_NULL
        ccall((:vecbasic_free, SE.libsymengine), Nothing, (Ptr{Cvoid},), x.ptr)
        x.ptr = C_NULL
    end
end

args(ex::SE.Basic) = args!(VecBasic(), ex)
function args!(vec::VecBasic, ex::SE.Basic)
    ccall(
        (:basic_get_args, SE.libsymengine),
        Nothing,
        (Ref{SE.Basic}, Ptr{Cvoid}),
        ex,
        vec.ptr,
    )
    vec
end

function getindex!(result::SE.Basic, s::VecBasic, n)
    ccall(
        (:vecbasic_get, SE.libsymengine),
        Nothing,
        (Ptr{Cvoid}, UInt, Ref{SE.Basic}),
        s.ptr,
        UInt(n - 1),
        result,
    )
    result
end

@inline function unsafe_getindex(s::VecBasic, n)
    res = Ref(Ptr{Cvoid}(C_NULL))
    ccall(
        (:vecbasic_get, SE.libsymengine),
        Nothing,
        (Ptr{Cvoid}, UInt, Ref{Ptr{Cvoid}}),
        s.ptr,
        UInt(n - 1),
        res,
    )
    SE.Basic(res[])
end
@inline Base.getindex(s::VecBasic, n) = unsafe_getindex(s, n)

@inline function Base.length(s::VecBasic)
    ccall((:vecbasic_size, SE.libsymengine), UInt, (Ptr{Cvoid},), s.ptr)
end
@inline function Base.iterate(s::VecBasic, (i, n) = (1, 0))
    if n == 0
        n = length(s)
    end
    i > n && return nothing
    s[i], (i + 1, n)
end
Base.eltype(::Type{VecBasic}) = SE.Basic


struct UnsafeVecBasicIterator
    v::VecBasic
    x::SE.Basic
end
UnsafeVecBasicIterator(v::VecBasic) = UnsafeVecBasicIterator(v, v[1])
@inline Base.length(s::UnsafeVecBasicIterator) = length(s.v)
@inline function Base.iterate(s::UnsafeVecBasicIterator, i = 1)
    i > length(s.v) && return nothing
    getindex!(s.x, s.v, i), i + 1
end
Base.eltype(::Type{UnsafeVecBasicIterator}) = SE.Basic
