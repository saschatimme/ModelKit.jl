using SymEngine_jll: libsymengine


function __init__()
    __init_constants()
    __init_type_ids()
end

mutable struct Expression <: Number
    ptr::Ptr{Cvoid}

    function Expression()
        z = new(C_NULL)
        ccall((:basic_new_stack, libsymengine), Nothing, (Ref{Expression},), z)
        finalizer(free!, z)
        return z
    end

    function Expression(v::Ptr{Cvoid})
        z = new(v)
        return z
    end
end

Expression(T) = convert(Expression, T)

free!(b::Expression) =
    ccall((:basic_free_stack, libsymengine), Nothing, (Ref{Expression},), b)

struct ExpressionRef
    ptr::Ptr{Cvoid}
end
ExpressionRef() = ExpressionRef(Ptr{Cvoid}())

Base.convert(::Type{ExpressionRef}, e::Expression) = ExpressionRef(e.ptr)

function to_string(b::Union{Expression,ExpressionRef})
    if b.ptr == C_NULL
        return ""
    end
    if b isa Expression
        a = ccall(
            (:basic_str_julia, libsymengine),
            Cstring,
            (Ref{Expression},),
            b,
        )
    else
        a = ccall(
            (:basic_str_julia, libsymengine),
            Cstring,
            (Ref{ExpressionRef},),
            b,
        )
    end
    string = unsafe_string(a)
    ccall((:basic_str_free, libsymengine), Nothing, (Cstring,), a)
    return string
end

Base.show(io::IO, b::Union{Expression,ExpressionRef}) = print(io, to_string(b))
Base.hash(x::Expression, h::UInt) = Base.hash_uint(3h - hash(x))
function Base.copy(x::Union{Expression,ExpressionRef})
    y = Expression()
    ccall(
        (:basic_assign, libsymengine),
        Nothing,
        (Ref{Expression}, Ref{ExpressionRef}),
        y,
        x,
    )
    y
end

function Base.:(==)(b1::Expression, b2::Expression)
    ccall(
        (:basic_eq, libsymengine),
        Int,
        (Ref{Expression}, Ref{Expression}),
        b1,
        b2,
    ) == 1
end

Base.zero(::Expression) = zero(Expression)
Base.zero(::Type{Expression}) = Expression(0)
Base.one(::Expression) = one(Expression)
Base.one(::Type{Expression}) = Expression(1)

for op in [:im, :π, :ℯ, :γ, :catalan]
    @eval begin
        const $(Symbol("__", op)) = Expression(C_NULL)
    end
end

macro init_constant(op, libnm)
    tup = (Base.Symbol("basic_const_$libnm"), libsymengine)
    alloc_tup = (:basic_new_stack, libsymengine)
    op_name = Symbol("__", op)
    :(
        begin
            ccall($alloc_tup, Nothing, (Ref{Expression},), $op_name)
            ccall($tup, Nothing, (Ref{Expression},), $op_name)
            finalizer(free!, $op_name)
        end
    )
end

function __init_constants()
    @init_constant im I
    @init_constant π pi
    @init_constant ℯ E
    @init_constant γ EulerGamma
    @init_constant catalan Catalan
end

################
## arithmetic ##
################

Base.promote_rule(::Type{Expression}, ::Type{<:Number}) = Expression

## main ops
for (op, libnm) in
    [(:+, :add), (:-, :sub), (:*, :mul), (:/, :div), (://, :div), (:^, :pow)]

    f = Expr(:., :Base, QuoteNode(op))
    @eval begin
        function $f(b1::Expression, b2::Expression)
            a = Expression()
            ccall(
                $((Symbol("basic_", libnm), libsymengine)),
                Nothing,
                (Ref{Expression}, Ref{Expression}, Ref{Expression}),
                a,
                b1,
                b2,
            )
            return a
        end
    end
end

Base.:^(a::Expression, b::Integer) = a^Expression(b)
Base.:+(b::Expression) = b
Base.:-(b::Expression) = Expression(0) - b


# Functions
macro make_func(arg1, arg2)
    quote
        function $(esc(arg1))(b::Expression)
            a = Expression()
            ccall(($(QuoteNode(arg2)), libsymengine), Base.Nothing, (Base.Ref{Expression}, Base.Ref{Expression}), a, b)
            return a
        end
    end
end

@make_func expand basic_expand

##############################
## conversion to Expression ##
##############################

function Base.convert(::Type{Expression}, s::String)
    a = Expression()
    ccall(
        (:symbol_set, libsymengine),
        Nothing,
        (Ref{Expression}, Ptr{Int8}),
        a,
        s,
    )
    return a
end
Base.convert(::Type{Expression}, s::Symbol) = convert(Expression, s)

Base.convert(::Type{Expression}, x::Irrational{:γ}) = __γ
Base.convert(::Type{Expression}, x::Irrational{:π}) = __π
Base.convert(::Type{Expression}, x::Irrational{:ℯ}) = __ℯ
Base.convert(::Type{Expression}, x::Irrational{:catalan}) = __catalan


# basic number types
for (f, T) in [
    (:integer_set_si, Int),
    (:integer_set_ui, UInt),
    (:integer_set_mpz, BigInt),
    (:real_double_set_d, Float64),
]
    @eval begin
        function Base.convert(::Type{Expression}, x::$T)
            a = Expression()
            ccall(
                ($(QuoteNode(f)), libsymengine),
                Nothing,
                (Ref{Expression}, $T),
                a,
                x,
            )
            return a
        end
    end
end


Base.convert(::Type{Expression}, x::Union{Float16,Float32}) =
    convert(Expression, convert(Float64, x))
Base.convert(::Type{Expression}, x::AbstractFloat) =
    convert(Expression, convert(BigFloat, x))
function Base.convert(::Type{Expression}, x::BigFloat)
    if (x.prec <= 53)
        return convert(Expression, Float64(x))
    else
        a = Expression()
        ccall(
            (:real_mpfr_set, libsymengine),
            Nothing,
            (Ref{Expression}, Ref{BigFloat}),
            a,
            x,
        )
        return a
    end
end
Base.convert(::Type{Expression}, x::Int32) =
    convert(Expression, convert(Int, x))
Base.convert(::Type{Expression}, x::UInt32) =
    convert(Expression, convert(UInt, x))

Base.convert(::Type{Expression}, x::Integer) = Expression(BigInt(x))
Base.convert(::Type{Expression}, x::Rational) =
    Expression(numerator(x)) / Expression(denominator(x))
Base.convert(::Type{Expression}, x::Complex) =
    Expression(real(x)) + Expression(imag(x)) * __im

Base.complex(x::Expression, y::Expression) = x + y * __im
Base.complex(x::Expression, y::Real) = x + y * __im
Base.complex(x::Real, y::Expression) = x + y * __im



################################
## Iterating over expressions ##
################################


# Get class of an Expression

const REAL_NUMBER_TYPES = [:Integer, :RealDouble, :Rational, :RealMPFR]
const COMPLEX_NUMBER_TYPES = [:Complex, :ComplexDouble, :ComplexMPC]
const NUMBER_TYPES = [REAL_NUMBER_TYPES; COMPLEX_NUMBER_TYPES]

function type_id(s::Union{Expression,ExpressionRef})
    ccall((:basic_get_type, libsymengine), UInt, (Ref{Expression},), s)
end

function get_class_from_type_id(id::UInt)
    a = ccall((:basic_get_class_from_id, libsymengine), Ptr{UInt8}, (Int,), id)
    str = unsafe_string(a)
    ccall((:basic_str_free, libsymengine), Nothing, (Ptr{UInt8},), a)
    Symbol(str)
end

# prepopulate the dict
const TYPE_IDS = Dict{UInt,Symbol}()

function __init_type_ids()
    x = Expression("x")
    types = [
        (x, :Symbol),
        (Expression(1), :Integer),
        (Expression(0.5), :RealDouble),
        (Expression(2 // 3), :Rational),
        (Expression(big(0.5)), :RealMPFR),
        (Expression(5 + 3im), :Complex),
        (Expression(0.5 + 0.2im), :ComplexDouble),
        (Expression(0.5 + big(0.2) * im), :ComplexMPC),
        (2x, :Mul),
        (x + 2, :Add),
        (x^2, :Pow),
    ]
    for (v, class) in types
        TYPE_IDS[type_id(v)] = class
    end
    nothing
end

function class(e::Union{Expression,ExpressionRef})
    id = type_id(e)
    if haskey(TYPE_IDS, id)
        TYPE_IDS[id]
    else
        # add for futurue fast lookup
        cls = get_class_from_type_id(id)
        TYPE_IDS[id] = cls
        cls
    end
end


mutable struct ExprVec <: AbstractVector{Expression}
    ptr::Ptr{Cvoid}
    m::Ptr{ModelKit.ExpressionRef}

    function ExprVec()
        ptr = ccall((:vecbasic_new, libsymengine), Ptr{Cvoid}, ())
        m = Ptr{Ptr{ModelKit.ExpressionRef}}()
        z = new(ptr, m)
        finalizer(free!, z)
        z
    end
end
function vec_set_ptr!(v::ExprVec)
    v.m = unsafe_load(Ptr{Ptr{ModelKit.ExpressionRef}}(v.ptr))
    v
end

function free!(x::ExprVec)
    if x.ptr != C_NULL
        ccall((:vecbasic_free, libsymengine), Nothing, (Ptr{Cvoid},), x.ptr)
        x.ptr = C_NULL
    end
end

Base.length(s::ExprVec) =
    ccall((:vecbasic_size, libsymengine), UInt, (Ptr{Cvoid},), s.ptr)
Base.size(s::ExprVec) = (length(s),)

args(ex::Expression) = args!(ExprVec(), ex)
function args!(vec::ExprVec, ex::Expression)
    ccall(
        (:basic_get_args, libsymengine),
        Nothing,
        (Ref{Expression}, Ptr{Cvoid}),
        ex,
        vec.ptr,
    )
    vec_set_ptr!(vec)
end

function Base.getindex(v::ExprVec, n, ::Val{false})
    @boundscheck checkbounds(v, n)
    unsafe_load(v.m, n)
end
function Base.getindex(v::ExprVec, n, ::Val{true} = Val(true))
    @boundscheck checkbounds(v, n)
    copy(unsafe_load(v.m, n))
end


################################
## conversion from Expression ##
################################

function Base.convert(::Type{Int}, n::Expression)
    @assert class(n) == :Integer
    ccall((:integer_get_si, libsymengine), Int, (Ref{Expression},), n)
end
