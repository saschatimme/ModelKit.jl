
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

function Base.getindex(s::VecBasic, n)
    result = SE.Basic()
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
    res = Ref(Ptr{Cvoid}())
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

function Base.length(s::VecBasic)
    ccall((:vecbasic_size, SE.libsymengine), UInt, (Ptr{Cvoid},), s.ptr)
end
function Base.iterate(s::VecBasic, i = 1)
    i > length(s) && return nothing
    s[i], i + 1
end
Base.eltype(::Type{VecBasic}) = SE.Basic


struct UnsafeVecBasicIterator
    v::VecBasic
    x::SE.Basic
end
UnsafeVecBasicIterator(v::VecBasic) = UnsafeVecBasicIterator(v, v[1])
Base.length(s::UnsafeVecBasicIterator) = length(s.v)
function Base.iterate(s::UnsafeVecBasicIterator, i = 1)
    i > length(s.v) && return nothing
    getindex!(s.x, s.v, i), i + 1
end
Base.eltype(::Type{UnsafeVecBasicIterator}) = SE.Basic




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
                    x = getindex!(b2, vec, 1)
                    # x = unsafe_getindex(vec, 1)
                    for (i, v) in enumerate(vars)
                        if x == v
                            D[i, j] = convert(Int, getindex!(b2, vec, 2))
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
            x = getindex!(b2, vec, 1)
            for (i, v) in enumerate(vars)
                if x == v
                    D[i, j] = convert(Int, getindex!(b2, vec, 2))
                    break
                end
            end
        end
    end
    D
end
degrees(expr::SE.BasicType, vars::Vector{Variable}) =
    zeros(Int32, length(vars), 0)

degree(expr::Variable, var::Variable) = Int(expr == var)
@inline function degree(expr::SE.Basic, var)
    if ModelKit.type(expr) == :Mul
        sum(e -> degree(e, var), UnsafeVecBasicIterator(args(expr)))
    elseif ModelKit.type(expr) == :Pow
        expr_args = args(expr)
        expr_args[1] == var ? convert(Int, expr_args[2]) : 0
    elseif ModelKit.type(expr) == :Symbol
        Int(expr == var)
    else
        0
    end
end
