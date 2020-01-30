using ModelKit
using LinearAlgebra
using Test

@testset "ModelKit.jl" begin
    # Write your own tests here.

    @testset "Variables" begin
        @var a b x[1:2] y[1:2, 1:3]

        @test a isa Variable
        @test b isa Variable
        @test x isa Vector{Variable}
        @test length(x) == 2
        @test y isa Matrix{Variable}
        @test size(y) == (2, 3)

        @var c, d
        @test c isa Variable
        @test d isa Variable

        let
            c2 = @unique_var c
            @test c != c2
        end

        f = a + b
        @test variables(f) == [a, b]
        @test nvariables(f) == 2
        g = x[1]
        @test variables([f, g]) == [a, b, x[1]]
        @test nvariables([f, g]) == 3
    end

    @testset "Subs" begin
        @var x y w z u
        f = x^2 * (x + y * w)

        @test subs(f, x => z) == z^2 * (z + w * y)
        @test subs([f], x => z) == [z^2 * (z + w * y)]
        @test subs(f, [x, y] => [z^2, z + 2]) == z^4 * (w * (2 + z) + z^2)
        @test subs(f, [x, y] => [z^2, z + 2], w => u) ==
              z^4 * (u * (2 + z) + z^2)
    end

    @testset "Evaluation" begin
        @var x y w
        f = x^2 * (x + y * w)
        @test evaluate([f, f], [x, y, w] => [2, 3, -5]) == [-52, -52]
    end

    @testset "Linear Algebra" begin
        @var x[1:2, 1:2]
        @test_broken det(x) == -x[2, 1] * x[1, 2] + x[2, 2] * x[1, 1]
    end

    @testset "Differentation" begin
        @var x y

        f = x^2 + y^2
        g = x^3 + y^3

        @test differentiate(f, x) == 2x
        @test differentiate(f, x, 2) == 2
        @test differentiate(f, [x, y]) == [2x, 2y]

        @test differentiate([f, g], x) == [2x, 3 * x^2]
        @test differentiate([f, g], x, 2) == [2, 6x]
        @test differentiate([f, g], [x, y]) == [2x 2y; 3 * x^2 3 * y^2]
    end

    @testset "Expand" begin
        @var x y
        @test expand((x + y)^2) == 2 * x * y + x^2 + y^2
    end

    @testset "Modeling" begin
        @testset "Bottleneck" begin
            @var x y z
            f = [
                (0.3 * x^2 + 0.5z + 0.3x + 1.2 * y^2 - 1.1)^2 +
                (0.7 * (y - 0.5x)^2 + y + 1.2 * z^2 - 1)^2 - 0.3,
            ]

            I = let
                x = variables(f)
                n, m = length(x), length(f)
                @unique_var y[1:n] v[1:m] w[1:m]
                J = [differentiate(fᵢ, xᵢ) for fᵢ in f, xᵢ in x]
                f′ = [subs(fᵢ, x => y) for fᵢ in f]
                J′ = [subs(gᵢ, x => y) for gᵢ in J]
                Nx = (x - y) - J' * v
                Ny = (x - y) - J′' * w
                System([f; f′; Nx; Ny], [x; y; v; w])
            end
            @test I isa System
            @test size(I) == (8, 8)
        end

        @testset "Steiner" begin
            @var x[1:2] a[1:5] c[1:6] y[1:2, 1:5]

            #tangential conics
            f = sum([a; 1] .* monomials(x, 2))
            ∇ = differentiate(f, x)
            #5 conics
            g = sum(c .* monomials(x, 2))
            ∇_2 = differentiate(g, x)
            #the general system
            #f_a_0 is tangent to g_b₀ at x₀
            function Incidence(f, a₀, g, b₀, x₀)
                fᵢ = f(x => x₀, a => a₀)
                ∇ᵢ = [∇ᵢ(x => x₀, a => a₀) for ∇ᵢ in ∇]
                Cᵢ = g(x => x₀, c => b₀)
                ∇_Cᵢ = [∇ⱼ(x => x₀, c => b₀) for ∇ⱼ in ∇_2]

                [fᵢ; Cᵢ; det([∇ᵢ ∇_Cᵢ])]
            end
            @var v[1:6, 1:5]
            I = vcat(map(i -> Incidence(f, a, g, v[:, i], y[:, i]), 1:5)...)
            F = System(I, [a; vec(y)], vec(v))
            @test size(F) == (15, 15)
        end

        @testset "Reach plane curve" begin
            @var x y
            f = (x^3 - x * y^2 + y + 1)^2 * (x^2 + y^2 - 1) + y^2 - 5
            ∇ = differentiate(f, [x; y]) # the gradient
            H = differentiate(∇, [x; y]) # the Hessian

            g = ∇ ⋅ ∇
            v = [-∇[2]; ∇[1]]
            h = v' * H * v
            dg = differentiate(g, [x; y])
            dh = differentiate(h, [x; y])

            ∇σ = g .* dh - ((3 / 2) * h) .* dg

            F = System([v ⋅ ∇σ; f], [x, y])
            @test size(F) == (2, 2)
        end
    end

    @testset "System" begin
        @var x y a b
        f = [(x + y)^3 + x^2 + x + 5y + 3a, 2 * x^2 + b]
        F = System(f, [x, y], [b, a])

        show_F = """
        System of length 2
         2 variables: x, y
         2 parameters: b, a

         3*a + x + 5*y + x^2 + (x + y)^3
         b + 2*x^2"""
        @test sprint(show, F) == show_F

        T = ModelKit.type_level(F)
        F2 = ModelKit.interpret(T)
        @test F == F2
        @test sprint(show, T) == "TSystem encoding: $show_F"
        @test size(T) == size(F) == (2, 2)
    end

    @testset "Homotopy" begin
        @var x y z t

        h = [x^2 + y + z + 2t,
         4 * x^2 * z^2 * y + 4z - 6x * y * z^2]
        H = Homotopy(h, [x, y, z], t)

        show_H = """
        Homotopy in t of length 2
         3 variables: x, y, z

         2*t + y + z + x^2
         4*z - 6*x*y*z^2 + 4*x^2*y*z^2"""

        @test sprint(show, H) == show_H

        T = ModelKit.type_level(H)
        H2 = ModelKit.interpret(T)
        @test H == H2
        @test sprint(show, T) == "THomotopy encoding: $show_H"
        @test size(T) == size(H) == (2, 3)
    end

    @testset "Codegen helpers" begin
        @test ModelKit.sqr(3 + 2im) == (3 + 2im)^2
        @test ModelKit.sqr(3) == 3^2
    end

    include("test_instructions.jl")
end
