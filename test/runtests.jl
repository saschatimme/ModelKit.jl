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
        @test det(x) == -x[2,1]*x[1,2] + x[2,2]*x[1,1]
    end
end
