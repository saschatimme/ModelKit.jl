using ModelKit
using Test

@testset "ModelKit.jl" begin
    # Write your own tests here.

    @testset "Variables" begin
        @var a b x[1:2] y[1:2,1:3]

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
end
