@testset "Instructions" begin

    @testset "Higher order pow diff" begin
        @var x
        for d in [2, 5]
            f = x^d
            list, _ = ModelKit.instruction_list([f])

            diff_map = Dict()
            diff_map[(:x, 1)] = :x1
            diff_map[(:x, 2)] = :x2
            diff_map[(:x, 3)] = :x3

            @eval ModelKit begin
                function __diff_4_pow(x, t)
                    x1 = diff(x, t)
                    x2 = diff(x, t, t) / 2
                    x3 = diff(x, t, t, t) / 6
                    $(ModelKit.to_expr(ModelKit.univariate_diff!(
                        list,
                        4,
                        diff_map,
                    )))
                end
            end

            SE.@funs u
            @var t

            exp1 = SE.expand(
                SE.subs(diff(u(t)^d, t, 4), diff(u(t), t, 4) => 0) /
                factorial(4),
            )

            exp2 = SE.expand(ModelKit.__diff_4_pow(u(t), t))
            @test exp1 == exp2
        end
    end

    @testset "Higher order mul" begin
        @var x y
        f = x * y
        list, _ = ModelKit.instruction_list([f])

        diff_map = Dict()
        diff_map[(:x, 1)] = :x1
        diff_map[(:x, 2)] = :x2
        diff_map[(:x, 3)] = :x3
        diff_map[(:y, 1)] = :y1
        diff_map[(:y, 2)] = :y2
        diff_map[(:y, 3)] = :y3

        @eval ModelKit begin
            function __diff_4_mul__(x, y, t)
                x1 = diff(x, t)
                x2 = diff(x, t, 2) / 2
                x3 = diff(x, t, 3) / 6
                y1 = diff(y, t)
                y2 = diff(y, t, 2) / 2
                y3 = diff(y, t, 3) / 6
                $(ModelKit.to_expr(ModelKit.univariate_diff!(
                    list,
                    4,
                    diff_map,
                )))
            end
        end

        SE.@funs u v
        @var t

        exp1 = SE.expand(
            SE.subs(
                diff(u(t) * v(t), t, 4),
                diff(u(t), t, 4) => 0,
                diff(v(t), t, 4) => 0,
            ) / factorial(4),
        )

        exp2 = SE.expand(ModelKit.__diff_4_mul__(u(t), v(t), t))
        @test exp1 == exp2
    end

    @testset "Higher order plus" begin
        @var x y
        f = x + y
        list, _ = ModelKit.instruction_list([f])

        diff_map = Dict()
        diff_map[(:x, 1)] = :x1
        diff_map[(:x, 2)] = :x2
        diff_map[(:x, 3)] = :x3
        diff_map[(:y, 1)] = :y1
        diff_map[(:y, 2)] = :y2
        diff_map[(:y, 3)] = :y3

        @eval ModelKit begin
            function __diff_3_plus__(x, y, t)
                x1 = diff(x, t)
                x2 = diff(x, t, 2) / 2
                x3 = diff(x, t, 3) / 6
                y1 = diff(y, t)
                y2 = diff(y, t, 2) / 2
                y3 = diff(y, t, 3) / 6
                $(ModelKit.to_expr(ModelKit.univariate_diff!(
                    list,
                    3,
                    diff_map,
                )))
            end
        end

        SE.@funs u v
        @var t

        exp1 = SE.expand(diff(u(t) + v(t), t, 3) / factorial(3))

        exp2 = SE.expand(ModelKit.__diff_3_plus__(u(t), v(t), t))
        @test exp1 == exp2
    end
end
