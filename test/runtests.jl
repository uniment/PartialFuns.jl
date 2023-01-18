using PartialFuns
using Test

@testset "PartialFuns.jl" begin
    @underscores begin
        # PR24990 tests
        @test div(_, 3)(13) === 4
        @test (_+1)(3) === 4
        @test (_.re)(5+6im) === 5
        @test (_[2])([7,8,9]) === 8
        @test div.(10,_)([1,2,3,4]) == [10,5,3,2]
        @test (_ .+ 1)([1,2,3,4]) == [2,3,4,5]
        @test (_ // _)(3,4) === 3//4
        let _round(x,d; kws...) = round(x; digits=d, kws...) # test a 2-arg func with keywords
            @test _round(_, 2, base=10)(pi) == 3.14
            @test _round(_, 2, base=2)(pi) === _round(_, _, base=2)(pi, 2) == 3.25
        end
        @test split(_)("a b") == ["a","b"]
        @test split(_, limit=2)("a b c") == ["a","b c"]
        #@test Meta.lower(@__MODULE__, :(f(_...))) == Expr(:error, "invalid underscore argument \"_...\"") fail
        # Additional tests
        @test _+1 ≡ _+1
        @test _+1 == _+1
        let x=(a=1,)
            @test (_.a)(x)  === 1
            @test (x._)(:a) === 1
            @test (_[1])(x) === 1
            @test (x[_])(1) === 1
        end
        @test _[_, _](ones(2, 2), 2, 2) === 1.0
        @test _[_...](ones(2, 2), 2, 2) === 1.0
        let f(a,b)=a(b)
            @test _(1)(_+2)    === 3
            @test (_+2)(_)(1)  === 3
            @test _(_)(_+2, 1) === 3
        end 
        let f=_;  @test f === PartialFun(identity, UnfixedArg())  end
        @test _ + 2 isa Fix2{typeof(+), Int}
        @test _ + 2 === Fix2(+, 2)
        @test 1 + _ isa Fix1{typeof(+), <:Number}
        @test 1 + _ === Fix1(+, 1)
        @test Fix1(+, 1) isa Fix1
        @test !(Fix1(+, 1) isa Fix2)
        @test !(Fix1(+, 1) isa FixFirst)
        @test !(Fix2(+, 2) isa FixLast)
        @test !(FixFirst(+, 1) isa Fix1)
        @test (_ + 2).f === +
        @test (_ + 2).x === 2
        @test (1 + _).f === +
        @test (1 + _).x === 1
        @test +(1, _...) isa FixFirst{typeof(+), Int}
        @test +(1, _...) === FixFirst(+, 1)
        @test +(_..., 9) isa FixLast{typeof(+), Int}
        @test +(_..., 9) === FixLast(+, 9)
        @test map(_^2, _...) isa FixFirst{typeof(map), typeof(_^2)}
        let _! = UnfixedArg(), _!s = UnfixedArgSplat()
            @test +(_, 2, _, _..., 9, _; a=1) === PartialFun(+, _!, 2, _!, _!s, 9, _!; a=1)
        end
        @test "hi $_"("there") === "hi there"
        @test "hi $(_...) and $_"("joe", "mary", "steve", "paul") === "hi joemarysteve and paul"
        let f(a...; kw...) = (a, (; kw...))
            @test f.(_, (1, 2, 3))((3, 2, 1)) === (((3, 1), (;)), ((2, 2), (;)), ((1, 3), (;)))
            @test f(1, _, 3, _)(2, 4) === ((1, 2, 3, 4), (;))
            @test f(_, 1, _..., 4, _)(0, 2, 3, 5) === ((0, 1, 2, 3, 4, 5), (;))
            @test f(_...; a=:a)(1, 2, 3; b=:b) === ((1, 2, 3), (a=:a, b=:b))
            @test f(_...; a=:a)(a=:b) === ((), (a=:b,))
        end
        @test (_ .> 1:5)(3) == [1, 1, 0, 0, 0]
        let f(a, b) = a(b)
            @test f.(_ .> (1:5), 5:-1:1) == f.(.>(1:5), 5:-1:1) == [1, 1, 0, 0, 0]
        end
        @test collect((_ .+ (1:5))(5:-1:1)) == [6, 6, 6, 6, 6]
        let data=(43, 89, 97, 40, 98, 1, 25, 68, 76, 19, 32, 35, 14, 13, 5, 11, 27, 24, 100, 32)
            @test map(_^2, data) === (1849, 7921, 9409, 1600, 9604, 1, 625, 4624, 5776, 361, 1024, 1225, 196, 169, 25, 121, 729, 576, 10000, 1024)
            @test filter(<(2000) ∘ _^2, data) === (43, 40, 1, 25, 19, 32, 35, 14, 13, 5, 11, 27, 24, 32)
        end
        @test +(1, _, 3)(2) === 6
        @test let f=_::Int; f(0) === 0 end
        @test let f=_; f(5) === 5 end
        @test let f(a, b, c) = a+b+c;  f(_::Int...)(1, 2, 3)  end === 6
        @test let f(a, b) = a(b);  f.(_+1, 1:3)  end  ==  [2, 3, 4]
        @test (_ .> 2)(1:4) == Bool[0, 0, 1, 1]
        @test (_ .> 1:4)(3) == Bool[1, 1, 0, 0]
        @test (_ .> 1:4)(4:-1:1) == Bool[1, 1, 0, 0]
        @test let f(a, b) = a(b);  f.((_ .> 1:4), 4:-1:1)  end == Bool[1, 1, 0, 0]
        @test let f(a, b) = a(b);  f.((_ .> 2), 4:-1:1)  end == Bool[1, 1, 0, 0]
    end
    let underscores! = PartialFuns.underscores!
        @test_throws "cannot splat functions into call" underscores!(:( (_...)(_) ))
        @test_throws "cannot splat functions into call" underscores!(:( (_...).(_) ))
        @test_throws "cannot splat functions into call" underscores!(:( (_::Int...)(_) ))
        @test_throws "cannot splat functions into call" underscores!(:( (_::Int...).(_) ))
        @test_throws TypeError eval(underscores!(:( let f=_::Int; f(2.5) end )))
    end
end
