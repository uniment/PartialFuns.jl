*PartialFuns.jl*
---

Refined partial function applicator types and parsing for underscore partial application syntax, à la [PR#24990](https://github.com/JuliaLang/julia/pull/24990).

You can do things like this!

```julia
julia> Fix2(getproperty, :a)
_.a

julia> Fix1(getindex, (1,2,3))
(1, 2, 3)[_]

julia> FixFirst(map, cos)
map(cos, _...)

julia> map(_^_, 1:3, 2:4)
3-element Vector{Int64}:
  1
  8
 81

julia> filter((_>10) ∘ (_^2), 1:5)
2-element Vector{Int64}:
 4
 5

julia> (_ .> ntuple(identity, 5))(3)
(true, true, false, false, false)

julia> map("hi $_", ("Jane", "Harold", "Leanne"))
("hi Jane", "hi Harold", "hi Leanne")
```


Support for:

- fixed argument counts
- varargs
- non-final varargs
- type assertion
- keyword arguments
- `getindex`
- `getproperty`
- `string` interpolation
- `tuple`
- `NamedTuple`
- `Base.vect`
- `vcat`
- `hcat`
- `adjoint`
- `Core.apply_type`
- unfixed function name
- broadcasting

Does not support at the moment:
- `setindex!`
- `setproperty!`
- `hvcat`
- `hvncat`
- broadcast fusion

Provides types:

- `PartialFun`, which generalizes
- `Fix1` and
- `Fix2` with backward compatibility, and
- `FixFirst` and 
- `FixLast` 


## Getting Started

Run this in your REPL:

```julia
using PartialFuns
PartialFuns.init_repl()
```

Then the fun begins!

`init_repl()` makes it so that underscores are parsed on every line in the REPL. Otherwise, you can use the `@underscores` macro. This macro is recursive, so you can call the macro on entire code blocks.

Note: This code performs a syntax transform at the earliest stage possible, meaning that it will break macros that use underscores. If this was a language feature instead of just user code, that wouldn't be the case, because the syntax transform would occur *after* macro expansion. 


## Demos to Try

Run these and see what you get:

```julia
_
1+_
1+_ isa Fix1{typeof(+), Int}
_*2. isa Fix2{typeof(*), Float64}
map(_^2, _...) isa FixFirst{typeof(map), typeof(_^2)}
join(_..., ", ") isa FixLast
Fix1
map(_^2, (1,2,3))
map(_+_, _...)((1,2,3), (4,5,6))
let f(a...; k...) = (a, (;k...));  f(_, 2, _..., 5, _; a=1)(1, 3, 4, 6; b=2)  end
let x=(a=1,);  (_.a)(x), (x._)(:a), (_._)(x, :a)  end
let x=(a=1,);  (_[1])(x), (x[_])(1), (_[_])(x, 1)  end
let x=reshape(1:9,3,3);  (x[_, 2])(2), (x[_, _])(2, 2), (x[_...])(2, 2)  end
map("Hello $_ and $_", (:Mary, :Matt, :Kelly), (:John, :Susan, :Dave))
(_ .> 2)(1:3)
(_ .> 1:3)(2)
(_ .> 1:3)(3:-1:1)
let f(a, b) = a(b);  f.((_ .> 1:3), 3:-1:1)  end
let f(a, b) = a(b);  f.((_ .> 2), 3:-1:1)  end
let f(a, b) = a(b);  f.([_^1 _^2; _^3 _^4], [1 2; 3 4])  end
_(_).((sin, cos), (π/2, 0))
(1, _, 3)(2)
(a=1, b=_, c=3)(2)
[1, _, 3](2)
[[1, 2]; _]([3, 4])
[1 _ 3](2)
_'([1, 2])
NamedTuple{_}((:a, :b))((1, 2))
```
