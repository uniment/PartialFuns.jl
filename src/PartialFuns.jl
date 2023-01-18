module PartialFuns 
export PartialFun, Fix1, Fix2, FixFirst, FixLast, FixedArg, UnfixedArg, UnfixedArgSplat, @underscores
using .Meta
init_repl() = let at=Base.active_repl_backend.ast_transforms; first(at) ≡ underscores! || pushfirst!(at, underscores!); at end

# syntax transform
macro underscores(ex)  esc(underscores!(ex))  end
underscores!(ex) = let  uf=:(PartialFuns.UnfixedArg), ufs=:(PartialFuns.UnfixedArgSplat),
                        fix=:(PartialFuns.PartialFun), broadcaster=:(PartialFuns.BroadcastPartialFun),
    is_uf(ex::Symbol) = ex ≡ :_
    is_uf(ex) = isexpr(ex, :(::)) && is_uf(ex.args[1]) # if we care about performance
    is_ufs(ex) = isexpr(ex, :...) && is_uf(ex.args[1]) # then we will solve issue #47760
    is_uf_or_ufs(ex) = is_uf(ex) || is_ufs(ex)
    repl_undr(ex::Symbol, start=ex) = is_uf(ex) ? (ex ≡ start ? :($uf()) : :($ufs())) : ex
    repl_undr(ex, start=ex) = if isexpr(ex, :(::)) && is_uf(ex.args[1]);  ex ≡ start ? :($uf($(ex.args[2]))) : :($ufs($(ex.args[2])))
        elseif ex ≡ start && isexpr(ex, :...);  repl_undr(ex.args[1], ex)
        else  start  end

    is_uf_or_ufs(ex) && return Expr(:call, fix, :identity, repl_undr(ex))
    ex isa Expr && !(isexpr(ex, :using) || isexpr(ex, :quote)) || return ex
    greenlight = any(is_uf_or_ufs, ex.args)
    if isexpr(ex, :call) && greenlight
        isexpr(ex.args[1], :...) && error("cannot splat functions into call")
        if string(ex.args[1])[1] != '.'  # normal function call; avoid the broadcasting infix operators
            findfirst(x->isexpr(:..., x), ex.args) == findlast(x->isexpr(:..., x), ex.args) || error("only one _... splat permitted")
            if length(ex.args) > 2 && isexpr(ex.args[2], :parameters) # pull parameters forward
                ex.args[1:2] .= reverse(ex.args[1:2])
            end
            pushfirst!(ex.args, fix)
            ex.args .= map(repl_undr, ex.args)
        else # infix operator broadcasting (did you know that .> gets converted to Expr(:., :>) ? wth???)
            newex = Expr(:call)
            newex.args = Any[Symbol(string(ex.args[1])[2:end]); ex.args[2:end]]
            ex.head, ex.args = :call, Any[broadcaster, underscores!(newex)]
        end
    elseif isexpr(ex, :.) && length(ex.args) ≥ 2 && isexpr(ex.args[2], :tuple) && any(is_uf_or_ufs, ex.args[2].args) # normal broadcasting
        newex = Expr(:call)
        newex.args = Any[ex.args[1]; ex.args[2].args]
        ex.head, ex.args = :call, Any[broadcaster, underscores!(newex)]
    elseif isexpr(ex, :call) && length(ex.args) > 1 && isexpr(ex.args[2], :parameters) && !isempty(ex.args[2].args) && first(ex.args[2].args) == :_  # fix all args by calling f(a, b; _)
        popfirst!(ex.args[2].args)
        let (f, p) = ex.args[1:2];  ex.args[1:2] .= (p, f)  end # pull parameters forward
        pushfirst!(ex.args, fix)
    elseif isexpr(ex, :.) && length(ex.args) == 2 && (ex.args[1] == :_ || ex.args[2] == :(:_)) # getproperty special case
        ex.head, ex.args = :call, Any[:getproperty, ex.args[1], ex.args[2] == :(:_) ? :_ : ex.args[2]]
        underscores!(ex)
    elseif isexpr(ex, :ref) && greenlight # getindex special case
        ex.head, ex.args = :call, Any[:getindex; ex.args]
        underscores!(ex)
    elseif isexpr(ex, :string) && greenlight # string special case
        ex.head, ex.args = :call, Any[:string; ex.args]
        underscores!(ex)
    end
    if isexpr(ex, :(=)) && (ex.args[1] ≡ :_ || isexpr(ex.args[1], :tuple));  ex.args[2] = underscores!(ex.args[2])  # don't replace underscores being assigned to
    else  @. ex.args = underscores!(ex.args)  end
    ex
end

# types and functions
import Base: show, length, iterate, getproperty, broadcastable
struct FixedArg{X} x::X;   FixedArg(x::X) where X = new{X}(x)  end
struct UnfixedArg{T}       UnfixedArg(T) = new{T}();      UnfixedArg() = new{Any}()      end
struct UnfixedArgSplat{T}  UnfixedArgSplat(T) = new{T}(); UnfixedArgSplat() = new{Any}() end
const  UnfixedArgOrSplat{T} = Union{UnfixedArg{T}, UnfixedArgSplat{T}}
const  ArgTypes = Union{FixedArg, UnfixedArgOrSplat}
length(a::FixedArg) = length(a.x)
iterate(a::FixedArg, t=a.x) = Iterators.peel(t)
length(::UnfixedArgOrSplat) = 1
broadcastable(a::UnfixedArgOrSplat) = Ref(a)
"""```
    PartialFun(f, args...; kws...)
```
Construct a partially-applied function which calls `f` on the specified arguments. To specify unfilled arguments, use `UnfixedArg(T)` or `UnfixedArgSplat(T)`, where `T` is the type to assert the unfilled argument take. To avoid type assertion, use `UnfixedArg()` or `UnfixedArgSplat()`.

Example:
```
julia> f = PartialFun(+, 1, UnfixedArg())
+(1, _)

julia> f(2)
3
```"""
struct PartialFun{A<:Tuple{Vararg{ArgTypes}}, K<:NamedTuple} #<: Function # I want pretty-printing for now, but we should subtype Function
    args::A; kws::K
    @inline PartialFun{A,K}(args::A, kws::K) where {A,K} = new{A, K}(args, kws)
end
@inline PartialFun(args...; kws...) = let kws=(;kws...), args=map(a->a isa UnfixedArgOrSplat ? a : FixedArg(a), args)
    PartialFun{typeof(args), typeof(kws)}(args, kws)
end
broadcastable(f::PartialFun) = Ref(f)
_show(x::FixedArg) = repr(x.x)
_show(::UnfixedArg{T}) where T = T≡Any ? "_" : "_::$T"
_show(::UnfixedArgSplat{T}) where T = T≡Any ? "_..." : "_::$T..."
_showargs(args::Tuple) = join(map(_show, args), ", ")
_showargs(kws::NamedTuple) = isempty(kws) ? "" : "; " * join(("$k = " * repr(v) for (k,v) = pairs(kws)), ", ")
show(io::IO, f::PartialFun) = print(io, _show(f.args[1]), "(", _showargs(f.args[2:end]), all(a->a isa FixedArg, f.args[2:end]) ? "; _" : "", _showargs(f.kws), ")")
show(io::IO, f::PartialFun{T} where {T<:Tuple{FixedArg{typeof(getproperty)}, Vararg{ArgTypes}}}) = print(io, _show(f.args[2]), ".", _show(f.args[3]))
show(io::IO, f::PartialFun{T} where {T<:Tuple{FixedArg{typeof(getindex)}, Vararg{ArgTypes}}}) = 
    print(io, _show(f.args[2]), "[", _showargs(f.args[3:end]), _showargs(f.kws), "]")
show(io::IO, f::PartialFun{T} where {T<:Tuple{FixedArg{typeof(string)}, Vararg{ArgTypes}}}) = 
    let str(x) = x isa UnfixedArg{Any} ? "\$"*_show(x) : x isa UnfixedArgOrSplat ? "\$("*_show(x)*")" : x.x
        print(io, "\"", map(str, f.args[2:end])..., "\"")
    end
@inline (f::PartialFun)(args...; kws...) = call(_assemble_args(getfield(f, :args), args)...; getfield(f, :kws)..., kws...)
@inline call(args...; kws...) = let (f, args...) = args;  f(args...; kws...)  end
parameters(T::DataType; ignore=0) = Tuple(T.parameters)[1:end-ignore]
parameters(T::UnionAll; ignore=0) = parameters(T.body; ignore=ignore+1)
@inline @generated _assemble_args(fargs::T1, args::T2) where {T1<:Tuple, T2<:Tuple} = let out_ex = Expr(:tuple)
    t1, t2 = map(parameters, (T1, T2)) 
    i, j = 1, 1
    while true # front args
        if i > length(t1);  j > length(t2) || error("too many arguments"); return out_ex  end
        if t1[i] <: UnfixedArg;  push!(out_ex.args, let a=:(args[$j]), T=parameters(t1[i])[1]; T≡Any ? a : :($a::$T) end); i+=1; j+=1
        elseif t1[i] <: UnfixedArgSplat;  break # switch to filling in back args
        else  push!(out_ex.args, :(fargs[$i].x)); i+=1  end
    end
    k, l, backargs = lastindex(t1), lastindex(t2), []
    while true # back args
        if l < j  out_ex.args = Any[out_ex.args; backargs]; return out_ex  end
        if t1[k] <: UnfixedArg;  pushfirst!(backargs, let a=:(args[$l]), T=parameters(t1[k])[1]; T≡Any ? a : :($a::$T) end); k-=1; l-=1
        elseif t1[k] <: UnfixedArgSplat; pushfirst!(backargs, let a=:(args[$l]), T=parameters(t1[k])[1]; T≡Any ? a : :($a::$T) end); l-=1
        else  pushfirst!(backargs, :(fargs[$k].x)); k-=1  end        
    end
end
const Fix1{F,X} = PartialFun{Tuple{FixedArg{F},FixedArg{X},UnfixedArg{UF}},typeof((;))} where {F,X,UF}
const Fix2{F,X} = PartialFun{Tuple{FixedArg{F},UnfixedArg{UF},FixedArg{X}},typeof((;))} where {F,X,UF}
Fix1(f, x) = PartialFun(f, x, UnfixedArg())
Fix2(f, x) = PartialFun(f, UnfixedArg(), x)
(f::Fix1)(y; kws...) = getfield(getfield(getfield(f, :args), 1), :x)(getfield(getfield(getfield(f, :args), 2), :x), y; kws...) # specialization
(f::Fix2)(y; kws...) = getfield(getfield(getfield(f, :args), 1), :x)(y, getfield(getfield(getfield(f, :args), 3), :x); kws...) # specialization
const FixFirst{F,X} = PartialFun{Tuple{FixedArg{F},FixedArg{X},UnfixedArgSplat{UF}},typeof((;))} where {F,X,UF}
const FixLast{F,X}  = PartialFun{Tuple{FixedArg{F},UnfixedArgSplat{UF},FixedArg{X}},typeof((;))} where {F,X,UF}
FixFirst(f, x) = PartialFun(f, x, UnfixedArgSplat())
FixLast(f, x)  = PartialFun(f, UnfixedArgSplat(), x)
@inline getproperty(f::Union{Fix1,FixFirst}, s::Symbol) = s ∈ (:f, :x) ? getfield(f, :args)[s≡:f ? 1 : 2].x : getfield(f, s) # backwards compatibility
@inline getproperty(f::Union{Fix2,FixLast},  s::Symbol) = s ∈ (:f, :x) ? getfield(f, :args)[s≡:f ? 1 : 3].x : getfield(f, s) # backwards compatibility
struct BroadcastPartialFun{A,K} f::PartialFun{A,K} end
(bf::BroadcastPartialFun)(args...; kws...)= let args = _assemble_args(bf.f.args, args)
    Broadcast.BroadcastFunction(args[1])(args[2:end]...; bf.f.kws..., kws...)
end
show(io::IO, bf::BroadcastPartialFun) = print(io, _show(bf.f.args[1]), ".(", _showargs(bf.f.args[2:end]), _showargs(bf.f.kws), ")")
length(bf::BroadcastPartialFun) = maximum(length, bf.f.args[2:end])
_tail_init(args) = zip(map(a->length(a) == 1 ? Iterators.repeated(a isa UnfixedArgOrSplat ? a : a.x) : Iterators.cycle(a.x), args)...)
iterate(bf::BroadcastPartialFun, (i,t)=(1, _tail_init(bf.f.args[2:end]))) = 
    i > length(bf) ? nothing : let (h,t) = Iterators.peel(t);  PartialFun(bf.f.args[1].x, h...; bf.f.kws...), (i+1, t)  end

end # Fixes