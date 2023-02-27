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
        if string(ex.args[1])[1] != '.' || ex.args[1] ≡ :..  # normal function call; avoid the broadcasting infix operators
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
    elseif isexpr(ex, :.) && length(ex.args) == 2 && (is_uf(ex.args[1]) || ex.args[2] == :(:_)) # getproperty special case
        ex.head, ex.args = :call, Any[:getproperty, ex.args[1], ex.args[2] == :(:_) ? :_ : ex.args[2]]; underscores!(ex)
    elseif isexpr(ex, :tuple) && any(x->isexpr(x, :(=)) && is_uf(x.args[2]), ex.args) # NamedTuple special case 1
        k, v = map(x->QuoteNode(x.args[1]), ex.args), map(x->length(x.args)>1 ? (is_uf(x.args[2]) ? repl_undr(x.args[2]) : x.args[2]) : x.args[1], ex.args)
        newex = :(NamedTuple{($(k...),)} ∘ $fix(tuple, $(v...)))
        ex.head, ex.args = newex.head, newex.args; underscores!(ex)
    elseif isexpr(ex, :tuple) && length(ex.args) == 1 && isexpr(ex.args[1], :parameters) && any(x->isexpr(x, :kw) && is_uf(x.args[2]), ex.args[1].args) # NamedTuple special case 2
        k, v = map(x->isexpr(x, :kw) ? QuoteNode(x.args[1]) : QuoteNode(x), ex.args[1].args), map(x->isexpr(x, :kw) ? repl_undr(x.args[2]) : x.args[1], ex.args[1].args)
        newex = :(NamedTuple{($(k...),)} ∘ $fix(tuple, $(v...)))
        ex.head, ex.args = newex.head, newex.args; underscores!(ex)
    elseif greenlight # moar special cases
        flag = true
        if isexpr(ex, :ref);  pushfirst!(ex.args, :getindex) # getindex special case
        elseif isexpr(ex, :string);  pushfirst!(ex.args, :string) # string special case
        elseif isexpr(ex, :tuple);  pushfirst!(ex.args, :tuple) # tuple special case
        elseif isexpr(ex, :vect);  pushfirst!(ex.args, :(Base.vect)) # vect special case
        elseif isexpr(ex, :vcat);  pushfirst!(ex.args, :vcat) # vcat special case
        elseif isexpr(ex, :hcat);  pushfirst!(ex.args, :hcat) # hcat special case
        elseif isexpr(ex, Symbol("'"));  pushfirst!(ex.args, :adjoint) # adjoint special case
        elseif isexpr(ex, :curly);  pushfirst!(ex.args, :(Core.apply_type)) # apply_type special case
        else  flag = false  end
        flag && (ex.head = :call; underscores!(ex))
    end
    if isexpr(ex, (:(=), :(.=))) && (ex.args[1] ≡ :_ || isexpr(ex.args[1], :tuple) || isexpr(ex.args[1], :call)) || isexpr(ex, (:function, :->))
        ex.args[2] = underscores!(ex.args[2])  # don't replace underscores being assigned to, or function definitions
    else  @. ex.args = underscores!(ex.args)  end
    ex
end

# types and functions
import Base: show, length, iterate, getproperty, broadcastable, _stable_typeof
struct FixedArg{X} x::X;   FixedArg(x) = new{_stable_typeof(x)}(x)  end
struct UnfixedArg{T}       UnfixedArg(T) = new{T}();      UnfixedArg() = new{Any}()      end
struct UnfixedArgSplat{T}  UnfixedArgSplat(T) = new{T}(); UnfixedArgSplat() = new{Any}() end
const  UnfixedArgOrSplat{T} = Union{UnfixedArg{T}, UnfixedArgSplat{T}}
const  ArgTypes = Union{FixedArg, UnfixedArgOrSplat}
length(a::FixedArg) = length(a.x)
iterate(a::FixedArg, t=a.x) = Iterators.peel(t)
length(::UnfixedArgOrSplat) = 1
broadcastable(a::UnfixedArgOrSplat) = Ref(a)
parameters(T::DataType; discard=0) = Tuple(T.parameters)[1:end-discard]
parameters(T::UnionAll; discard=0) = parameters(T.body; ignore=discard+1)
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
struct PartialFun{A<:Tuple{Vararg{ArgTypes}}, K<:NamedTuple} <: Function
    args::A; kws::K
    @inline PartialFun{A,K}(args::A, kws::K) where {A<:Tuple{Vararg{Union{FixedArg,UnfixedArg}}},K} = new{A,K}(args, kws) # no splat specialization
    @inline PartialFun{A,K}(args::A, kws::K) where {A,K} = let # splat requires more error checks
        sum(a->a isa UnfixedArgSplat, args) > 1 && error("cannot have more than one unfixed argument splat") # count allocates in 1.9 for some reason; using sum
        args[1] isa UnfixedArgSplat && error("cannot splat functions into call")
        new{A,K}(args, kws)
    end
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
show(io::IO, pf::PartialFun) = show(io::IO, MIME"text/plain"(), pf)
show(io::IO, ::MIME"text/plain", pf::PartialFun) = print(io, _show(pf.args[1]), "(", _showargs(pf.args[2:end]), all(a->a isa FixedArg, pf.args) ? "; _" : "", _showargs(pf.kws), ")")
show(io::IO, ::MIME"text/plain", pf::PartialFun{T} where {T<:Tuple{FixedArg{typeof(getproperty)}, Vararg{ArgTypes}}}) = print(io, _show(pf.args[2]), ".", _show(pf.args[3]))
show(io::IO, ::MIME"text/plain", pf::PartialFun{T} where {T<:Tuple{FixedArg{typeof(getindex)}, Vararg{ArgTypes}}}) = 
    print(io, _show(pf.args[2]), "[", _showargs(pf.args[3:end]), _showargs(pf.kws), "]")
show(io::IO, ::MIME"text/plain", pf::PartialFun{T} where {T<:Tuple{FixedArg{typeof(string)}, Vararg{ArgTypes}}}) = 
    let str(x) = x isa UnfixedArg{Any} ? "\$"*_show(x) : x isa UnfixedArgOrSplat ? "\$("*_show(x)*")" : x.x
        print(io, "\"", map(str, pf.args[2:end])..., "\"")
    end
show(io::IO, ::MIME"text/plain", pf::PartialFun{T} where {T<:Tuple{FixedArg{typeof(tuple)}, Vararg{ArgTypes}}}) = print(io, "(", _showargs(pf.args[2:end]), ")")
@inline (pf::PartialFun)(args...; kws...) = let (f, args...) = _assemble_args(getfield(pf, :args), args); f(args...; getfield(pf, :kws)..., kws...) end
@inline @generated _assemble_args(fargs::TFA, args::TA) where {TFA<:Tuple, TA<:Tuple} = let out_ex = Expr(:tuple)
    T1s, T2s = map(parameters, (TFA, TA)) 
    i, j = 1, 1
    while true # front args
        if i > length(T1s);  j > length(T2s) || error("too many arguments"); return out_ex  end
        if T1s[i] <: UnfixedArg;  push!(out_ex.args, let a=:(getfield(args, $j)), T=parameters(T1s[i])[1]; T≡Any ? a : :($a::$T) end); i+=1; j+=1
        elseif T1s[i] <: UnfixedArgSplat;  break # switch to filling in back args
        else  push!(out_ex.args, :(getfield(getfield(fargs, $i), :x))); i+=1  end
    end
    k, l, backargs = lastindex(T1s), lastindex(T2s), []
    while true # back args
        if l < j  out_ex.args = Any[out_ex.args; backargs]; return out_ex  end
        if T1s[k] <: UnfixedArg;  pushfirst!(backargs, let a=:(getfield(args, $l)), T=parameters(T1s[k])[1]; T≡Any ? a : :($a::$T) end); k-=1; l-=1
        elseif T1s[k] <: UnfixedArgSplat; pushfirst!(backargs, let a=:(getfield(args, $l)), T=parameters(T1s[k])[1]; T≡Any ? a : :($a::$T) end); l-=1
        else  pushfirst!(backargs, :(getfield(getfield(fargs, $k), :x))); k-=1  end        
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
struct BroadcastPartialFun{A,K} #<: Function # subtyping Function opts-in to undesirable broadcasting behavior
    pf::PartialFun{A,K} 
end
(bf::BroadcastPartialFun)(args...; kws...)= let args = _assemble_args(bf.pf.args, args)
    Broadcast.BroadcastFunction(args[1])(args[2:end]...; bf.pf.kws..., kws...)
end
show(io::IO, bf::BroadcastPartialFun) = show(io, MIME"text/plain"(), bf)
show(io::IO, ::MIME"text/plain", bf::BroadcastPartialFun) = print(io, _show(bf.pf.args[1]), ".(", _showargs(bf.pf.args[2:end]), _showargs(bf.pf.kws), ")")
length(bf::BroadcastPartialFun) = maximum(length, bf.pf.args[2:end])
_tail_init(args) = zip(map(a->length(a) == 1 ? Iterators.repeated(a isa UnfixedArgOrSplat ? a : a.x) : Iterators.cycle(a.x), args)...)
iterate(bf::BroadcastPartialFun, (i,t)=(1, _tail_init(bf.pf.args[2:end]))) = 
    i > length(bf) ? nothing : let (h,t) = Iterators.peel(t);  PartialFun(bf.pf.args[1].x, h...; bf.pf.kws...), (i+1, t)  end
end # Fixes