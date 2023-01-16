module Fixes
#export Fix, Fix1, Fix2, FixFirst, FixLast, UnfixedArgument, UnfixedArgumentSplat, @underscores
using REPL
init_repl() = pushfirst!(Base.active_repl_backend.ast_transforms, underscores!)
macro underscores(ex)  esc(underscores!(ex))  end
underscores!(ex) = let  isexpr=Meta.isexpr, 
                        unfixarg=:(Fixes.UnfixedArgument()), unfixargsplat=:(Fixes.UnfixedArgumentSplat()), 
                        fix=:(Fixes.Fix), broadcaster=:(Fixes.BroadcastFix)
    ex == :_ && return :identity
    ex isa Expr && !(isexpr(ex, :using) || isexpr(ex, :quote)) || return ex
    hasunderscore(args) = any(x->x==:_ || x==:(_...), args)
    if isexpr(ex, :call) && hasunderscore(ex.args[2:end])
        if string(ex.args[1])[1] != '.'  # normal function call; avoid the broadcasting infix operators
            findfirst(==(:(_...)), ex.args) == findlast(==(:(_...)), ex.args) || error("only one _... splat permitted")
            ex.args[1] != :_ || error("wut u doin?!?")
            if length(ex.args) > 2 && isexpr(ex.args[2], :parameters) # pull parameters forward
                let (f, p) = ex.args[1:2];  ex.args[1:2] .= (p, f)  end
            end
            pushfirst!(ex.args, fix)
            ex.args .= replace(ex.args, :_ => unfixarg, :(_...) => unfixargsplat)
        else # infix operator broadcasting (did you know that .> gets converted to Expr(:., :>) ? wth???)
            newex = Expr(:call)
            newex.args = Any[Symbol(string(ex.args[1])[2:end]); ex.args[2:end]]
            ex.head, ex.args = :call, Any[broadcaster, underscores!(newex)]
        end
    elseif isexpr(ex, :.) && length(ex.args) ≥ 2 && isexpr(ex.args[2], :tuple) && hasunderscore(ex.args[2].args) # normal broadcasting
        newex = Expr(:call)
        newex.args = Any[ex.args[1]; ex.args[2].args]
        ex.head, ex.args = :call, Any[broadcaster, underscores!(newex)]
    elseif isexpr(ex, :call) && length(ex.args) > 1 && first(ex.args[2].args) == :_  # fix all args by calling f(a, b; _)
        popfirst!(ex.args[2].args)
        let (f, p) = ex.args[1:2];  ex.args[1:2] .= (p, f)  end # pull parameters forward
        pushfirst!(ex.args, fix)
    elseif isexpr(ex, :.) && length(ex.args) == 2 && (ex.args[1] == :_ || ex.args[2] == :(:_)) # getproperty special case
        ex.head, ex.args = :call, Any[:getproperty, ex.args[1], ex.args[2] == :(:_) ? :_ : ex.args[2]]
        underscores!(ex)
    elseif isexpr(ex, :ref) && hasunderscore(ex.args) # getindex special case
        ex.head, ex.args = :call, Any[:getindex; ex.args]
        underscores!(ex)
    elseif isexpr(ex, :string) && hasunderscore(ex.args) # string special case
        ex.head, ex.args = :call, Any[:string; ex.args]
        underscores!(ex)
    end
    if isexpr(ex, :(=));  ex.args[2] = underscores!(ex.args[2])  # don't replace underscores being assigned to
    else  @. ex.args = underscores!(ex.args)  end
    ex
end

struct UnfixedArgument end       
struct UnfixedArgumentSplat end
Base.show(io::IO, ::UnfixedArgument) = print(io, "_")
Base.show(io::IO, ::UnfixedArgumentSplat) = print(io, "_...")
Base.length(::Union{UnfixedArgument,UnfixedArgumentSplat}) = 1
Base.iterate(a::Union{UnfixedArgument,UnfixedArgumentSplat}, n=1) = a
struct Fix{F, A<:Tuple, K<:NamedTuple} #<: Function # I want pretty-printing for now, but we should subtype Function
    f::F; args::A; kw::K
    @inline Fix(f::F, args...; kw...) where F = let kw=(; kw...); new{F, typeof(args), typeof(kw)}(f, args, kw) end
end
_showargs(args::Tuple) = join(map(repr, args), ", ")
_showargs(kw::NamedTuple) = isempty(kw) ? "" : "; " * join(("$k = " * repr(v) for (k,v) = pairs(kw)), ", ")
Base.show(io::IO, f::Fix) = print(io, repr(f.f), "(", _showargs(f.args), _showargs(f.kw), ")")
@inline (f::Fix{F,A,K})(args...; kw...) where {F,A,K} = f.f(_assemble_args(f.args, args)...; f.kw..., kw...)
@inline @generated _assemble_args(fargs::T1, args::T2) where {T1<:Tuple, T2<:Tuple} = let out_ex = Expr(:tuple)
    t1, t2 = map(fieldtypes, (T1, T2)) 
    i, j = 1, 1
    while true # front args
        if i > length(t1);  j > length(t2) || error("too many arguments"); return out_ex  end
        if t1[i] ≡ UnfixedArgument;  push!(out_ex.args, Expr(:call, :getindex, :args, j)); i+=1; j+=1
        elseif t1[i] ≡ UnfixedArgumentSplat;  break # switch to filling in back args
        else  push!(out_ex.args, Expr(:call, :getindex, :fargs, i)); i+=1  end
    end
    k, l, backargs = lastindex(t1), lastindex(t2), []
    while true # back args
        if l < j  out_ex.args = Any[out_ex.args; backargs]; return out_ex  end
        if t1[k] ≡ UnfixedArgument;  pushfirst!(backargs, Expr(:call, :getindex, :args, l)); k-=1; l-=1
        elseif t1[k] ≡ UnfixedArgumentSplat; pushfirst!(backargs, Expr(:call, :getindex, :args, l)); l-=1
        else  pushfirst!(backargs, Expr(:call, :getindex, :fargs, k)); k-=1  end        
    end
end
const Fix1{F,X} = Fix{F,Tuple{X,UnfixedArgument},typeof((;))} where {F,X}
const Fix2{F,X} = Fix{F,Tuple{UnfixedArgument,X},typeof((;))} where {F,X}
const Fix0_2p{F} = let T=Tuple, U=UnfixedArgument, US=UnfixedArgumentSplat, nkw=typeof((;))  # edge case d'oh
    Union{Fix{F,T{U,U},nkw} where F, Fix{F,T{U,US},nkw} where F, Fix{F,T{US,U},nkw} where F, Fix{F,T{US,US},nkw} where F}
end
Fix1(f, x) = Fix(f, x, UnfixedArgument())
Fix2(f, x) = Fix(f, UnfixedArgument(), x)
Base.show(io::IO, f::Fix{typeof(getproperty)}) = print(io, repr(f.args[1]), ".", f.args[2])
Base.show(io::IO, f::Fix{typeof(getindex)}) = print(io, repr(f.args[1]), "[", _showargs(f.args[2:end]), _showargs(f.kw), "]")
const FixFirst{F,X} = Fix{F,Tuple{X,UnfixedArgumentSplat},typeof((;))} where {F,X}
const FixLast{F,X}  = Fix{F,Tuple{UnfixedArgumentSplat,X},typeof((;))} where {F,X}
FixFirst(f, x) = Fix(f, x, UnfixedArgumentSplat())
FixLast(f, x)  = Fix(f, UnfixedArgumentSplat(), x)
@inline Base.getproperty(f::Union{Fix1,FixFirst}, s::Symbol) = s == :x ? getfield(f, :args)[1] : getfield(f, s) # backwards compatibility
@inline Base.getproperty(f::Union{Fix2,FixLast},  s::Symbol) = s == :x ? getfield(f, :args)[2] : getfield(f, s) # backwards compatibility
@inline Base.getproperty(f::Fix0_2p, s::Symbol) = getfield(f, s) # edge case
(f::Fix1)(y) = f.f(f.x, y) # specialization
(f::Fix2)(y) = f.f(y, f.x) # specialization
struct BroadcastFix{F,A,K} f::Fix{F,A,K} end
(bf::BroadcastFix{F,A,K})(args...; kw...) where {F,A,K} = Broadcast.BroadcastFunction(bf.f.f)(_assemble_args(bf.f.args, args)...; bf.f.kw..., kw...)
Base.show(io::IO, bf::BroadcastFix) = print(io, repr(bf.f.f), ".(", _showargs(bf.f.args), _showargs(bf.f.kw), ")")
Base.length(bf::BroadcastFix) = maximum(length, bf.f.args)
Base.iterate(bf::BroadcastFix, (i,t)=(1,zip(map(a->length(a)==1 ? Iterators.repeated(a) : Iterators.cycle(a), bf.f.args)...))) = 
    i > length(bf) ? nothing : let (f,t) = Iterators.peel(t);  Fix(bf.f.f, f...; bf.f.kw...), (i+1, t)  end
end