# Note: I had thought of making (_,) turn into tuple(_), and I implemented the whole thing below.
# However, that precludes any ability to make a collection like (_, _^2, _^3, _^4), so I'm saying no. If you want a tuple, write `tuple`.
#elseif isexpr(ex, :tuple) && hasunderscore(ex.args) # tuple special case
#    ex.head, ex.args = :call, Any[:tuple; ex.args]
#    underscores!(ex)
#elseif isexpr(ex, :tuple) && all(isexpr(x, :(=)) for x ∈ ex.args) && any(x.args[2] == :_ for x ∈ ex.args) # NamedTuple special case 1
#    n, v = [], []
#    for x ∈ ex.args;  push!(n, QuoteNode(x.args[1])); push!(v, x.args[2]);  end
#    ex.head, ex.args = :call, Any[:∘, :(NamedTuple{($(n...),)}), :(($(v...),))]
#    underscores!(ex)
#elseif isexpr(ex, :tuple) && length(ex.args)==1 && isexpr(ex.args[1], :parameters) && any(isexpr(x, :kw) && x.args[2]==:_ for x ∈ ex.args[1].args)
#    # NamedTuple special case 2
#    n, v = [], []
#    for x ∈ ex.args[1].args
#        if isexpr(x, :kw)  push!(n, QuoteNode(x.args[1])); push!(v, x.args[2])
#        else  push!(n, QuoteNode(x)); push!(v, x)  end
#    end
#    ex.head, ex.args = :call, Any[:∘, :(NamedTuple{($(n...),)}), :(($(v...),))]
#    underscores!(ex)
