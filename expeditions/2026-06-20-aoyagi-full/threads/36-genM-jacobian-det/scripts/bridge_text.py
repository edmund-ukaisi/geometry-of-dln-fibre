# The Aoyagi exponent T=(t^1,...,t^L) and the chain Text=[Text_0,...,Text_L] must be related.
# Aoyagi convention: t^j = surviving rank after the FIRST j matrices are "collapsed". The layer-peel
# minAdm(M0,M1,M2,..) = min_t1 [(M0-t1)(M1-t1) + minAdm(t1,M2,..)] recurses: t1 = rank after collapsing (M0,M1).
# So t^1 = rank surviving the first pair, t^2 = rank surviving after the next, etc. With t^L=0.
# Hmm but t^L=0 forces the final rank to 0 -- that's the ACHIEVER center (product = 0, the deepest stratum).
#
# The chain Text is the rank sequence in the FACTORED chain (the resolution). For the achiever (product->0),
# the chain descends to rank 0 at the leaf. Let me check: does Text_k = t^k (Aoyagi) for the achiever?
# (2,2,2) Aoyagi achiever T=(1,0): t^1=1, t^2=0. So ranks: M0=2, then 1, then 0. Text=[2,1,0]?
# But the anchor RouteM222StructAdm used t222=(2,1,1) => Text=[2,2,1,1]. That's a DIFFERENT (non-achiever) path!
# CONFIRMS my certificate finding: t222=(2,1,1) is NOT the achiever; the achiever Text is [2,1,0].
# Let me compute the achiever Text for each anchor from its Aoyagi T*, via Text_k = t^k (t^0=M_0):
def achiever_text(M, T):
    # Text_0 = M_0, Text_k = t^k for k=1..L (t^L=0). T stores t^1..t^L at index 0..L-1.
    return [M[0]] + list(T)

for M,T in [((4,4,2,2),(4,2,0)),((3,3,4),(1,0)),((2,2,1),(1,0)),((2,2,1),(2,0)),((2,2,2),(1,0))]:
    Text=achiever_text(M,T)
    # per-boundary chain codim with this Text: r_k=Text_k-Text_{k+1}, c_k = Wext_k - Text_{k+1}=M_k - Text_{k+1}
    L=len(M)-1; codims=[]
    for k in range(L):
        r=Text[k]-Text[k+1]; c=M[k]-Text[k+1]
        codims.append(r*c)
    print(f"M={M}, Aoyagi T*={T} -> achiever Text={Text}, chain per-boundary codims={codims}, sum={sum(codims)}")
