# Re-examine: for (3,3,4) and (4,4,2,2), did the chain E-block sum match minAdm? Let me compute with
# achiever Text = [M0] + list(Aoyagi T*) and BOTH width conventions.
def chain_Eblocks(M, Text):  # cols use M_s (BEFORE)
    L=len(M)-1
    return [(Text[s]-Text[s+1], M[s]-Text[s+1]) for s in range(L)]
def aoyagi_blocks(M,T):  # cols use M_{j+1} (AFTER)
    L=len(T)
    return [((M[0] if j==0 else T[j-1])-T[j], M[j+1]-T[j]) for j in range(L)]

for M,T in [((4,4,2,2),(4,2,0)),((3,3,4),(1,0)),((2,2,1),(1,0)),((2,2,2),(1,0))]:
    Text=[M[0]]+list(T)
    ce=chain_Eblocks(M,Text); ca=aoyagi_blocks(M,T)
    ces=sum(r*c for r,c in ce); cas=sum(r*c for r,c in ca)
    print(f"M={M} T*={T} Text={Text}")
    print(f"   chain E-blocks (cols=M_s BEFORE): {ce} sum={ces}")
    print(f"   Aoyagi blocks  (cols=M_j+1 AFTER): {ca} sum={cas}  minAdm={cas}  MATCH chain? {ces==cas}")
