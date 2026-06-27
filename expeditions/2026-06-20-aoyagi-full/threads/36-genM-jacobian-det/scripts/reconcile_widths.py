# CRITICAL: do the chain E-block dims (r_k x c_k = (Text_k - Text_{k+1}) x (Wext_k - Text_{k+1})) match the
# Aoyagi rBlock x cBlock = (tPrev_j - tStar_j) x (M_{j+1} - tStar_j)?
# Chain: tach(k+1)=tStar(k) so Text(k+1)=tStar(k), Text(0)=M0, Text(k)=tStar(k-1) for k>=1.
# Aoyagi index j (Fin L, 0-indexed): rBlock_j = tPrev_j - tStar_j, cBlock_j = M_{j+1} - tStar_j.
#   tPrev_j = M0 if j=0 else tStar_{j-1}.
# Chain boundary k (1-indexed interior 1..L-1 + leaf L). Let me line up chain boundary k with Aoyagi j.
# The E-block at chain boundary k (interior): rows = Text(k)-Text(k+1), cols = Wext(k)-Text(k+1) = M_k - Text(k+1).
#   Text(k) = tStar(k-1) [for k>=1], Text(k+1) = tStar(k). So rows = tStar(k-1) - tStar(k).
#   cols = M_k - tStar(k).
# Aoyagi j: rBlock_j = tPrev_j - tStar_j. For j>=1: tPrev_j = tStar_{j-1}, so rBlock_j = tStar_{j-1}-tStar_j.
#   cBlock_j = M_{j+1} - tStar_j.
# Match chain k <-> Aoyagi j: chain rows (tStar(k-1)-tStar(k)) = Aoyagi rBlock_j (tStar_{j-1}-tStar_j) needs k=j.
#   chain cols (M_k - tStar(k)) vs Aoyagi cBlock_j=k (M_{k+1} - tStar_k). M_k vs M_{k+1}: OFF BY ONE in width!
# So chain E-block at boundary k has cols M_k - tStar(k), Aoyagi cBlock_k has cols M_{k+1} - tStar(k). DIFFERENT.
#
# Let me just COUNT both for the anchors and see which the ACTUAL B_det uses.
import functools
@functools.lru_cache(None)
def minAdmRec(M):
    M=tuple(M); n=len(M)
    if n==1: return 0
    if n==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdmRec((t,)+M[2:]) for t in range(0,min(M[0],M[1])+1))

def aoyagi_blocks(M, tStar):  # tStar: Fin L (Aoyagi), tStar[j] = t^{j+1}
    L=len(tStar)
    out=[]
    for j in range(L):
        tprev = M[0] if j==0 else tStar[j-1]
        r=tprev-tStar[j]; c=M[j+1]-tStar[j]
        out.append((r,c,r*c))
    return out
def chain_Eblocks(M, tach):  # tach: Fin(L+1), tach[k]=Text(k+1)
    L=len(M)-1
    Text=[M[0]]+[tach[k] for k in range(L)]; Wext=list(M)
    # interior boundaries k=1..L-1 + leaf k=L. E-block at interior k: rows Text(k)-Text(k+1), cols Wext(k)-Text(k+1)
    blocks=[]
    for k in range(1,L):
        r=Text[k]-Text[k+1]; c=Wext[k]-Text[k+1]
        blocks.append(('int',k,r,c,r*c))
    # leaf
    blocks.append(('leaf',L,Text[L],Wext[L],Text[L]*Wext[L]))
    return blocks

# 222: tStar (Aoyagi) = (1,0) [t^1=1,t^2=0]; tach=(2,1,0)
for M,tStar,tach in [((2,2,2),(1,0),(2,1,0)),((3,3,3,3),(2,1,0),(3,2,1,0)),((2,2,1),(1,0),(2,1,0)),((3,3,4),(1,0),(3,1,0))]:
    ab=aoyagi_blocks(M,tStar); cb=chain_Eblocks(M,tach)
    print(f"M={M}: Aoyagi blocks(r,c,rc)={ab} sum={sum(b[2] for b in ab)} minAdm={minAdmRec(M)}")
    print(f"        chain E-blocks={cb} sum={sum(b[4] for b in cb)}")
