# Count the ACTUAL radial active normals from the banked leafH + the chart structure.
# 222: leafH222 = {0:2, 4:1} -> radial pivot x0 (exp 2 = minAdm-1=2), spectator x4 (exp 1). 
#   The radial blow-up pb222 = pivotBlowupOn {0,6,7} 0 -> active = {0,6,7}, card 3 = minAdm. 
#   So the ACTIVE set is {pivot=0, 6, 7} (NOT including x4 which is a SEPARATE bsubst factor).
#   x6 = Rmat1 E-block; x7 = Rfin2(0,1). pivot x0 scales the FIXED-1 at Rfin2(0,0). active.card=3=minAdm. ✓
# 3333: pb3333 active.card = 6 (minAdm). leafH3333 = {0:5,1:4,4:2,9:3}. radial pivot x0 (exp 5=minAdm-1).
#   The radial active = the 6 residual normals. Let me identify them from B_det3333:
#   - Rmat1 = e_{22}: the FIXED 1 at (2,2) = the PIVOT slot (x0 scales it). 1 slot (the pivot).
#   - Rmat2 = !![0,0,0;0,x13,x14]: E-block 1x2 = x13,x14. 2 active.
#   - Rfin3 = !![x24,x25,x26]: 1x3 = 3 active.
#   pivot(1) + x13,x14(2) + x24,x25,x26(3) = 6 = minAdm. ✓✓
# So the ACTIVE set = {the fixed-1 pivot slot} ∪ {interior E-blocks Rmat_k} ∪ {leaf Rfin_L}, total = minAdm.
# The fixed-1 pivot is ONE of the interior E-block slots (3333: Rmat1 E(2,2)) OR the leaf (222: Rfin2(0,0)).
#
# So the COUNT: minAdm = (# interior E-block entries) + (# leaf Rfin entries), where ONE of them is the fixed-1 pivot.
# Let me recount with the RIGHT per-boundary E-block dims:
#  interior boundary k (1..L-1): E-block r_k x c_k, r_k = Text(k)-Text(k+1), c_k = Wext(k)-Text(k+1).
#  leaf: Rfin_L = Text(L) x Wext(L).
# 222: interior k=1: r=Text1-Text2=2-1=1, c=Wext1-Text2=2-1=1 -> 1. leaf: Text2*Wext2=1*2=2. tot=1+2=3=minAdm ✓
# 3333: k=1: r=Text1-Text2=3-2=1,c=Wext1-Text2=3-2=1->1. k=2: r=Text2-Text3=2-1=1,c=Wext2-Text3=3-1=2->2.
#   leaf: Text3*Wext3=1*3=3. tot=1+2+3=6=minAdm ✓✓✓
# So my earlier formula was RIGHT for 222/3333. Let me recheck 4422/334 — they are NOT chain anchors (pure radial),
# so their tach is different. Let me just confirm 222/3333 (the chain anchors) and re-derive the CORRECT tach for 334.
def count(M, tach):
    L=len(M)-1
    Text=[M[0]]+[tach[k] for k in range(L)]
    Wext=list(M)
    interior=sum((Text[k]-Text[k+1])*(Wext[k]-Text[k+1]) for k in range(1,L))
    leaf=Text[L]*Wext[L]
    return interior+leaf, Text, interior, leaf
import functools
@functools.lru_cache(None)
def minAdmRec(M):
    M=tuple(M); n=len(M)
    if n==1: return 0
    if n==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdmRec((t,)+M[2:]) for t in range(0,min(M[0],M[1])+1))
for M,tach in [((2,2,2),(2,1,0)),((3,3,3,3),(3,2,1,0)),((2,2,1),(2,1,0))]:
    tot,Text,i,l=count(M,tach)
    print(f"M={M} tach={tach}: active=interior({i})+leaf({l})={tot}, minAdm={minAdmRec(M)}, MATCH={tot==minAdmRec(M)}")
