import numpy as np
np.random.seed(21)
# CORRECT multi-drop GENERAL optimal v: product = B with rank r>0, AND interior drops ABOVE r.
# The fibre point v is optimal (product=B). For L2-at-v the SINGULAR core appears from the BOTTLENECK
# (interior layers forcing rank below the widths), the regular block from the smooth directions.
# Profile: t_0..t_5 with t_L = r (=rank B) > 0, and interior bottleneck. E.g. widths 4, r=1:
#   t = (4, 3, 2, 2, 1, 1) — drops at s=1(4→3),s=2(3→2),s=4(2→1), final rank t_5=1=r. Multi-drop, B rank 1.
W=4; L=5; r=1
tt=[4,3,2,2,1,1]   # t_0..t_5, final = r = 1
Cs=[]
for s in range(1,L+1):
    U=np.linalg.qr(np.random.randn(W,W))[0]; V=np.linalg.qr(np.random.randn(W,W))[0]
    D=np.diag([1.0]*tt[s]+[0.0]*(W-tt[s]))
    Cs.append(U@D@V)
P=np.eye(W); ranks=[]
for s in range(L):
    P=Cs[s]@P; ranks.append(np.linalg.matrix_rank(P,tol=1e-9))
B=P.copy()
print(f"GENERAL multi-drop optimal v: T_v target {tt[1:]}, achieved {ranks}, rank(B)={np.linalg.matrix_rank(B)}=r={r}")
print(f"  interior drops at s=1(4→3),s=2(3→2),s=4(2→1); final rank r=1>0 (a NON-deepest optimal v)")
print()
def dn(s):
    Pr=np.eye(W)
    for i in range(L-1,s,-1): Pr=Pr@Cs[i]
    return Pr
def up(s):
    Pr=np.eye(W)
    for i in range(s-1,-1,-1): Pr=Pr@Cs[i]
    return Pr
cols=[]
for s in range(L):
    for a in range(W):
        for b in range(W):
            E=np.zeros((W,W)); E[a,b]=1
            cols.append((dn(s)@E@up(s)).flatten())
M_dP=np.array(cols).T
rank_dP=np.linalg.matrix_rank(M_dP,tol=1e-7)
print(f"rank(dP) = {rank_dP} (regular block dim). For the rank-≤? determinantal tangent at B rank {r}:")
print(f"  r(M^1+M^L⁺¹)-r² = {r*(W+W)-r*r} (if product forced to rank r)")
print()
# THE SERIALIZATION: peel highest-rank-layer first. For EACH drop layer, the pivot = the up/downstream
# product sub-block on the surviving ranks. Check: are they UNITS at every drop SIMULTANEOUSLY? And do
# the drops couple (share pivot variables)?
drops=[(s,tt[s-1],tt[s]) for s in range(1,L+1) if tt[s-1]>tt[s]]
print("Drop layers (highest-rank-first), pivot sub-block ranks:")
for (s,a,b) in sorted(drops,key=lambda x:-x[1]):
    dns=dn(s-1); ups=up(s-1)
    rk_dn=np.linalg.matrix_rank(dns,tol=1e-9); rk_up=np.linalg.matrix_rank(ups,tol=1e-9)
    # the pivot for this drop = the (a-b) complement directions; pivot magnitude = singular values of
    # the relevant sub-block. Check the complement pivot is a UNIT (nonzero).
    print(f"  s={s}: {a}→{b} (complement rank {a-b}). downstream rank={rk_dn}, upstream rank={rk_up}")
print()
# CRITICAL: at a non-deepest v (final rank r=1>0), the downstream of the EARLY drops still has rank ≥ r
# (it doesn't collapse to 0). So the early-drop pivots see a nonzero downstream. Check the downstream
# of the highest drop (s=1) has rank ≥ r:
print(f"downstream of s=1 (the highest drop) rank = {np.linalg.matrix_rank(dn(0),tol=1e-9)} (≥ r={r}? the pivot survives)")
print(f"  ⟹ at a NON-deepest v the early-drop downstream is NONZERO (rank ≥ r), so the pivots are units.")
print(f"  This is the L2-at-v setting (B rank r>0). The deepest point (B=0) is D1's job, downstream.")
