import numpy as np, scipy.linalg as sla
np.random.seed(50)
# OVER-VERIFY: non-transversal suffix/prefix flags. The Ferrers structure im(dP)=Σ Im(suffix)⊗Row(prefix)
# assumed the suffix images and prefix row-spaces are in GENERAL POSITION. A non-transversal v has them
# OVERLAPPING (a coincidental alignment) ⟹ the rectangles could degenerate / overlap ⟹ rank(dP) might
# DROP below nReg, OR the unit-pivot peel might fail.
#
# Construct a non-transversal v: make the downstream image and upstream row-space SHARE a direction
# (forced alignment). E.g. CONJUGATE layers so Im(downstream) ∩ Row(upstream) is larger than generic.
#
# Concrete: a chain where the SAME subspace is the survivor at multiple layers (aligned, not generic).
# Use the cascade itself C_s=diag(1^{t_s},0) — this is MAXIMALLY aligned (all survivors = the SAME
# top-coords). The cascade is the MOST non-transversal point (all flags aligned to the standard flag)!
W=5; L=5; r=1
tt=[5,4,3,2,1,1]
# cascade (maximally aligned flags): C_s = diag(1^{t_s}, 0), all survivors = top coords.
Cs=[np.diag([1.0]*tt[s]+[0.0]*(W-tt[s])) for s in range(1,L+1)]
P=np.eye(W); ranks=[]
for s in range(L):
    P=Cs[s]@P; ranks.append(np.linalg.matrix_rank(P,tol=1e-9))
print(f"MAXIMALLY-ALIGNED v (the cascade itself, all flags = standard flag): ranks {ranks}, rank(B)={np.linalg.matrix_rank(P)}")
print(f"  This is the MOST non-transversal point — every layer's survivor = the SAME top coords.")
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
nReg=r*(W+W)-r*r
print(f"rank(dP) at the aligned cascade = {rank_dP}, nReg={nReg}, match={rank_dP==nReg}")
print()
# CRITICAL: at the cascade (B rank 1, the deepest of THIS rank pattern), is rank(dP) still nReg, or does
# the alignment DROP it? If it drops, the regular block is SMALLER than nReg at non-transversal v —
# meaning the split peels FEWER regular dirs, and MORE go to the core. That's not a FAILURE (the core
# just gets bigger), but it changes nReg-at-v. The L2-at-v split must use rank(dP) AT v, not the formula.
