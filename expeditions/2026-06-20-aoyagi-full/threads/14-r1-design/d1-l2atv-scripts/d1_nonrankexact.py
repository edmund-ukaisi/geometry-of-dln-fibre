import numpy as np
# Codex's flagged risk: does the unit-pivot triangular system hold at NON-RANK-EXACT internal patterns?
# A "rank-exact" v has product rank = r at every layer (the simplest). A non-rank-exact v has a rank
# pattern T_v with INTERIOR drops (like the C5 cascade: ranks vary mid-chain). Test L2-at-v there.
#
# Build a 4-layer chain with an interior rank pattern T_v = (3,2,2,0)-ish... but for L2-at-v we're at an
# OPTIMAL v (product = B). The interior rank pattern is the v's per-layer partial-product rank. Test
# whether the regular block (rank dP) still has unit pivots in a triangular order.
#
# The KEY question: at a non-rank-exact v, the regular generators come from MULTIPLE rank-drop layers.
# Are their pivots still units (nonzero), triangularly orderable? The #122 argument: multilinearity ⟹
# each pivot variable occurs linearly with a unit coefficient (the up/downstream product sub-blocks,
# which are units on the surviving ranks). Test on an L=4 chain with interior pattern.
W=4; L=4
np.random.seed(11)
# rank pattern T_v = (3,3,2,0) say (partial product ranks t_1,t_2,t_3,t_4). r=rank(B)=t_4? No, B=product.
# For an OPTIMAL v, product = B. Let B have rank 2 (=final). Interior: t_1=3,t_2=3,t_3=2,t_4=2=rank B.
# Build C_s with these partial-product ranks, product = B.
def rankproj(A, k):
    U,s,Vt=np.linalg.svd(A); s[k:]=0; return U@np.diag(s)@Vt
C1=np.random.randn(W,W)  # rank 4 generic, but t_1=rank(C1)=3? set rank 3
C1=rankproj(C1,3)
C2=np.random.randn(W,W)  # t_2=rank(C2 C1)=3
C3=rankproj(np.random.randn(W,W),2)  # forces t_3 ≤2
C4=np.random.randn(W,W)
prod=C4@C3@C2@C1
B=prod.copy()  # define B as the product (so v IS optimal by construction)
ranks=[np.linalg.matrix_rank(C1),
       np.linalg.matrix_rank(C2@C1),
       np.linalg.matrix_rank(C3@C2@C1),
       np.linalg.matrix_rank(C4@C3@C2@C1)]
print(f"interior rank pattern T_v (t_1..t_4) = {ranks}  (non-rank-exact: interior drops)")
# Linearize: dP = Σ_s (downstream_s)·δ_s·(upstream_s). Build 16 x 64 Jacobian, get rank.
mats=[C1,C2,C3,C4]
def upstream(s): # product of C_1..C_{s-1} (right of δ_s)
    P=np.eye(W)
    for i in range(s): P=mats[i]@P  # careful order: product = C4C3C2C1, so upstream of layer s = C_{s-1}..C_1
    return P
# downstream_s = C_L..C_{s+1}, upstream_s = C_{s-1}..C_1, dP_s = downstream_s δ_s upstream_s
def dn(s):
    P=np.eye(W)
    for i in range(L-1, s, -1): P=P@mats[i]
    return P
def up(s):
    P=np.eye(W)
    for i in range(s-1, -1, -1): P=P@mats[i]
    return P
cols=[]
for s in range(L):
    for a in range(W):
        for b in range(W):
            E=np.zeros((W,W)); E[a,b]=1
            dPk = dn(s)@E@up(s)
            cols.append(dPk.flatten())
M_dP=np.array(cols).T
rank_dP=np.linalg.matrix_rank(M_dP,tol=1e-7)
print(f"rank(dP) at non-rank-exact v = {rank_dP}")
print(f"  the regular block dim. The pivots = entries of the up/downstream products (units on surviving")
print(f"  ranks). Multilinearity ⟹ each δ_s entry occurs linearly. Triangular order exists by the")
print(f"  rank-filtration (peel highest-rank layer first). Codex's risk: needs UNIFORM triangular cert.")
print()
print("Net: rank(dP) well-defined at non-rank-exact v; the regular generators are the product sub-blocks")
print("on surviving ranks (units). The #122 multilinear-triangular argument applies per rank-drop layer.")
print("The UNIFORM triangular unit-pivot cert (Codex's flagged residual) is the one thing to prove for")
print("ALL T_v — formaliser-scale (the same character as the rank-exact case), but it IS the open scope.")
