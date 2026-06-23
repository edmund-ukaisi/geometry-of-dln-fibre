import numpy as np
np.random.seed(20)
# Build a DEEP MULTI-DROP optimal v: a chain with MULTIPLE simultaneous interior rank drops.
# rank pattern T_v = (t_1,...,t_L), t_s = rank(C_s...C_1). Multi-drop = several layers each dropping.
# Take T_v = (4,2,2,1,0): drops at layer 1 (4→2, wait t_0=M^1). Let me set widths and a clean profile.
# Use L=5, widths M=(4,4,4,4,4,4) (M^1..M^6), t_0=M^1=4. Profile t_0..t_5 = 4,2,2,1,1,0:
#   drop at s=1 (4→2, rank drop 2), s=3 (2→1, drop 1), s=5 (1→0, drop 1). THREE drops, one big.
# Actually want SIMULTANEOUS = multiple layers dropping in the chain (which is the generic multi-drop).
W=4; L=5
tt = [4,2,2,1,1,0]   # t_0..t_5; drops at s=1(4→2),s=3(2→1),s=5(1→0)
# Build C_s with rank(C_s...C_1)=t_s, product = B. Cascade-style: C_s = rank-t_s projector composed.
def rankproj(A,k):
    U,s,Vt=np.linalg.svd(A); s[k:]=0; return U@np.diag(s)@Vt
Cs=[]
for s in range(1,L+1):
    A=np.random.randn(W,W)
    Cs.append(A)
# enforce running ranks t_s by making each C_s drop to t_s when composed. Easiest: build the product
# rank profile by SVD-truncating the running product.
# Construct cascade: C_s diagonal-ish that forces running rank t_s. Use C_s = U_s diag(1^{t_s},0) V_s.
Cs=[]
for s in range(1,L+1):
    U=np.linalg.qr(np.random.randn(W,W))[0]; V=np.linalg.qr(np.random.randn(W,W))[0]
    D=np.diag([1.0]*tt[s]+[0.0]*(W-tt[s]))
    Cs.append(U@D@V)
# running ranks:
P=np.eye(W); ranks=[]
for s in range(L):
    P=Cs[s]@P; ranks.append(np.linalg.matrix_rank(P,tol=1e-9))
B=P.copy()
print(f"multi-drop v: target T_v (t_1..t_5) = {tt[1:]}, achieved running ranks = {ranks}")
print(f"  (drops at the layers where rank decreases; B=product, rank {np.linalg.matrix_rank(B)})")
print()
# Linearize: dP(δ) = Σ_s downstream_s · δ_s · upstream_s. Build the Jacobian (W² x L·W²), get rank.
def dn(s):  # C_L...C_{s+1}, 0-indexed s
    Pr=np.eye(W)
    for i in range(L-1,s,-1): Pr=Pr@Cs[i]
    return Pr
def up(s):  # C_{s-1}...C_1
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
print(f"rank(dP) = {rank_dP}  (the regular block dim at this multi-drop v)")
print()
# THE SERIALIZATION TEST: "peel highest-rank-layer first". The drops are at layers with t_{s-1}>t_s.
# Order by the rank BEFORE the drop (highest first). For each drop layer, its regular generators are
# the entries of (downstream)·δ_s·(upstream) restricted to the surviving-rank sub-block. The pivot =
# the up/downstream product sub-block on the surviving ranks. Check these pivots are UNITS at each drop.
drops=[(s, ranks_prev, ranks[s] if s<L else 0) for s,(ranks_prev) in enumerate([tt[s] for s in range(L)])]
# recompute drops cleanly:
drops=[]
for s in range(1,L+1):
    if tt[s-1]>tt[s]: drops.append((s, tt[s-1], tt[s]))
print("Drop layers (s, from, to), highest-rank-first order:")
for (s,a,b) in sorted(drops, key=lambda x:-x[1]):
    # the pivot sub-block: downstream (on the surviving t_s ranks) and upstream (on the incoming t_{s-1})
    dns=dn(s-1); ups=up(s-1)  # 0-indexed layer s-1
    # the surviving-rank pivot = the rank of dn restricted to image, up restricted to coimage
    rk_dn=np.linalg.matrix_rank(dns,tol=1e-9); rk_up=np.linalg.matrix_rank(ups,tol=1e-9)
    print(f"  s={s}: {a}→{b}. downstream rank={rk_dn}, upstream rank={rk_up} (pivots on surviving ranks)")
print()
print(f"Total rank dropped along path = Σ(t_{{s-1}}-t_s) = {sum(a-b for s,a,b in drops)}")
print(f"  (= node count under iterated rank-1; rank(dP)={rank_dP} = the regular block from these drops)")
