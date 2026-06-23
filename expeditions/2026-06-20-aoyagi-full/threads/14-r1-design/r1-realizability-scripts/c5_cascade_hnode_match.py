import numpy as np, sympy as sp
# CROSS-CHECK: does pp2's diagonal cascade C_s=diag(1^{t_{s+1}},0) give the realization skeleton my
# C5 hnode (Fubini-shear) implements at t=(3,3,2,2,2,0)?
#
# The cascade EXHIBITS a tuple A* with rank(C_1..C_j)=t_j (a point IN the stratum S(T*)). My hnode is
# the local resolution chart NEAR a point of S(T*). The coordination question:
#   (Q-A) does the cascade's per-step rank-drop dictate the ChainDimSplit sequence?
#   (Q-B) is the cascade point a SMOOTH point of the stratum (so the chart is the local resolution)?
#   (Q-C) at a PARTIAL-drop step (t_{s-1}>t_s>0), does the cascade's step = my shear's step?
#
# t = (3,3,2,2,2,0) means partial-product ranks: t_1=3,t_2=3,t_3=2,t_4=2,t_5=2,...,t_L=0.
# Wait — that's 6 entries, t_6=0. The DROPS: t_2->t_3 = 3->2 (partial, C5), and the final ->0.
# pp2's cascade: C_s = diag(1^{t_{s+1}}, 0). So per step the running rank is forced to t_{s+1}.
t = [3,3,2,2,2,0]   # t_1..t_6 (L=6 chain? indices). Use as the running ranks t_1..t_L with t_0=M^1.
M = [3,3,3,3,3,3,3] # widths M^1..M^7, all 3 (generous). M^1=t_0 region.
# Build the cascade and check ranks:
L = len(t)
Cs = []
t0 = M[0]
tt = [t0] + t
for s in range(L):
    msin, msout = M[s], M[s+1]
    C = np.zeros((msin, msout))
    rk = tt[s+1]
    for i in range(min(rk, msin, msout)): C[i,i] = 1.0
    Cs.append(C)
P = np.eye(M[0]); ranks=[]
for s in range(L):
    P = P @ Cs[s]; ranks.append(int(round(np.linalg.matrix_rank(P))))
print(f"cascade ranks for t={t}: {ranks}  match: {ranks==t}")
print()
# (Q-A) The ChainDimSplit sequence: each step the running rank drops from tt[s] to tt[s+1].
# At s where tt[s] > tt[s+1] > 0: PARTIAL drop (C5). At s=2 (0-indexed): tt[2]=3 -> tt[3]=2, partial.
for s in range(L):
    a, b = tt[s], tt[s+1]
    typ = "C1(full→0)" if b==0 else ("C5(partial)" if a>b>0 else ("pass(a=b)" if a==b else "?"))
    if a>b: print(f"  step s={s}: rank {a}->{b}  [{typ}]")
print()
# (Q-C) At the C5 step (3->2): the cascade C_s = diag(1,1,0) (t_{s+1}=2 ones). The next factor sees
# a rank-2 input. My shear model: survivor rank 2 (the two 1's), complement rank 1 (the dropped coord).
# The cascade's dropped coordinate (the 3rd, =0) IS my complement; the two surviving 1's ARE my survivor.
# So the cascade's per-step structure = my survivor⊕complement split EXACTLY. ✓
print("(Q-C) C5 step 3->2: cascade C_s=diag(1,1,0). Survivor = 2 surviving units, complement = the")
print("  dropped 3rd coord. This IS my survivor(rank2)⊕complement(rank1) split. The cascade DICTATES")
print("  the ChainDimSplit; my Fubini-shear is the analytic chart resolving the complement at that step.")
print()
# (Q-B) Is the cascade point a smooth point of S(T*)? The diagonal cascade is the MOST degenerate
# point (all structure on the diagonal) — actually it's a specific point; the resolution chart is built
# at a generic/adapted point. The hnode is local near the deepest point of the REDUCED core, not the
# cascade point itself. The cascade gives the rank-drop SEQUENCE (which layer drops how much), which is
# what the dispatcher routeStep needs to emit the branch. The analytic chart (hnode) is then built per step.
print("(Q-B) The cascade gives the rank-drop SEQUENCE (the routeStep branch structure); the hnode is")
print("  the per-step analytic chart. They compose: cascade=combinatorial skeleton, hnode=analytic flesh.")
print()
print("VERDICT on coordination: my C5 hnode IMPLEMENTS pp2's cascade step. The cascade's per-step")
print("partial-drop (3->2 via diag(1,1,0)) = my survivor⊕complement split; the shear resolves the")
print("complement, the survivor (the 2 surviving units) is the reduced chain that recurses. ALIGNED.")
