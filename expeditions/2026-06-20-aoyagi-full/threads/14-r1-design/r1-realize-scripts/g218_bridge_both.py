import numpy as np
from itertools import product
# Complete the bridge: Adm M = RealizableRank M (both directions, structural).
# DIRECTION 1 (Adm ⊆ Realizable): every admissible T realized by the canonical diagonal cascade (g217 ✓).
# DIRECTION 2 (Realizable ⊆ Adm): every rank vector ACHIEVED by a tuple is admissible.
def admissible(M,t):
    L=len(M)-1; tt=[M[0]]+list(t)
    if tt[-1]!=0: return False
    for j in range(1,L+1):
        if not(0<=tt[j]<=tt[j-1]): return False
        if tt[j]>M[j]: return False
    return True
print("DIRECTION 2 (Realizable ⊆ Adm): every achieved rank vector is admissible. STRUCTURAL:")
print("  t_j = rank(C_1···C_j). (a) rank(C_1···C_j) ≤ rank(C_1···C_{j-1}) [appending a factor can't raise")
print("  rank] ⟹ weakly-decreasing. (b) rank(C_1···C_j) ≤ rank(C_j) ≤ min(M^j, M^{j+1}) ≤ M^{j+1} ⟹ t_j ≤ M^{j+1}.")
print("  (c) t_j ≤ t_{j-1} (from a). So any achieved T satisfies Adm's inequalities ⟹ Realizable ⊆ Adm. ✓")
print("  (On {∏=0}: t_L=0, the fibre constraint — built into both.)")
print()
# RANDOMIZED converse check: random tuples, achieved rank vector always admissible?
np.random.seed(7); bad=0; n=0
for _ in range(200):
    L=np.random.randint(2,5); M=[np.random.randint(1,4) for _ in range(L+1)]
    Cs=[np.random.randn(M[s],M[s+1]) for s in range(L)]
    # force product to 0? No — test general achieved ranks are weakly-decr + bottlenecked (the non-fibre Adm).
    P=np.eye(M[0]); t=[]
    for s in range(L): P=P@Cs[s]; t.append(int(round(np.linalg.matrix_rank(P,tol=1e-9))))
    # check weakly-decreasing + t_j ≤ M^{j+1} (the Adm inequalities sans the t_L=0 fibre constraint)
    tt=[M[0]]+t; ok=all(0<=tt[j]<=tt[j-1] and tt[j]<=M[j] for j in range(1,L+1))
    n+=1
    if not ok: bad+=1
print(f"DIRECTION 2 randomized: {n} random tuples, achieved rank vectors violating Adm inequalities: {bad} (0 ⟹ Realizable ⊆ Adm ✓)")
print()
print("="*68)
print("THE BRIDGE SEED (Adm M = RealizableRank M, structural — the §4 reachability seed for fm3):")
print("="*68)
print("Adm M (Lambda, the exponent cone) = RealizableRank M (Core, Set.range rankFn) on the chain, BOTH dirs:")
print(" (⊆) every admissible T realized by the canonical diagonal cascade C_s=diag(1^{t_{s+1}},0): the")
print("     admissibility t_{s+1}≤min(t_s,M^{s+1}) is EXACTLY when the cascade achieves t_{s+1} (g217: all")
print("     admissible T realized, 5 cases). STRUCTURAL: the diagonal cascade with t_{s+1} ones has running")
print("     partial-product rank = t_{s+1}, valid iff t_{s+1}≤min(t_s,M^{s+1}) = admissibility.")
print(" (⊇) every achieved rank vector is admissible: rank(C_1···C_j) is weakly-decreasing (appending a")
print("     factor can't raise rank) + ≤ M^{j+1} (bottleneck) = the Adm inequalities (g218: 200 random, 0 viol).")
print()
print("⟹ the achiever T* (Lambda's Mval-minimiser, T*∈Adm) is ALWAYS in RealizableRank (realized by its")
print("   cascade) ⟹ §4 reachability holds: the chart path resolving each layer to t*_s (the cascade ranks)")
print("   reaches T*. The Adm↔RealizableRank bridge = this two-direction rank-cascade ↔ admissibility-cone")
print("   equivalence. For Lean: the (⊆) cascade construction is the constructive realizer (rankFn(cascade)=T);")
print("   the (⊇) is rank-mono + bottleneck. NOT stratum_surjective (full) — just T*∈Realizable (the achiever).")
