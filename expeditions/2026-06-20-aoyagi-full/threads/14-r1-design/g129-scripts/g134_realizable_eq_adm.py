import sympy as sp, itertools
# KEY: is every admissible prefix-rank tuple t ∈ Adm M REALIZABLE (some tuple has those partial ranks)?
# If an admissible t were NOT realizable, S(t) would be empty and surjectivity would be vacuous/ill-posed
# for it. Conversely if a realizable prefix-rank tuple were NOT in Adm, the atlas would have a stratum
# outside the value cone (a soundness worry). Need: {realizable prefix-rank tuples with product rank 0}
# = Adm M exactly. Check by direct construction + the rank-pattern constraints.
#
# Realizability of a prefix-rank tuple t=(t_1,...,t_L), t_j = rank(C¹···Cʲ): the constraints are
#   (monotone) t_j ≤ t_{j-1}  (rank of a longer product ≤ shorter — adding a factor can't raise rank)
#       actually rank(C¹···Cʲ) ≤ rank(C¹···C^{j-1}) AND ≤ rank(Cʲ); the partial product rank is
#       non-increasing in j IF we extend on the right... rank(AB) ≤ min(rank A, rank B). So t_j ≤ t_{j-1}.
#   (block bound) t_j ≤ M_{j+1} (the product C¹···Cʲ has ≤ M_{j+1} columns) and ≤ M_0 (rows). And the
#       admBound: t_1 ≤ min(M_0,M_1).
#   (deepest) t_L = 0 (product is 0 at the deepest core point).
# These are EXACTLY admPred (weak-decrease + last=0 + admBound). So Adm M = {admissible prefix-rank tuples}.
# Realizability: given such a t, build C_j to achieve it (the nested-rank normal form). 
def admBound(M,j,L): return min(M[0],M[1]) if j==0 else M[j+1]
def adm_cone(M):
    L=len(M)-1; cone=[]
    for T in itertools.product(*[range(admBound(M,j,L)+1) for j in range(L)]):
        if all(T[j]<=T[i] for i in range(L) for j in range(L) if i<=j) and T[L-1]==0: cone.append(T)
    return cone,L
def realize_chain(M,t):
    # build factors C_1..C_L (C_j : M_{j-1} x M_j ... careful with indexing: C_j shape M_j x M_{j+1}? )
    # Use: factor s connects layer s -> s+1, shape M_s x M_{s+1}. Partial product P_j = C_1...C_j has
    # shape M_0 x M_{j+1}... NO. Standard DLN: prod = C_L ... C_1, C_s : M_s x M_{s+1}. Let me just build
    # diagonal rank-t factors: C_s = diag with t_{s} ones (in the achievable nested pattern) and check ranks.
    L=len(M)-1
    facs=[]
    for s in range(L):
        # C_s : M_s x M_{s+1}, set rank so partial products hit t. Use a "staircase": C_s has 1's on
        # diagonal up to the needed rank. The partial product rank = min of the staircase heights.
        Cs = sp.zeros(M[s], M[s+1])
        # target rank for this factor so that cumulative min gives t: set factor-s rank = t_s' generously
        rk = t[s] if s < L else 0
        # we want rank(C_1...C_s) = t_s; achieve with C_s = I_{rk} block (and pad)
        for i in range(min(rk, M[s], M[s+1])): Cs[i,i]=1
        facs.append(Cs)
    # partial products P_j = C_1 * C_2 * ... (left to right) — but DLN prod is C_L...C_1; for RANK pattern
    # the order convention doesn't change realizability. Compute cumulative product ranks:
    P=facs[0]; ranks=[P.rank()]
    for s in range(1,L):
        P=P*facs[s]; ranks.append(P.rank())
    return ranks
for M in [(2,2,2),(3,3,3),(2,2,2,2)]:
    cone,L=adm_cone(M)
    print(f"M={M}: checking every t∈Adm is realized by the staircase normal form:")
    allok=True
    for t in sorted(cone):
        r=realize_chain(M,t)
        ok = tuple(r)==tuple(t)
        allok = allok and ok
        if not ok: print(f"    t={t}: realized partial ranks {r}  MISMATCH")
    print(f"    all {len(cone)} strata realized exactly: {allok}")
