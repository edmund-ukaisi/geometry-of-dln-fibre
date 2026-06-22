import sympy as sp, itertools
# Pin the branch↔admissible-rank-stratum BIJECTION as a precise statement. Verify the index-set
# correspondence + codim-matching on (2,2,2) and a deeper case, so the Lean statement is non-vacuous.
#
# The pivot-tree: at each level the recursion blows up the active factor's rank-defect; the BRANCH CHOICE
# at that level = the resolved rank of that factor. A root-to-leaf PATH = a tuple of per-level resolved
# ranks. CLAIM: paths ↔ Adm M (the admissible exponent cone T : Fin L → ℕ), and the path's min-codim
# along its center chain = Mval M T.
#
# Adm M for M=(2,2,2): T : Fin 2 → ℕ, admPred: T0 ≤ min(M0,M1)=2, T1 ≤ M2=2, weak-decrease T1≤T0,
#   last (j=L-1=1) T1 = 0. So T1=0, T0 ∈ {0,1,2}. Adm = {(0,0),(1,0),(2,0)}.
def admBound(M, j, L):
    return min(M[0], M[1]) if j==0 else M[j+1]
def adm_cone(M):
    L = len(M)-1
    cone=[]
    ranges=[range(admBound(M,j,L)+1) for j in range(L)]
    for T in itertools.product(*ranges):
        # admPred: weak decrease, last = 0, bound (already by ranges)
        if all(T[j] <= T[i] for i in range(L) for j in range(L) if i<=j) and (T[L-1]==0 if L>=1 else True):
            cone.append(T)
    return cone, L
def Mval(M,T,L):
    def tPrev(j): return M[0] if j==0 else T[j-1]
    return sum((tPrev(j)-T[j])*(M[j+1]-T[j]) for j in range(L))

for M in [(2,2,2),(2,1,2),(3,3,3),(2,2,2,2)]:
    cone,L = adm_cone(M)
    vals = {T: Mval(M,T,L) for T in cone}
    mn = min(vals.values())
    print(f"M={M}: |Adm|={len(cone)}, Mval per stratum:")
    for T in sorted(cone): print(f"    T={T}: Mval={vals[T]}{'  <-- MIN (codim of top stratum)' if vals[T]==mn else ''}")
    print(f"   min_t Mval = {mn}, lambdaCore = {sp.Rational(mn,2)} (½·min)")
    print()
