import sympy as sp, itertools
# Verify the VALUE ASSEMBLY logic precisely: ⨅_paths threshold = ½·min_t Mval, given the structure.
# Subtlety: a path's threshold = ½·(min codim of centers ALONG that path), NOT ½·Mval(its-leaf-stratum)
# necessarily. The leaf stratum is where the path ENDS (rank-0 leaf); the binding (min) codim is the
# SMALLEST center blown up along the path. The cleanest faithful statement:
#   For each path i: monomialThreshold_i = ½·c_i,  c_i = min codim of the centers on path i (an integer ≥ min_t Mval).
#   ⨅_i ½·c_i = ½·(min_i c_i).  Need min_i c_i = min_t Mval.
#   - (≤) some path has c_i = min_t Mval (the path through the TOP stratum's binding divisor): SURJECTIVITY
#         onto Adm reaches the min stratum, whose binding center has codim = min_t Mval.
#   - (≥) every path has c_i ≥ min_t Mval: every center is a stratum of Adm (admissibility), so its codim
#         = some Mval(T) ≥ min_t Mval. [k_E=1 ⟹ the center's RATIO = codim/2, no high-mult deflation.]
# So the assembly needs: (a) every CENTER's codim is an admissible Mval (≥ min), (b) the min stratum's
# binding center IS reached (surjectivity). This is cleaner than per-leaf codim_match.
print("=== Faithful value assembly (refined) ===")
# numeric sanity: the min over paths of (min codim along path) = min over all centers of codim = min_t Mval,
# PROVIDED every center is an admissible stratum (codim ∈ {Mval(T): T∈Adm}) and the min stratum is a center.
def admBound(M,j,L): return min(M[0],M[1]) if j==0 else M[j+1]
def adm_cone(M):
    L=len(M)-1; cone=[]
    for T in itertools.product(*[range(admBound(M,j,L)+1) for j in range(L)]):
        if all(T[j]<=T[i] for i in range(L) for j in range(L) if i<=j) and T[L-1]==0: cone.append(T)
    return cone,L
def Mval(M,T,L):
    tP=lambda j: M[0] if j==0 else T[j-1]
    return sum((tP(j)-T[j])*(M[j+1]-T[j]) for j in range(L))
for M in [(2,2,2),(3,3,3),(2,2,2,2)]:
    cone,L=adm_cone(M); vals=[Mval(M,T,L) for T in cone]
    print(f"  M={M}: codim set {{Mval(T)}} = {sorted(set(vals))}, min = {min(vals)} = min_t Mval.")
print("""
REFINED obligation (cleaner than per-leaf codim_match — state at the CENTER level):
  (S) every admissible stratum T∈Adm is a center of SOME path (reached) — surjectivity / exhaustiveness.
  (A) every CENTER blown up is an admissible stratum (codim = Mval(T), T∈Adm) — admissibility.
  (K) every exceptional divisor has k_E=1 (multilinearity) ⟹ its ratio = codim/2 (no undershoot).
  ⟹ ⨅_paths monomialThreshold = ½·(min codim over reached centers) = ½·min_{T∈Adm} Mval M T
                                = ofReal(lambdaCore M).
The structure I'll state bundles (S)+(A)+(K); (S) is the residual real work, (A)+(K) are structural/#131/#132.
""")
