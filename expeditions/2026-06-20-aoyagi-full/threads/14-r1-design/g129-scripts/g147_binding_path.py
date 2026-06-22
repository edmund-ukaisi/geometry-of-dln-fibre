import sympy as sp
# THE BINDING PATH to T* (the achiever path i₀ in RouteMTree terms), + Core realizability.
# T* = the minimising stratum (prefix ranks (t_1,...,t_L), t_L=0). The path reaching it: at each node,
# the C1/C2/C4/C5 pivot choice that resolves the active factor to the rank prescribed by T*.
print("=== The binding path to T* (RouteMTree pivot-choice sequence) ===\n")
print("""
For a minimising stratum T* = (t_1,…,t_L) (t_L=0), the binding path is the sequence of dispatcher
choices that resolve each factor to its T*-rank, ending at the binding divisor over T*:

(2,2,2), T* = (1,0):  M = (2,2,2), reduced-width core ‖A1·A2‖² (2×2 factors).
  node 0 (M=(2,2,2)): active factor C_1 (2×2), T* wants rank(C_1) = t_1 = 1 (a rank-1 DROP from 2).
    The product rank t_2 = rank(C_1 C_2) = 0. Since t_1=1 < 2 = M_0, this is a C1 coupled rank-defect
    (the rank-1 stratum). PIVOT CHOICE: blow up a 1×1 minor of C_1 (the pivot exposing rank 1).
    → core∘φ = x_p²·Q (the x_p² exceptional weight); Schur-descent → ‖S·A2red‖², M'=(1,1,2)... 
    Actually for the BINDING divisor: the rank-1 incidence stratum {rkA1≤1, rkA2≤1, A1A2=0} has codim
    Mval(T*)=3, and the binding branch resolves it in ONE codim-3 center blow-up (r1-design §2):
    (k,h)=(1, Mval−1)=(1,2), ratio 3/2. This is the DEPTH-2 branch (#134): the rank-1 stratum is NOT
    the generic (rank-2) one — it's reached after the first blow-up exposes the rank-1 locus.
  ⟹ achiever path i₀ = [pick the rank-1 pivot at node 0; its binding divisor j₀ has (k,h)=(1,2)].

GENERAL T* = (t_1,…,t_L): the binding path picks, at each node s, the pivot resolving C_s to rank t_s
(the T*-prescribed rank); the binding divisor over the full T* stratum has codim Mval(T*)=m₀, giving
(k,h)=(1, m₀−1), ratio m₀/2. ONE path suffices (S-min); it is the branch through T*'s binding center.
""")
print("=== Core.RankPattern / baseChange_normalForm realizability ===")
print("""
T* ∈ Adm M is REALIZABLE (the stratum is nonempty): the Gabriel normal form ⊕M^{m̄} realizes the rank
pattern whose prefix is T* (Core.OrbitKostant: RealizableRank = range rankFn; Orbit.baseChange_normalForm
builds the realizing tuple). The seam: prefix : RealizableRank M → Adm M (the first-row r_{1,j} of a
realizable full rank pattern is an admissible prefix tuple). So T* is hit by a realizing tuple, the
binding path's center {rank pattern = T*} is nonempty, and its codim = Mval(T*) = m₀ (thread-03).
⟹ the achiever path EXISTS (the minimising stratum is reached), with binding divisor (1, m₀−1).
This is precisely IsResolutionAtlas.achiever: ∃ i₀, monomialThreshold (d i₀)(k i₀)(h i₀) = ½·m₀.
""")
# verify the depth-2 point for (2,2,2): the minimiser is the rank-1 stratum, reached after the rank-2
# generic stratum is passed. Confirm rank-1 (codim 3) < rank-2 (codim 4):
def Mval222(t1): 
    # M=(2,2,2), T=(t1,0): Mval = (M0-t1)(M1-t1) + (t1-0)(M2-0) = (2-t1)² + t1·2
    return (2-t1)**2 + t1*2
print("(2,2,2) codim by rank: rank-0 Mval=", Mval222(0), " rank-1 Mval=", Mval222(1), " rank-2 Mval=", Mval222(2))
print("⟹ minimiser = rank-1 (codim 3), NOT generic rank-2 (codim 4) — depth-2 branch, genuine content (#134).")
