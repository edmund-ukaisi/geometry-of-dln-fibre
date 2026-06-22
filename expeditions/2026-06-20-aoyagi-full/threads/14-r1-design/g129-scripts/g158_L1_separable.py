import sympy as sp
# THE CRITICAL CLAIM: is "deepest = min-core" (the rlctAtOn_mono input |dlnLoss near deepest| ≤
# |dlnLoss near v|) PROVEN L1-separable, or does it need the resolution value / Aoyagi Thm 2 citation?
# Be ADVERSARIAL (confirm don't assert) — a wrong "L1-separable" hides a 2nd-citation problem.
#
# First: what does rlctAtOn_mono ACTUALLY need? rlctAtOn_mono (F G wstar) (|G|≤|F| near wstar, G=0⟹F=0)
# ⟹ rlctAtOn G ≤ rlctAtOn F. For D1 (a) = rlctAt(deepest) ≤ rlctAt(v):
#   set F = dlnLoss near v (basepoint v), G = dlnLoss near deepest (basepoint deepest). Need |G|≤|F|...
# BUT F,G are at DIFFERENT basepoints — rlctAtOn_mono compares two functions at ONE point. So we CANNOT
# directly mono across two basepoints. This is EXACTLY the docstring's gap ("rlctAt_mono compares two
# functions at ONE point; here SAME loss at TWO points"). So the raw-mono route ALSO needs a bridge.
print("=== ADVERSARIAL: the raw-mono route ALSO can't compare two basepoints directly ===")
print("""
rlctAtOn_mono compares two FUNCTIONS at ONE basepoint. D1 (a) is the SAME function (dlnLoss H B) at TWO
basepoints (deepest vs v). So neither 'chart v' NOR 'raw-mono' directly gives D1 (a) — BOTH need a
bridge from the two points to a common comparison. The docstring flags exactly this.

THE BRIDGE (the only sound route, value-independent question): bring BOTH points to a common normal
form where the comparison is a single-basepoint mono. The deepest point's loss, in its gauge chart
(#44 sub-3), is ∑E² + dlnLoss M 0 (the FULL homogeneous core at 0). A general v's loss, in ITS chart
(non-rank-exact, broader split), is ∑E'² + (a LESS-degenerate core at 0). The comparison is then at the
COMMON basepoint 0 (both charts map their point to 0), and we need: the deepest core ≤ the v core there.
So we're BACK to needing v's chart (the non-rank-exact one crux2 flags) OR a value-independent argument
that the deepest core is the min over the strata.
""")
# So the HONEST question: is "deepest core = min over optimalSet strata" provable from block_elimination
# (L1) + the deepest structure, value-independently? The deepest core is the rank-exact stratum's core
# (most degenerate). A general v's core is a higher-rank stratum's core. Is deepest-core ≤ v-core?
# block_elimination gives: at ANY v, P_s(v s)Q_s = blockdiag[I_{s_s}, 0], s_s = rank(v s) ≥ r. The core
# at v = the residual after the rank-s_s regular block. The DEEPEST has s_s = r (smallest regular block,
# largest residual core). Larger residual = more vanishing = smaller rlct. So deepest ≤ v IF "smaller
# regular block ⟹ larger/more-degenerate core ⟹ smaller rlct". Is THAT value-independent (L1)?
print("=== Is deepest-core ≤ v-core L1-separable (block_elimination + rank monotonicity)? ===")
print("""
At v, block_elimination: rank(v s) = s_s ≥ r, regular block I_{s_s} (size s_s), residual core on the
(H_s − s_s) reduced block. DEEPEST: s_s = r (minimal), residual on (H_s − r) (MAXIMAL reduced block).
General v: s_s ≥ r, residual on (H_s − s_s) ≤ (H_s − r) (SMALLER reduced block).
⟹ the deepest residual core lives on a LARGER reduced block (more singular directions) than v's.
CLAIM (the L1-separable content): the deepest core (on the larger reduced block) DOMINATES v's core
(on the smaller block) in the rlctAtOn_mono sense ⟹ rlctAt(deepest) ≤ rlctAt(v).
ADVERSARIAL CHECK: is this a clean pointwise domination, or does it need the resolution VALUE (which
core has smaller rlct)? The reduced cores are dlnLoss M 0 on DIFFERENT M (M_deepest = H−r ⊇ M_v = H−s_s
as reduced widths). rlctAt(dlnLoss M 0) is MONOTONE in M? i.e. larger reduced widths ⟹ smaller rlct?
""")
# Test: is rlctAtOn(dlnLoss M 0) 0 monotone decreasing in M (larger M = smaller rlct)?
# M=(1,1,1): core=(c1 c2)², rlct=1/2.  M=(2,2,2): rlct=lambdaCore=3/2... WAIT that's LARGER M, LARGER rlct!
def lc(M):
    # lambdaCore via min Mval — compute
    import itertools
    def admB(M,j,L): return min(M[0],M[1]) if j==0 else M[j+1]
    L=len(M)-1; cone=[T for T in itertools.product(*[range(admB(M,j,L)+1) for j in range(L)])
                      if all(T[j]<=T[i] for i in range(L) for j in range(L) if i<=j) and T[L-1]==0]
    def Mval(T): 
        tP=lambda j: M[0] if j==0 else T[j-1]
        return sum((tP(j)-T[j])*(M[j+1]-T[j]) for j in range(L))
    return sp.Rational(min(Mval(T) for T in cone),2)
print(f"  rlct(core M=(1,1,1)) = lambdaCore = {lc((1,1,1))}")
print(f"  rlct(core M=(2,2,2)) = lambdaCore = {lc((2,2,2))}")
print(f"  rlct(core M=(3,3,3)) = lambdaCore = {lc((3,3,3))}")
print("  ⟹ larger M = LARGER rlct (1/2 < 3/2 < 7/2). NOT monotone-decreasing — the OPPOSITE!")
print("  So 'deepest has larger reduced block ⟹ smaller rlct' is FALSE if read as M-monotonicity.")
print("  This is the ADVERSARIAL catch: the naive 'larger reduced block ⟹ more singular' is WRONG.")
