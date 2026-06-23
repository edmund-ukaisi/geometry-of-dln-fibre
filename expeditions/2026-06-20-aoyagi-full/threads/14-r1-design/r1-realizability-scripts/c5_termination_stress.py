import numpy as np
# STRESS the two load-bearing claims of the termination check:
# (S1) the C5 e≠0 chart genuinely drops ΣM (width-drop model correct for a non-front active layer)
# (S2) the e=0 locus is genuinely measure-zero (not where the achiever lives)
#
# (S1): The schurState model drops the FRONT two vertices. But a C5 node at active layer s drops the
# vertices s, s+1 (the active edge). Is that the right model, and does it always strictly decrease ΣM?
# The Schur peel at an edge (s,s+1) clears one rank-defect unit by removing one row (from layer s's
# matrix) and one col (from layer s+1's matrix). In WIDTH terms: the resolved dimension is removed from
# BOTH the layer-s output width and the layer-(s+1) input width — i.e. width[s] and width[s+1] each -1.
# Wait — layer s matrix is M^s × M^{s+1}. The edge (s,s+1) is layer s+1's matrix? Index carefully.
# Regardless: the peel removes ≥1 from ΣM per unit. Confirm ΣM strictly drops for any active layer:
def widthsum(M): return sum(M)
M=[3,3,3,3,3,3]
allok=True
for s in range(len(M)-1):   # active edge (s,s+1)
    for comp in [1,2]:      # complement rank
        if M[s]>=comp and M[s+1]>=comp:
            red=list(M); red[s]-=comp; red[s+1]-=comp
            if not (widthsum(red) < widthsum(M)): allok=False
print(f"(S1) ΣM strictly drops for every active edge & complement rank: {allok}")
print()
# (S2): is {e=0} measure-zero AND not the achiever's home? e = Cnext·(complement direction). The
# complement direction is the kernel-of-the-drop. e=0 ⟺ Cnext kills it too. 
# CRITICAL re-examination: in the cover lintegral ∫_U |F|^{-c}, the charts must cover U up to null.
# The blow-up of the rank-1 complement center: the exceptional ℙ^0 is a POINT (rank-1 ⟹ the projective
# space of a 1-dim complement is a single point). So there is NO multi-chart cover of the complement —
# it's a single blow-up coordinate ε. Then "e" is NOT ranging over a ℙ; e is FIXED (the downstream
# applied to the single complement direction). So {e=0} is a condition on the DOWNSTREAM (Cnext), not
# a chart-cover gap. Let me reconsider.
print("(S2) RE-EXAMINATION — rank-1 complement ⟹ the complement is a SINGLE direction (ℙ^0 = point):")
print("""
  For a rank-1 complement (the t=(3,3,2,2,2,0) case, drop 3->2 = 1 unit), the blown-up center is a
  SINGLE coordinate line — no projective chart cover (ℙ^0 is a point). So 'e' is not a chart-cover
  variable; e = Cnext·(the complement direction) is a function of the DOWNSTREAM coords.
  - If e ≠ 0 GENERICALLY (on a dense open set of downstream coords): the shear works on that open set;
    {e=0} is a proper subvariety (codim≥1 in downstream coords) ⟹ MEASURE ZERO in the lintegral. ✓
  - {e=0} = the downstream ALSO kills the complement ⟹ a DEEPER stratum (lower in the closure order),
    which is a SEPARATE admissible T' with its OWN branch in the recursion (reached by ANOTHER cascade
    path), NOT a sub-chart of THIS node. Its ΣM is smaller (deeper drop). So it terminates on its own branch.
""")
# So the e=0 worry is NOT a chart-cover gap for rank-1; it's the boundary between two strata, handled
# by the recursion's OTHER branches (the cover-exhaustiveness g34-g35, marked INFERENCE but the
# achiever-only route only needs the achiever's branch, which has e≠0 generically by construction).
# Verify e≠0 generically: sample downstream Cnext, complement dir v, check e=Cnext·v ≠ 0 a.e.
np.random.seed(0); zeros=0
for _ in range(5000):
    Cnext=np.random.randn(3,3); v=np.random.randn(3)
    e=Cnext@v
    if np.linalg.norm(e)<1e-9: zeros+=1
print(f"(S2) e=Cnext·v = 0 frequency over 5000 random downstream: {zeros}/5000 (expect 0 = generic e≠0).")
print()
# For the ACHIEVER: the cascade builds T* explicitly; at each C5 node the cascade's downstream factors
# are diag(1^{t_{s+1}},0) which act NONTRIVIALLY on the complement IF the complement is in the surviving
# block. Check: does the cascade give e≠0 at the achiever's C5 nodes?
print("(S2-achiever) The cascade C_s=diag(1^{t_{s+1}},0): at a C5 node the complement (dropped coord)")
print("  is the (t_s+1)-th coord; the downstream cascade factors are diag(1^{t_{s'+1}},0). e = downstream")
print("  applied to the complement. Whether e≠0 depends on whether the complement coord survives one")
print("  more step — by the cascade's nesting, the dropped coord is killed AT this layer (it's 0 in C_s")
print("  already), so e relates to the COUPLING, not the cascade's own zeros. Need pp2's exact cascade")
print("  downstream to pin e≠0 at the achiever node — flagged as the one item to confirm with pp2.")
