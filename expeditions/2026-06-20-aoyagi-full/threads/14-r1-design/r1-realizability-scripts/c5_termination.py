# C5 per-chart branching termination under the LIVE measure ΣM (chainWidthSum), and under lex(L,ΣM).
#
# The C5 node (partial drop t_{s-1}=a > t_s=b > 0, complement rank a-b) branches into:
#   (charts e_i≠0): the standard blow-up cover of the complement direction. Each chart resolves the
#     rank-1 complement defect via the Schur/shear step. The reduced chain S.red = the survivor (rank b)
#     continuing. What is ΣM_red vs ΣM?
#   (e=0 sub-branch): the downstream ALSO kills the complement → a DEEPER defect. The recursion
#     descends into it. ΣM behavior?
#
# Recall schurState (the C1 model): drop=1 at the two pivot vertices (s.val<=1), so ΣM drops by 2.
# For a C5 partial drop of (a-b) units at the active vertex: the Schur clears (a-b) rank-defect units.
# Each unit drops the width at the pivot vertex by 1 (the resolved row+col). So:

def chainWidthSum(M): return sum(M)

# Model the C5 node width-drop. M = widths (Fin L+1). Active layer s: partial drop a->b, complement a-b.
# The Schur step on the complement clears (a-b) units. The width at the pivot vertices drops.
# In the schurState model (front pivots), drop=1 each at s=0,1. For a general active layer, the two
# Schur pivot vertices are layers s, s+1 (the active edge). Each drops by the complement rank (a-b).

# CASE 1: the e_i≠0 charts (complement resolved). The Schur peels (a-b)=1 unit (rank-1 complement).
#   ΣM_red = ΣM - 2*(a-b)? or - (a-b)? Depends on whether the peel clears row+col (2 vertices) or 1.
#   In schurState: drop=1 at BOTH pivot vertices (the edge's two endpoints), so ΣM drops by 2 per unit.
#   For a rank-1 complement: ΣM drops by 2. STRICTLY DECREASING. ✓
def c5_chart_red_widthsum(M, s, complement_rank):
    # peel complement_rank units at the active edge (vertices s, s+1), drop 1 each per unit
    red = list(M)
    red[s]   -= complement_rank
    red[s+1] -= complement_rank
    return red
M = [3,3,3,3,3,3]
s, a, b = 2, 3, 2; comp = a-b   # the C5 step in t=(3,3,2,2,2,0): layer index 2, drop 3->2
red = c5_chart_red_widthsum(M, s, comp)
print(f"C5 e≠0 chart: M={M} (ΣM={chainWidthSum(M)}) -> red={red} (ΣM={chainWidthSum(red)})")
print(f"  ΣM decrease: {chainWidthSum(M) - chainWidthSum(red)} (= 2*comp = 2*{comp}). STRICT? {chainWidthSum(red) < chainWidthSum(M)}")
print()
# CASE 2: the e=0 sub-branch (downstream kills the complement too — a DEEPER defect).
# Here e=0 means Cnext·(complement dir)=0, i.e. the NEXT factor has additional rank defect. This is a
# rank vector with a DEEPER drop than t. Does ΣM decrease? The e=0 locus is a sub-blow-up: it adds
# an exceptional resolving the e=0 condition. The width-drop: e=0 means the downstream factor drops
# rank in the complement direction → its own Schur peel → ΣM drops further (another -2) OR L drops.
print("C5 e=0 sub-branch (downstream kills complement = deeper defect):")
print("""
  e=0 ⟺ the next factor Cnext also annihilates the complement direction. This is NOT a free chart of
  the SAME node — it is a DIFFERENT rank stratum (deeper: the complement defect propagates downstream).
  Two readings of how the recursion handles it:
  (R1) e=0 is a CLOSED sub-locus of the blow-up center; the blow-up chart cover {e_i≠0} covers the
       complement projective space MINUS {e=0}. {e=0} is lower-dimensional (codim ≥1 in the exceptional
       ℙ). For the lintegral/rlct it is MEASURE ZERO ⟹ does NOT need its own branch (the cover-up-to-null
       discipline, g34-g35 cover-completeness). ⟹ NO e=0 branch needed; the {e_i≠0} charts cover a.e.
  (R2) IF e=0 must be resolved (not null), it is a deeper rank-defect ⟹ a node with LARGER total defect
       ⟹ its resolution peels MORE units ⟹ ΣM drops MORE. Still strictly decreasing.
""")
# Check (R1): is {e=0} measure-zero in the blow-up exceptional? e ranges over the downstream applied
# to the complement line. e=0 is a proper algebraic subvariety (Cnext·v=0 for v the complement dir)
# ⟹ codim ≥1 ⟹ measure zero in the chart. The {e_i≠0} affine charts cover the exceptional ℙ up to
# the coordinate hyperplanes, standard projective blow-up cover. ✓
print("(R1) is the operative one: {e=0} is a proper subvariety (codim≥1) of the exceptional ℙ ⟹")
print("  MEASURE ZERO ⟹ the {e_i≠0} affine charts cover a.e. (the standard projective blow-up cover).")
print("  NO separate e=0 branch in the lintegral. The cover-up-to-null discipline (g34-g35) handles it.")
print()
print("⟹ TERMINATION: the C5 e≠0 charts each drop ΣM by 2·(complement rank) > 0 (STRICT, under the")
print("  LIVE chainRel = ΣM-decrease). The e=0 locus is null (no branch). The branching is FINITE")
print("  (one chart per nonzero component of e = the complement ℙ's affine cover, finite).")
