import sympy as sp
# EXHAUSTIVENESS (a): does the (C2) recursion's atlas inf = the TRUE rlctAtOn(core) 0, not just ≤?
#
# The recursion gives, per the squeeze chain (#129/#131):
#   rlctAtOn(core_M) 0 = nReg_M/2 + rlctAtOn(core_{M'}) 0           [the squeeze step, EXACT EQUALITY]
# UNROLLING to the leaf: rlctAtOn(core_M) 0 = Σ_levels nReg/2 + rlctAtOn(leaf) 0.
# CRUCIAL: the squeeze step is an EQUALITY (rlctAt_mono both ways), NOT an inequality. So IF the
# recursion is a SINGLE chain (one blow-up center per node, deterministic), the result is an EXACT VALUE,
# and exhaustiveness is AUTOMATIC — there is no ⨅ over branches to worry about, it's a chain of equalities.
#
# BUT: the blow-up of a rank-defect center is covered by MULTIPLE affine charts (one per nonzero
# homogeneous coordinate / pivot choice — the #127 chart-locality caveat). So at each node there IS a
# branching: the cover is ⋃ charts, and rlctAtOn = ⨅ over charts (S1.1 min-over-cover). The question is
# whether ⨅ over the chart-cover at each node = the per-node squeeze value (so no chart beats it).
print("=== The key distinction: EQUALITY-chain vs ⨅-over-charts ===")
print("""
Two layers of structure:
 (1) Per NODE: the blow-up of the rank-defect center {rank < full} is an affine CHART COVER (Proj
     atlas — one chart per nonzero pivot coordinate). rlctAtOn(core) 0 = ⨅_{charts} (chart threshold).
     [This is the S1.1 min-over-cover; needs the charts to COVER a nbhd of origin∩{core=0}.]
 (2) WITHIN each chart: the pivot is a HARD unit (#127), the squeeze step applies, giving an EXACT
     equality nReg/2 + rlctAtOn(reduced core) — and the reduced core recurses (its own chart cover).

So the atlas is a TREE: nodes branch into charts (the ⨅), each chart descends by an equality to a
smaller node. The leaf value is nReg-sum/2 (pure smooth block, rlct = #squares/2).

EXHAUSTIVENESS = (a1) the chart cover at each node covers origin∩{core=0}  [⨅ is the true rlct, not
an over-estimate from a partial family]  +  (a2) the per-chart/per-divisor ratio is ≥ the codim-min
(multiplicity control) so the ⨅ doesn't UNDERSHOOT lambdaCore.
""")
# Verify the LOCAL cover claim on the (2,2,2)/(3,3,3) rank-defect center: blow up {A1=0} (the rank-0
# locus of the first factor), the charts = {A1[i,j] = pivot ≠ 0} for each (i,j). Do they cover a
# punctured nbhd of the center?  The center {A1=0} blown up: P(entries of A1) — affine charts U_{ij}
# = {A1[i,j] ≠ 0}, and ⋃_{ij} U_{ij} = {A1 ≠ 0} = complement of center. The center itself maps to the
# exceptional divisor (covered fibrewise). So yes — the chart cover is the standard projective atlas,
# EXHAUSTIVE by construction (every nonzero A1 has some nonzero entry).
print("(a1) LOCAL cover: blow-up of {A1=0} has affine charts U_{ij}={A1[i,j]≠0}; ⋃U_{ij}={A1≠0}.")
print("     Every point off the center has SOME nonzero coordinate ⟹ lies in some chart. EXHAUSTIVE")
print("     by the projective-atlas tautology (not a coincidence). The center → exceptional divisor,")
print("     covered fibrewise. This is the standard Proj cover — #127's chart-locality caveat says no")
print("     SINGLE chart covers all, but the UNION does. ✓")
