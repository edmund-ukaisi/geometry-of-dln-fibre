import sympy as sp
# Reconcile: lemma2Fwd is MP (det=-1, pure transvections), but my deepest-χ is unit-Jacobian.
# WHY the difference? lemma2Fwd straightens the STEP-1 RESIDUAL Q=‖Â B‖², Â=[[1,t1],[t2,t3]] -- where
# the pivot Â[0,0]=1 is a HARD 1 (constant), so the shears b00↦b00+t1 b10 are pure transvections (det=1).
# My deepest-χ straightens ‖prod-B‖² at A1=A2=[[1,0],[0,0]], where the perturbed pivot is (1+w0) -- a
# UNIT but not constant 1 -- so the elimination divides by (1+w0), giving a unit (non-±1) Jacobian.
#
# THE RECONCILIATION: in the (2,2,2) RESOLUTION, the blow-up happens FIRST (step1: A1=x·Â, Â[0,0]=1
# HARD), making the pivot a hard 1, THEN lemma2Fwd (transvections, MP). So the MP-ness comes from the
# blow-up normalizing the pivot to a hard 1 BEFORE the straighten.
# At the DEEPEST POINT directly (L2 product_reduction, no blow-up), the regular block's pivot is the
# PERTURBED (1+w0), so the straighten is unit-Jacobian.
#
# IMPLICATION for the L2 deepest split (#125): is L2's split done WITH a blow-up (then MP transvections)
# or WITHOUT (then unit-Jacobian)? L2 product_reduction is the REGULAR peel at the deepest point -- it
# does NOT blow up (the blow-up is R1, downstream on the core). So L2's regular-block split is
# unit-Jacobian, NOT MP. The MP lemma2Fwd is a RESOLUTION (R1) step, not the L2 regular peel.
print("=== RECONCILED: lemma2Fwd (MP) is an R1 RESOLUTION step; L2's regular peel is unit-Jacobian ===")
print("lemma2Fwd is MP because the step-1 BLOW-UP first normalizes the pivot to a HARD 1 (Â[0,0]=1),")
print("making the straighten pure transvections (det=−1). That's an R1 (resolution) operation.")
print()
print("L2 product_reduction's regular-block split at the deepest point does NOT blow up — the pivot is")
print("the PERTURBED unit (1+w0), so the split is unit-Jacobian (det = unit, not ±1). DIFFERENT operation.")
print()
print("So for the consumers:")
print(" - fm-2's schur_chart_exists (the R1 resolution chart, AFTER the blow-up normalizes the pivot to")
print("   a hard 1): CAN be MP (transvections, like lemma2Fwd) — the blow-up gives the hard pivot.")
print(" - a114e07e's L2 half-(a) regular-block split at the deepest point (NO blow-up): is unit-Jacobian,")
print("   NOT MP. Use the unit-weight rlctAtOn transport (rlct_unit_invariant_aux mechanism), not")
print("   rlctAtOn_comp_homeomorph (which needs MP).")
print()
print("THIS IS THE KEY DISTINCTION TO RELAY: the two consumers need DIFFERENT transport interfaces.")
print("fm-2 (R1 chart, post-blow-up hard pivot) = MP/transvection (lemma2Fwd-style, rlctAtOn_comp_homeomorph).")
print("a114e07e (L2 regular peel, deepest, no blow-up) = unit-Jacobian (unit-weight threshold invariance).")
