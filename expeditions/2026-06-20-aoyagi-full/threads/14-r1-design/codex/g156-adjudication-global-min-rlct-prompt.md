<task>
Determine whether, for the squared-Frobenius "zero-product" loss of a chain of matrices, the
ALL-ZERO point is the global-MINIMUM-RLCT point over any bounded region — and whether reduced
dimension >= 2 can create an interior singular stratum with STRICTLY SMALLER local RLCT.

SETTING. Chain widths M = (M_0, ..., M_{L+1}). A_s is M_s x M_{s+1}. Loss
  F(A) = || A_0 A_1 ... A_L ||_F^2   (square-Frobenius norm of the product; target = 0).
The real log canonical threshold rlct(F, p) at a point p of the zero-locus {F=0} = {A_0...A_L = 0}.
Known (Lehalleur-Rimanyi / Aoyagi): rlct(F, ALL-ZERO) = (1/2) * minAdm(M), where minAdm(M) is the
minimum over admissible rank profiles T of the codim mval(M,T). This is the DEEPEST point.

THE QUESTION (for a recursive blow-up RLCT proof). The recursion blows up one layer; the GE (>=) leg
needs |F_child|^{-c} integrable over a FIXED bounded "ratio box" Vz (the argmax chart's [-1,1]^d), NOT
just the child's point-RLCT. This box-integrability equals "c < rlct(child, all-zero)" IF AND ONLY IF
the all-zero point is the global-MINIMUM-RLCT point of F_child over Vz (the worst point governs the
integral). So:

  Q1. Is the all-zero point the global-minimum-RLCT point of F over the WHOLE space (equivalently over
      any bounded region)? I.e. for every p in {A_0...A_L = 0}, is rlct(F, p) >= rlct(F, all-zero)?
      Give the structural reason (orbit-closure / cone-tip / number-of-vanishing-directions), and state
      whether the inequality is STRICT or can TIE.

  Q2. Can reduced dimension >= 2 (intermediate widths exceeding the rank) create an INTERIOR singular
      stratum p (some factors nonzero, product still 0 — e.g. A_0 row in the left-kernel of A_1...A_L)
      whose local RLCT is STRICTLY BELOW rlct(F, all-zero)? Construct such a p or prove it cannot exist.
      Worked check welcome (e.g. (1,1,2): F = s^2(b1^2+b2^2); strata all-zero rlct 1/2, {s=0,b!=0} rlct
      1/2 TIE, {b=0,s!=0} rlct 1).

  Q3. If the all-zero point is the global min (ties allowed, never strictly below), then box-
      integrability collapses to the point-RLCT and the clean point-min recursion
      rlct(node) = min{mk/2, n/2 + rlct(child)} holds at the VALUE level (box-recursion internal to the
      proof). If some interior stratum can dip below, the recursion must thread genuine box-
      integrability and the value statement is NOT a clean point-min. Which is it?
</task>

<output_contract>
Q1-Q3 each: direct answer + derivation, FACT vs INFERENCE tags. End: one-line BOTTOM LINE —
"all-zero is global-min-RLCT (ties ok): point-min collapse HOLDS" or "interior stratum dips below:
box-recursion essential", + the single decisive reason.
</output_contract>

<grounding_rules>
The zero-locus is {product = 0}; all singular points have product exactly 0 (a rank-rho>0 product
point has F>0, NOT on {F=0}). rlct is governed by the worst (smallest-rlct) point of the zero-locus
inside the region. "More simultaneously-vanishing factors" => "more vanishing directions" => smaller
rlct. Check whether any non-cone-tip stratum can beat the cone tip. Derive; do not hand-wave Aoyagi.
</grounding_rules>
