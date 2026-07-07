<task>
Design-review the INTEGRATED-blow-up assembly for a Lean lemma `sjBoundaryPeel` in a DLN RLCT proof,
and adjudicate one exact structural finding. Do NOT rubber-stamp.

GOAL. Prove (Lean): routeMLayerBoxIntegral M c' 1 ≤ ∑_{t≤min(M0,M1)} C_t · jointPeelIntegral M t c'.
BANKED, CLOSED: an MP front-split gives
   routeMLayerBoxIntegral M c' 1 = ∫_{A'∈box(tail)} ∫_{A0∈matBox(M0,M1)} frobSq(A0·Q)^{-c'},  Q:=prod(tail)A' (M1×n).
BANKED reusable: (i) schur_cov + measurePreserving_shearSub (Jacobian-1 block shear on the t-pivot chart,
A0=[[A,B],[C,D]], A t×t invertible → corank block Γ=D−CA⁻¹B, (M0−t)×(M1−t)); (ii) pivotLocus_eq_iUnion
(rank-≥t locus of A0 = ⋃ pivot-minor charts); (iii) matBox_corank_residual_le (ISOTROPIC corank atom):
   ∫_{D∈matBox(p,q)} (frobSq D + w)^{−c'} dD ≤ Cresid(pq)·w^{−(c'−pq/2)},  for w>0, c'>pq/2.
jointPeelIntegral M t c' := ∫_{A'} P_tail^{−(c'−a/2)}·P_full^{−a/2}, a=(M0−t)(M1−t),
P_tail=frobSqTopRows t (Q) (top-t-rows loss), P_full=frobSq(Q) (FULL product loss).

TWO POINTWISE ROUTES ARE DEAD (proven): (1) fixed-Q pointwise lift: Real.rpow 0^neg=0 on {P_tail=0};
(2) pointwise inner bound ∫_{A0}frobSq(A0 Q)^{−c'} ≤ C·(joint integrand)(Q): FALSE — for rank-deficient
Q the inner integral = +∞ (since {A0 Q=0} has codim M0·rank(Q), so ∫_{A0} converges iff c'<M0·rank(Q)/2;
e.g. (2,2,2,2), c'∈[1,1.5), rank(Q)=1 → +∞), while the joint integrand is FINITE there — no uniform C.
The {det Q=0} locus is NULL in A' (codim 1), so the box integral is finite, but not pointwise-provable.

EXACT FINDING (my analysis, numerically checked). After schur on the t-pivot chart,
   frobSq(A0·Q) ≍ ‖A_pivot·Q̃_top‖² + ‖Γ·Q_b‖²,   Q_b = the (M1−t) rows of Q at A0's NON-pivot columns
(the bottom rows are unsheared: Q̃_b=Q_b). The corank Γ enters ANISOTROPICALLY as frobSq(Γ·Q_b), NOT
frobSq(Γ). Isotropizing via Γ↦Γ·Q_b (Q_b full row rank) has Jacobian ∝ det(Q_b Q_bᵀ)^{(M0−t)/2}, so the
corank atom gives per-chart residual det(Q_b Q_bᵀ)^{−(M0−t)/2}·P_tail^{−(c'−a/2)} — a GRAM DETERMINANT of
the non-pivot tail rows, pointwise ≥ P_full^{−a/2}=‖Q‖^{−a}. So the honest per-chart residual ≠
jointPeelIntegral's P_full^{−a/2}. (Aoyagi's D_J block is a determinant, matching the Gram, not frobSq.)

<grounding_rules>
- Reason from the stated banked lemmas + the exact block finding. Separate inference from assertion.
- The dead routes and the block identity are established; judge the assembly design + the residual finding.
</grounding_rules>

<output_contract>
1. Do you AGREE the honest per-chart residual is the Gram det(Q_b Q_bᵀ)^{−(M0−t)/2} (not P_full^{−a/2}),
   so jointPeelIntegral as defined is not the reachable reduction target? BOUNDED to fix or a real problem?
2. RECOMMEND the cleaner split: (A) keep the corank Γ EXPLICIT in sjBoundaryPeel (piece 3 = pure MP+cover
   reduction to ∑_κ ∫_{A'}∫_Γ (P_tail+frobSq(Γ·Q_b))^{−c'}, deferring the atom/isotropization to the
   finiteness pieces 4/5/7), OR (B) apply the atom IN piece 3 with the honest Gram residual (redefine
   jointPeelIntegral). Which is more formalisable, and why?
3. The ordered lemma sequence for the chosen split: how to (a) do the per-chart radial/block blow-up
   INTEGRATED over each chart, (b) isotropize frobSq(Γ·Q_b)→ the atom (the Gram c.o.v.; what it needs of
   Q_b), (c) assemble over the pivotLocus_eq_iUnion cover with the rank-deficient {det Q_b=0} locus NULL
   per-chart (a.e.), before summing. 5–7 lemmas, dependency order, flag load-bearing vs plumbing.
4. The single biggest risk in the chosen split, and the cheapest exact check to de-risk it.
</output_contract>
