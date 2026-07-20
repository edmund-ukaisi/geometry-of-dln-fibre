# Abstract-field pass — gate verdict (elder, 2026-07-18; task #56)

**VERDICT: the strengthened ChartBridge FORCES-ENOUGH for region_glue across every field. NO new
conjunct. The gate CLEARS; ChartBridge is FROZEN for the glue lane.** Both prior elder bets
(image-cover, residualCore squeeze) REFUTED as gaps — recorded as calibration. Every confound
resolved to a named BANKED proof step, not a missing hypothesis.

## Per-field (condensed; full text in the controller journal thread)
1. chartMap — FORCES-ENOUGH. Chain rule gives HasFDerivWithinAt; a.e.-InjOn suffices. Confound
   (volume N = 0 does not give N measurable; volume not complete): handled by
   `exists_measurable_superset_of_null` → N̄; integrate on srcBox∖N̄; discard the null image via
   `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`.
2. srcBox (measurable + bounded) — FORCES-ENOUGH; boundedness forces the enlarge-to-cube step
   Tonelli factorizes on (the F1 fix earning its keep).
3. divCoord/resCoord — FORCES-ENOUGH; injectivity + disjoint ranges IS the Tonelli alignment
   (no implicit assumption). Per-divisor total |u|^(divExp−1−2c') finite iff c' < divExp/2 = hrat.
4. LeafPullback residualCore + squeeze — FORCES-ENOUGH; NO cross-leaf uniformity needed (finite
   cover ⟹ finite sum of per-leaf finites). residualCore is NOT measurable-asserted and must NOT
   be integrated: bound the measurable (F∘chartMap)^(−c') pointwise via the squeeze. Upper squeeze
   forcing residualCore = 0 at the Morse center is faithful; the ∞ sits on a null set.
5. terminalExponents (divExp + resRank fold) — FORCES-ENOUGH; exactly the banked-read conditions
   (`lintegral_Ioc_rpow_lt_top`: c' < divExp/2; `sumSqND_box_lt_top`: c' < resRank/2). divExp = 0
   divergence impossible under hrat (c' > 0 branch). The resRank fold is load-bearing here.
6. LeafJacobian — FORCES-ENOUGH; |det Dφ| ≤ hi·∏|u|^(divExp−1) is the exact area-formula input.
   lo/ψsymm/inverse identities carried, honestly non-load-bearing. Area formula's g needs no
   measurability.
7. image-cover clause — FORCES-ENOUGH (elder bet REFUTED). The INDUCTIVE carrier forces finite
   trees ⟹ `leaves t` finite ⟹ the cover is a finite union (`lintegral_iUnion_le`, no extraction,
   no image measurability). Globalization: 0 ∈ locus ⊆ U open ⟹ paramsBoxM M ε ⊆ U
   (`exists_small_paramsBox_subset_open`); then the banked homogeneity globalization. L=0 corner
   banked.
8. residualCore squeeze standalone — REFUTED as a gap (see 4).
9. divProfile/Adm — out of region_glue's scope (feeds exponent_ledger_bridge upstream).

## OPTIONAL convenience (NOT required; tide's preference)
Strengthening `∃ N, volume N = 0` to also carry `MeasurableSet N` skips the superset step; the
construction supplies it freely (exceptional fibres closed). Proof-convenience, not soundness —
if wanted, the one-line ChartBridge edit routes through the construction seat (file owner).

## Proof-step checklist for the per-leaf tide (banked lemmas, not hypotheses)
- N̄ := `exists_measurable_superset_of_null` N; integrate on srcBox∖N̄; discard chartMap''(srcBox∩N̄)
  via `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`.
- `lintegral_image_eq_lintegral_abs_det_fderiv_mul` on srcBox∖N̄; chain rule
  |det Dφ| = |det Dψ(β·)|·|det Dβ| ≤ hi·∏|u|^(divExp−1).
- Bound the MEASURABLE (F∘chartMap)^(−c') pointwise via the LeafPullback squeeze; never integrate
  residualCore itself.
- Enlarge bounded srcBox to the flat cube [−R,R]^(flatDim M); Tonelli over divCoord (distinct) ×
  resCoord (distinct, disjoint) × spectators (constant bound, finite volume).
- 1-D reads: `lintegral_Ioc_rpow_lt_top` (c' < divExp/2) + `sumSqND_box_lt_top` (c' < resRank/2).
- Cover: finite `leaves t` ⟹ `lintegral_iUnion_le` finite sum; ε-box ⊆ U ⊆ ⋃ images; then
  `routeMLayerBoxIntegral_lt_top_of_small_box`; c' ≤ 0 corner banked.

## Scope caveat
This certifies region_glue's PROVABILITY FROM ChartBridge. It does NOT certify the construction
can satisfy LeafPullback/LeafJacobian's monomial assertions — that is rung 3-4's burden; a gap
there surfaces there. Orthogonal open item at pass time: the case-2 `+= 1` fix (elder+reviewer
convergent) not yet landed — blocks rung 2, independent of region_glue.
