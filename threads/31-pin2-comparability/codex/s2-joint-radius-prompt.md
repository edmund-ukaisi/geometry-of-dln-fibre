Lean 4 / Mathlib v4.29. I'm filling the S2 leaf of an L=2 diffeo-bridge: `ContDiffAt ℝ ⊤ (psiSplitDeltaL2 H r hr hL) q` for `q ∈ tsupport (cutoffBumpSplit H r hr hL)` (a ContDiffBump at 0 on `DeepestSplit = (Fin nReg→ℝ)×((Fin nCore→ℝ)×(Fin nGauge→ℝ))`).

I have (all LANDED, sorry-free):
- The lens decomposition `psiSplitDeltaL2Core_eq_payload`: at L=2, `psiSplitRawL2Core q - q = (rgΔ.1, (cΔ, rgΔ.2))` where `rgΔ = regGaugeSlotCLE.symm (l2GaugeΔ q)`, `cΔ = paramsEquivFlatCLE (l2CoreΔTuple q)`.
- The entrywise ContDiff of all named matrices (l2A0/A1/Y0/Z1/Y1/T1) EVERYWHERE.
- `contDiffAt_matrix_inv_entry_of_det_ne_zero_at` (ContDiffAt-family inverse entry on det≠0), `contDiffAt_matrix_mul_entry`.
- The named composites K = Z1·P00⁻¹·Y0, R = Z1·A1⁻¹·A0⁻¹·Y0, W = 1+R, S1 = T1−Z1·A1⁻¹·Y1, Br, with l2T1p = W⁻¹·Br and l2Y1p = Y1 + A0⁻¹·Y0·(T1−T1').

The matrices P00 = A0·A1+Y0·Z1 and W = 1+Z1·A1⁻¹·A0⁻¹·Y0 (and A0=1+readX_0, A1=1+readX_last) are all =1 (or invertible) at q=0. To get ContDiffAt of l2T1p/l2Y1p entries at a GENERAL support point q, I need det(A0 q),(A1 q),(P00 q),(W q) ≠ 0 at q.

The current `cutoffBumpSplit` is keyed to `unitRadius/2` where `unitRadius` ball ⊆ `unitSet = {p | ∀ s, det(1+readX_s p)≠0}` (the 1+readX locus ONLY — NOT enough for det P00/det W ≠ 0).

PLAN: re-key `cutoffBumpSplit` to a JOINT-unit radius. The matrices depend only on the gauge slot `(q.1,q.2.2)`; the W/P00 conditions only make sense at L=2 (they take `hL2eq : L=2`). The bump is L-generic.

QUESTIONS:
1. What's the cleanest L-generic `jointUnitSetSplit : Set DeepestSplit` (open, contains 0) such that at L=2 a ball inside it has det(P00),det(W)≠0 (plus det(1+readX_s)≠0 always)? Options: (a) `{q | (∀s, det(1+readX_s (q.1,q.2.2))≠0) ∧ (if h:L=2 then det(l2P00 ... q)≠0 ∧ det(l2W ... q)≠0 else True)}`; (b) define it only via det(1+readX) and SEPARATELY prove det P00, det W ≠0 follow on a SMALLER ball by continuity (det P00, det W continuous, =1 at 0). Which avoids the `dite`/`hL2eq`-cast pain in the openness + ball-subset proofs?
2. For openness with the `dite (L=2)`: does `IsOpen` of the set survive the `if h:L=2` cleanly, or should I `rcases eq_or_ne L 2` at the TOP of the whole S2 leaf (I already do) and define a SEPARATE joint bump only used in reasoning — no, the bump is baked into psiL2. So the bump's radius must be one L-generic def. 
3. Is option (b) cleaner: keep `cutoffBumpSplit` keyed to a radius `ρ` defined as `min (unitRadius/2) (a radius from a det-P00-and-W ≠0 ball)` where the second radius is obtained at L=2 (and = unitRadius/2 for L≠2)? i.e. `ρ := if h : L = 2 then min (unitRadius/2) (jointExtra h) else unitRadius/2`.

Give the cleanest construction + the openness/ball-subset proof sketch, flagging the `dite`-through-`IsOpen`/`Metric.ball` cast pitfalls. Note: at L≠2 psiSplitDeltaL2 = 0 (already proven), so the L≠2 branch of S2 is trivial — only the L=2 branch needs the joint dets.
