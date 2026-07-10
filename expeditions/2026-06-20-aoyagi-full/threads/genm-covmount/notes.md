# genm-covmount — CoV mountain thread notes

Target: close `sjJointResolution` (`RouteMSJResolution.lean:803`), `gammaPeelIntegral M t ρ κ c' < ⊤`
for `c' < minAdm M / 2`. Multi-tide mountain (~65-75% new). Base `9aa158e3`.

## Architecture (as mapped)

`gammaPeelIntegral M t ρ κ c' = ∫_{A'∈paramsBoxM(tailChain M)1} ∫_{A0∈matBox∩pivotChart ρ κ} frobSq(rmatMul A0 (prod(tailChain M) A'))^{-c'}`.

Banked chain to the freed form (prior tides):
- `gammaPeelIntegral_schurShearFree_eq` (RouteMSJFreedPeel) — EQUALITY, rewrites gammaPeelIntegral into
  `∫_{A'} ∫_{x∈outerDom t (M0-t)(M1-t) 1} ∫_{Γ∈shearbox} (freedSchurLoss x Γ Q̃)^{-c'}`,
  `Q̃ = (prod(tailChain M) A').submatrix (blockSplitEquiv κ) id`. NO finiteness, NO hyps.
- `freedSchurLoss x Γ Q = frobSq(P·Q̃ₚ) + frobSq(C·Q̃ₚ + Γ·Q_b)`, `Q̃ₚ = Q_p + P⁻¹B₁₂ Q_b`,
  `P=of x.1.1, B₁₂=of x.1.2, C=of x.2, Q_p/Q_b = row-blocks of Q`.

## What I banked

- **Gap A (DONE)**: `RouteMSJDepthReduce.lean` — `freedSchurLoss_eq_sjGoodMap` (hyp form:
  `Q̃ₚ = v·A₂`, `Q_b = W·A₂` ⟹ freedSchurLoss = g_cc(Γ,v)) + `freedSchurLoss_eq_sjGoodMap_mul`
  (product form: from `Q̃ = Ã₁·A₂`, reads `W=(Ã₁)_b`, `v=(Ã₁)_p + P⁻¹B₁₂(Ã₁)_b` via submatrix_mul).
  Clean-three. Front-peel (`prod_front_peel`, RouteMFrontPeel) is BANKED, so gap A was mostly the
  pointwise algebra composing `schurSplitLoss_eq_sjGoodMap`.

## The remaining mountain (precise)

After the integrand-level rewrite into g_cc coords, `gammaPeelIntegral = ∫_{A'} ∫_x ∫_Γ g_cc(Γ, v(A',x))^{-c'}`
where `v(A',x) = (Ã₁)_p + P⁻¹B₁₂ W`, `W=(Ã₁)_b`, `A₂=A₂(A')` (deep factor), `Ã₁=(A'0).submatrix(blockSplitEquiv κ)id`.

The endpoint `sjGoodMap_loss_matBox_lt_top` bounds `∫_{(Γ,v)∈box×box} g_cc^{-c'}` for `c'<(pq+th)/2`
treating v as a FREE box variable + P left-inv, W/A₂ right-inv. But in gammaPeelIntegral v is DETERMINED
by (A',x), not free. Two remaining un-banked pieces:
1. **v-exposure CoV**: for fixed (deeper→A₂, W, P, B₁₂, C), the pivot rows `(Ã₁)_p ↦ v` map is a
   TRANSLATION (Jac 1), exposing v as a free box variable. Then inner ∫_Γ∫_v = endpoint.
2. **env integration + UNIFORM endpoint bound**: integrating the finite inner over the bounded
   environment (deeper, W, x)-box needs a UNIFORM-in-parameters endpoint bound. The banked
   `corner_block_lintegral_lt_top` proof ALREADY produces `∫ ≤ a^{-c'}·(∫r^p)·μ_sphere` — extractable as
   `corner_block_lintegral_le`. Needs `a≥δ²` uniform on good cover (§8 compactness gate) + `R≤R₀`.
3. **good/deeper cover split + charge (sjChargeBudget_le) + L-recursion** over the rank flag.

CIRCULARITY WARNING: `sjJointResolution_of_boxThresholdFinite` (RouteMSJJointReduce) reduces to
`RouteMBoxThresholdFinite M` of the SAME chain — circular, useless for the induction. Confirmed by prior
tides (genm-sjcarrier8/sjbuild3): the (S,J) descent is the genuine unbuilt content.

## Checkpoint 2 target
`gammaPeelIntegral_sjGoodMap_eq` — unconditional integrand-level rewrite of gammaPeelIntegral into g_cc
coords (composes schurShearFree_eq + prod_front_peel + submatrix_mul + Gap A). Then the finiteness is the
remaining analytic mountain (pieces 1-3 above).
