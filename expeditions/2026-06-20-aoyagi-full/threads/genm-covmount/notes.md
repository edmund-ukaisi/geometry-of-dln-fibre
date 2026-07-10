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

## Checkpoint 2 (DONE) — `RouteMSJGoodCoords.lean`
- `sjTail_factor`: `(prod(tailChain M) A').submatrix(blockSplitEquiv κ)id = Ã₁·A₂` (banked front-peel +
  submatrix_mul). NOTE: `rw [submatrix_mul]` FAILS on the dependent-HMul product (CLAUDE.md friction);
  use the fully-applied `(Matrix.submatrix_mul …).trans` form.
- `sjGoodChartLoss` + `freedSchurLoss_eq_sjGoodChartLoss`: names the endpoint g_cc shape.
- `gammaPeelIntegral_sjGoodMap_eq`: UNCONDITIONAL EQUALITY, gammaPeelIntegral entirely in g_cc coords.
  (rw motive tip: don't `rw [choose_spec]` — its statement mentions the term being abstracted; isolate a
  `have heq` at the loss level and `rw [heq]`.)

## Checkpoint 3 (DONE) — `RouteMSJCornerBound.lean`
- `cornerRadialConst N R c'` + `cornerRadialConst_lt_top` (loss-free finite constant, `c'<N/2`).
- `corner_block_lintegral_le`: `∫_{ball R} g^{-c'} ≤ a^{-c'} · cornerRadialConst N R c'` — the EXPLICIT
  uniform-in-parameters bound (mirror of banked `corner_block_lintegral_lt_top`, ending le_trans key +
  lintegral_const instead of discarding to `<⊤`). Dependence on the loss is ONLY through the sphere lb `a`.
- `corner_block_lt_top_of_bound`: consistency witness (re-derives the banked `<⊤`).
  This unblocks the env integration (the cert's underspecified `domain control` step): on a good cover
  with `a≥a₀` and `R≤R₀`, inner ≤ a₀^{-c'}·cornerRadialConst N R₀ c' = CONSTANT, integrable over the
  finite-measure env box.

## Checkpoint 4 (DONE) — `RouteMSJVExpose.lean`
- `assembleFront x v W`: rebuilds the front factor from a FREE `v` + fixed corank map `W` (corank rows
  = W, pivot rows = v − P⁻¹B₁₂W; the inverse of the depth reduction).
- `sjGoodChartLoss_assembleFront`: `sjGoodChartLoss x Γ (assembleFront x v W) A₂ = frobSq(sjGoodMap P C
  W A₂ (Γ,v)).1 + frobSq(...).2` (v collapses via sub_add_cancel).
- `sjGoodChartLoss_endpoint_lt_top`: good chart (P left-inv, W/A₂ right-inv), `c'<(a·b+t·h)/2`,
  `∫_{(Γ,v)∈matBox×matBox} (sjGoodChartLoss x Γ (assembleFront x v W) A₂)^{-c'} < ⊤`. The TERMINAL chart
  finiteness with v EXPOSED — the target the v-exposure CoV lands on. Composes checkpoint 2 + banked
  endpoint.

## Checkpoint 5 (DONE) — `RouteMSJSphereLB.lean` (step 2, §8 uniform lower bound)
- `exists_uniform_sphere_lb`: continuous + pointwise-positive on unit sphere ⟹ `∃ a>0, ∀ ω, a ≤ g ω`
  (extreme-value `IsCompact.exists_forall_le'`; sphere compact since EuclideanSpace proper).
- `corner_block_lintegral_le_of_pos` / `corner_block_lt_top_of_pos`: the ball endpoint (explicit bound /
  finiteness) from POINTWISE positivity alone (derives the uniform a). Composes checkpoint 3.

## PRECISE HANDOFF for the next tide (the remaining mountain)

5 checkpoints banked (~490 LoC, all clean-three). Both CoV ENDS + endpoint machinery are banked:
- MEASURE-SIDE: `gammaPeelIntegral_sjGoodMap_eq` (= ∫∫∫ g_cc, v DETERMINED by A').
- ENDPOINT: `sjGoodChartLoss_endpoint_lt_top` (∫_{(Γ,v)-box} g_cc^{-c'} < ⊤, v FREE via assembleFront);
  `corner_block_lt_top_of_pos` (ball endpoint from pointwise positivity).

## Checkpoint 6 (DONE) — `RouteMSJDeepFactor.lean` (transport prerequisite)
- `sjDeepFactor M A'` (explicit deep factor, Classical.choose-free), `sjTail_factor_explicit`,
  `sjDeepFactor_update_zero` (A'0-independence — key for the Pi-split), `gammaPeelIntegral_sjGoodMap_eq'`
  (measure-side entry with explicit deep factor). Removes the Classical.choose motive blocker.

## Checkpoint 7 (DONE) — `RouteMSJPivotTranslate.lean` (transport step (c))
- `sjGoodChartLoss_pivotRows_translate_eq`: the pivot-rows→v translation EQUALITY (v-exposure atom).
  `∫_{U∈matBox} g_cc(of(elim U W)) = ∫_{v∈{v−P⁻¹B₁₂W∈matBox}} g_cc(assembleFront x v W)` via
  `measurePreserving_add_right` + `setLIntegral_comp_preimage_emb` + defeq (assembleFront = of(elim(v−S)W)).

## CODEX DESIGN (decorrelated, xhigh; `codex/transport-{prompt,answer}.md`)
Route A (Pi-split → Fubini → row-split → pivot-translation) is CONFIRMED cheapest; verified the API
pieces exist. "No mathematical wall in the transport itself — it is labour." Route B (single fiberwise
shear on A'0) collapses back to A or uses a fragile det-1 equiv — not preferred. KEY CAVEAT (matches
checkpoints 3+5): pointwise good=invertible is NOT enough for the env integral; need QUANTITATIVE δ-good
data OR a uniform compactness sphere-lb (checkpoint 5 gives the per-point version). Env skeleton:
`∫_{env∈EnvBox∩Good δ} inner ≤ ∫ BallBound δ = BallBound δ · vol(EnvBox∩Good δ) < ⊤`, with the shifted
(Γ,v)-box ⊆ fixed ball domination feeding the BALL endpoint (NOT the cube).

## PRECISE HANDOFF for the next tide (the remaining mountain)

`sjJointResolution:803` still open. Remaining = the MEASURE TRANSPORT connecting the two ends + cover +
recursion. Route A per Codex; steps (c)/translation banked (checkpoint 7), (Classical.choose blocker)
cleared (checkpoint 6). This is HEAVY interlocking infrastructure:

## Checkpoint 8 (DONE) — `RouteMSJTailSplit.lean` (transport step a)
- `eFrontTail` (Params (tailChain M) ≃ᵐ (A'0 layer)×(deeper), `piFinSuccAbove 0`), MP, apply,
  `eFrontTail_preimage_box`, `tailParams_pi_split`. The `A'0`-vs-deeper Pi-split. Mirrors banked `eFront`.

1. **measure transport (the hard core), remaining sub-steps:** (a) DONE = `tailParams_pi_split` (ck8).
   IMMEDIATE NEXT: the `sjDeepFactorCore` bridge — `sjDeepFactor M (eFrontTail.symm (U,rest))` is
   independent of U (Codex §2). Route: `(eFrontTail).symm (U,rest) = update ((eFrontTail).symm (U',rest))
   0 U` (needs `piFinSuccAbove.symm`/`insertNth 0`/`Fin.cons` apply lemmas at 0) + `sjDeepFactor_update_zero`
   (ck6). Fiddly, NOT a missing API — deferred, not walled. (b) the `A'0` row-reindex (`blockSplitEquiv κ`,
   MP — template `matReindexEquiv`, RouteMSJBlockReindex) + row-split into κ-pivot-rows × corank-rows(=W)
   via `sumPiEquivProdPi` (`splitCols` template) so the leading-layer box becomes `matBox(pivot) ×ˢ
   matBox(W)`; (c) DONE = `sjGoodChartLoss_pivotRows_translate_eq` (ck7). Then good-cover inverses → ball
   endpoint.
2. **env integration** — `∫_{env∈EnvBox∩Good δ} inner ≤ BallBound δ · vol(EnvBox∩Good δ) < ⊤`; inner ≤
   a₀^{-c'}·cornerRadialConst (ck3+5) on good env. Needs the shifted (Γ,v)-box ⊆ fixed ball domination
   (Codex §3, cert §1c) to use the BALL endpoint (ck3/5) — the CUBE endpoint (ck4) is NOT enough (domain
   is a shifted box). Use QUANTITATIVE δ-good (|det P|≥δ, δ-minors of W, A₂), NOT bare invertibility.
3. **good/deeper cover + L-recursion** — matBox∩pivotChart = good{|det pivot|≥δ} ∪ deeper; deeper
   NON-binding by banked `sjChargeBudget_le`; L-recursion over the rank flag (finite, nonincreasing).

The threshold bookkeeping: for the endpoint on `(Γ,v)` the dim is `(M0-t)(M1-t)+t·M2`; the charge
accounting `sjChargeBudget_le` gives min-over-branches = minAdm. See `genm-covdesign/sjjoint-exponents-cert.md`.

DEAD END confirmed: `sjJointResolution_of_boxThresholdFinite` (RouteMSJJointReduce) is circular.
Corank-atom route (`freedSchurLoss_inner_peel_lt_top`, RouteMSJFreedPeel) has interface hyps that fail
pointwise — same mountain. The endpoint route (this thread) is the live path.
