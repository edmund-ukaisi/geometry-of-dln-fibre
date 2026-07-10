# genm-cruxfinish — the residual CoV route (`frontChartIntegral_lt_top`)

**Status at tide close.** Of the 3 carrier sorries this tide targeted, **2 are fully closed**
(`reduced_frobSq_ae_pos` / CRUX A, and the `morse_reduced_box_lt_top` borderline `c'=d/2`), and the
datum `normalSliceChartData` is **restructured so its `cover` field is PROVED**; the sole remaining
sorry is the per-chart change-of-variables **`frontChartIntegral_lt_top`** in
`RouteMFrontPeelCarrier.lean`. This note records the decorrelated-Codex-validated route
(`codex/cov-route-{prompt,answer}.md`, xhigh) for the follow-on tide.

## The goal
On the pivot chart `{A' | (ρ,κ) q×q minor of P = prod (tailChain M) A' is a unit}`, show the front-split
loss integral `∫_{chart}∫_{A0 box} frobSq(A0·P)^{−c'}` is `< ⊤` below `½·minAdm M`, given the strong IH
`RouteMBoxThresholdFinite (redTail M q)`.

## The four sub-pieces, ranked by Lean difficulty (Codex §4, hardest first)

1. **Domain control over the UNBOUNDED Schur image — the genuine residual subtlety (HARDEST).**
   The shear coefficients `K_i = γ_i α_i⁻¹` blow up as the `(ρ,κ)`-minor → singular on the open chart,
   so the measure-preserving CoV maps the bounded `A'`-chart to an UNBOUNDED reduced-`Y` region. The
   banked finiteness brick `reducedMorseFront_lt_top` is for the radius-`1` BOX. Fixed-radius box-scaling
   homogeneity proves radius-independence for any FINITE box but does NOT cover the unbounded image
   (Codex §2 warning, independently reached). **This is not pure labour.** Two candidate resolutions:
   - **(a) bounded-image refinement.** Refine the pivot chart into a FINITE family on which `|minor det|`
     is bounded away from `0` (hence `α⁻¹`, `K` bounded, image in a fixed radius-`T` box). The naive
     countable `{|det| ≥ 1/n}` cover is NOT safe (overlapping, `T_n → ∞`, the per-piece finite bounds can
     sum to `⊤`). A genuinely finite refinement with a uniform `T` is the open question.
   - **(b) unbounded-domain finiteness variant** of `reducedMorseFront_lt_top` (integrate the Morse+core
     integrand over `Y ∈ ℝ^{flatDim(redTail)}`, not just the box). This is a real RLCT-at-infinity claim;
     the tail decay of `frobSq(prod redTail Y)^{−c'}` at large `Y` must be controlled.

2. **Loss split (hard, local once isolated).** The `A0`-integral takes its OWN shear
   `A0 ↦ A0·(S₀)⁻¹` (rowwise unit-triangular, measure-preserving). From `S₀·P = fromBlocks α B 0 Z`,
   `A0·P = (A0·(S₀)⁻¹)·fromBlocks α B 0 Z`; block-split the sheared `A0`'s columns to expose
   `frobSq(A0·P) ≃ ‖R‖² + frobSq Z` (`R` the `M₀q` block, `Z = prod (redTail) Y`). Aim for the exact
   block expression then the inequality needed for `lintegral_mono` — avoid a brittle global equality
   (non-orthogonal `α,B` changes can introduce determinant factors).

3. **Telescoping (tedious opaque-width algebra, but the invariant is STABLE).** Approach (a): define the
   shear coefficients `K i` by BACKWARD recursion (`K N = 0`, `K i = γ_i α_i⁻¹`) FIRST, then prove a
   FORWARD-prefix telescope over `prodAux` (do not induct right-to-left through the fold). Invariant, with
   `N := L+1` tail layers, everything reindexed by `blockSplitEquiv`:

       Pblk n := reindex (prodAux H A' n);  S i := fromBlocks 1 0 (-(K i)) 1;  Sinv i := fromBlocks 1 0 (K i) 1
       Invariant(n):  ∃ Bacc, S 0 * Pblk n * Sinv n = fromBlocks (αProd n) Bacc 0 (YProd n)
       αProd 0 = 1, YProd 0 = 1, αProd (n+1) = αProd n * α n, YProd (n+1) = YProd n * Y n

   Step: `S 0 * Pblk (n+1) * Sinv (n+1) = (S 0 * Pblk n * Sinv n) * (S n * Xblk n * Sinv (n+1))`, then
   apply the banked `blockShear_step` to the second factor + `fromBlocks_multiply`; fully-applied
   associativity terms (`mul_three_reassoc`), never `rw [Matrix.mul_assoc]`. At `n = N`, `K N = 0` ⟹
   `Sinv N = 1` ⟹ the normal form. Keep as an ABSTRACT theorem from a `ThreadedShearData` bundle;
   construct the data from the chart separately. Rank read off by the banked
   `rank_eq_q_add_of_normalForm` (already in `RouteMSJThreadedShear`).

4. **Radius scaling (EASIEST; clean standalone, genuinely reusable).** Fixed-radius product-box identity
   (Codex §2, exponent certain, Mathlib scaling-API names not pinned):

       ∫_{paramsBoxM H T} ofReal(frobSq(prod H A)^{−c'})
         = ofReal(T^(flatDim H − 2·N·c')) · ∫_{paramsBoxM H 1} ofReal(frobSq(prod H A)^{−c'})   (0 < T)

   from `prod H (T•A) = T^N • prod H A` (BANKED `D1L2ExplicitCoreProducer.prodAux_smul_pow` /
   `LossHomogeneity`) + `frobSq (T^N•P) = T^{2N}·frobSq P` + linear cube scaling (Jacobian `T^{flatDim}`).
   Anisotropic variant for the Morse+core (`X`-radius `T^N`, `Y`-radius `T`):
   `I(T^N, T) = T^(flatDim + N·d − 2N·c') · I(1,1)` with `d = M₀q`. The exponent sign never breaks
   finiteness (`T^e` a finite positive real) — but see sub-piece 1: this covers finite boxes only.

## Recommended isolation (Codex §4)
Package the telescope + MP CoV + `A0` loss split + finite-radius/image control as hypotheses of a single
`frontChartIntegral_lt_top_of_threadedCoV`; everything above then consumes `reducedMorseFront_lt_top`
cleanly. The current single named sorry `frontChartIntegral_lt_top` already sits at this granularity.

## What is PROVED and consumable now (this tide)
- `reduced_frobSq_ae_pos` (CRUX A) — `corePoly` a.e.-nonzero transport + `minAdmRec_eq_zero_of_width_zero`
  degenerate case-split. Factored reusable helpers: `frobSq_prod_ae_pos` (all widths ≥1 ⟹ a.e. pos),
  `all_one_le_of_one_le_minAdm`.
- `morse_reduced_box_lt_top` borderline — `rpow_add_split_le` (AM-GM split) → pure-Morse `Kbound` × IH core.
- `normalSliceChartData.cover` — pivot cover (`pivotLocus_eq_iUnion` rank `q`) + `lintegral_iUnion_le`.
- Banked bricks in `RouteMSJThreadedShear`: `blockShear_step`, `rank_eq_q_add_of_normalForm`,
  `rank_eq_q_iff_reduced_zero`.
