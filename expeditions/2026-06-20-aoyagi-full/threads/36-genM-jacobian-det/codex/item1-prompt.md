# Lean 4 / Mathlib v4.29: the bijective coordinatization (item 1) for the general DLN achiever chart det — architectural fork

## State
- BANKED: the RATE chart `chartParamsFlat M t … x := chartParamsGen (x p) M t (genBlkFlat x) hle : Params M`,
  where `chartParamsGen`'s layers are `chainA(N_k)(W_k)(C(k+1))` (the abstract chain). `genBlkFlat` reads
  block data from flat coords via a MODULAR index (`flatIdxOf`, NOT bijective — rate-side only). The rate
  `routeMCore (paramsEquivFlat ∘ chartParamsFlat) = u²·V` is banked.
- BANKED det algebra: `composeFold_abs_det` (prefix-fold telescope over `ChartFactor` = full-ambient CLM +
  HasFDerivAt), `schurFrame_abs_det = |det K|^{r+c}` (on `SchurInc t r c`), `lduCoreDeriv_det = ∏q^{2(t-1-i)}`
  (on `LDUParam t`), `chainUnit_det = 1`, `pivotBlowupOn_abs_det = |x_p|^{card-1}`.
- The (3,3,3,3) ANCHOR did it as `phi3333 = Q3333 ∘ T3333`, `T3333 = Frame3333 ∘ Kparam3333` (hand-transcribed
  flat maps `(Fin 27 → ℝ) → (Fin 27 → ℝ)`), `det_comp` on the composition.

## The goal
`phiFlat_abs_det : |det Dφ_flat| = ∏_j |u_j|^{leafH j}` ∀M, via `composeFold_abs_det` over the
Schur/LDU/chain/radial factors. Item 1 = a determinant-ready bijective coordinatization `Fin N ≃ Σ (boundary,
role)`; items 2-3 = full-ambient factor conjugates + `D(chart) = composeFold(factors)`.

## The cert's coordinate subtlety (verified `ninputs = flatDim` per witness)
`flatDim M = ∑_s M_{s.castSucc}·M_{s.succ}`. The cert's free params per boundary s: Schur `K_s`(t²),`X_s`(r·t),
`N_s`(t·c); LDU `q,l,u` (REPARAMETRIZE `K_s` — `K_s = L·diag(q)·U`, so `K_s`'s t² free coords ARE the LDU
`q`(t),`l`,`u`); chain lift `W_{s+1}` (c·M_{s+1}); plus ONE radial `u` that REPLACES one distinguished
residual slot (fixed =1). So the accounting `∑ block-dims + 1(radial) − 1(fixed residual) = flatDim` is
NONTRIVIAL — it's not a clean `⊕`.

## THE ARCHITECTURAL FORK (want your read)
To reach `phiFlat_abs_det`, two routes:

**(A) Reconcile the existing `chainA` chart.** Build a bijective `Fin N ≃ Σ(boundary,role)` coordinatization,
re-decode `genBlkFlat` bijectively, then prove `D(chartParamsGen ∘ Bflat_bijective) = composeFold(Schur/LDU/
chain/radial factors)` — the `chainA`-vs-frame deriv equality over opaque widths (Codex's flagged true
bottleneck, item 3). KEEPS the banked rate (the rate chart is `chartParamsGen ∘ Bflat`).

**(B) Build the chart FRESH as the factor product.** Define `φ_flat := Q ∘ composeFold(Schur/LDU/chain/radial)`
directly (the (3,3,3,3) `Q ∘ Frame ∘ Kparam` generalized to opaque widths), get its det FREE from
`composeFold_abs_det` + per-factor dets. Then TRANSFER THE RATE to this fresh `φ_flat` — re-proving
`routeMCore (φ_flat u) = u²·V` either (b1) by a NEW keystone `φ_flat = paramsEquivFlat ∘ chartParamsGen ∘ Bflat`
(same reconciliation as A, just det-first), or (b2) by re-deriving the rate telescope on the factor product
directly (re-runs the landed telescope/cast work).

## QUESTIONS
1. Is there ANY route to `phiFlat_abs_det` that AVOIDS the `chainA`-vs-Schur-frame reconciliation (item 3)
   entirely? E.g. is the rate identity provable DIRECTLY on the Schur-frame factor product `φ_flat`
   (route b2) WITHOUT going through `chartParamsGen`/`chainA` — i.e. is `prod M (decode(φ_flat u)) = u·H`
   provable from the Schur-frame/LDU/chain structure directly (the cert's telescoping `A^(0)⋯A^(L-1) = u·H`
   IS stated on the `C_s`/chaining, which ARE the Schur frames)? If so, route B avoids the reconciliation —
   the rate AND the det both come from the factor product, and `chainA`/`chartParamsGen` is never involved
   in the det chart.
2. For item 1 specifically: what is the cleanest Lean shape for the bijective `Fin N ≃ Σ(boundary,role)`
   given the nontrivial `+1 radial −1 fixed-residual` accounting? Is it `(Σ s, blockRole s) ≃ Fin N` via
   `Fintype.equivFin` (cardinality `flatDim`), with `blockRole s` a sum type of the K/X/N/q/l/u/W slots?
   Does the "one fixed residual" break the clean `Fintype.card = flatDim` (making it NOT a bijection of the
   full flat space)?
3. Bottom line: is item 1 (+ the route to phiFlat_abs_det) a bounded build on the banked machinery, or is
   the `chainA`/Schur reconciliation (or the radial-residual accounting) a genuine multi-pass wall? If route
   B avoids item 3, is route B the recommendation? Name the ONE sub-step that is the true bottleneck and
   whether it's bounded.

Be skeptical and concrete. I want to know whether to push item 1 now (and which route), or report the
reconciliation as the precise residual.
