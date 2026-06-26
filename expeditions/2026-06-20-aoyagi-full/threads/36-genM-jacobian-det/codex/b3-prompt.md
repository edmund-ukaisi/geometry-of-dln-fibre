# Lean 4 / Mathlib v4.29: B3 phiFlat_abs_det — the global chart-equality over opaque widths. Sharpest route?

## Banked (sorry-free)
- Per-factor dets (all on `LinearMap.det`): `schurFrame_abs_det : |det (schurFrameDeriv X K N)| = |det K|^{r+c}`
  (on the increment space `SchurInc t r c = Matrix(t,t)×(Matrix(t,c)×(Matrix(r,t)×Matrix(r,c)))`);
  `lduCoreDeriv_det : det = ∏ q_i^{2(t−1−i)}` (on `LDUParam t`); `chainUnit_det = 1` (on
  `Matrix(c,m')×Matrix(t,m')`); `pivotBlowupOn_abs_det = |x p|^{card−1}` (full-ambient `Fin N → ℝ`).
- `general_composed_clm_abs_det (N) (fs : List ((Fin N→ℝ)→L(Fin N→ℝ))) (m) (hfac) : |det (fs.prod)| = m.prod`
  — telescopes a LIST of FULL-AMBIENT CLM factors, given each factor's abs-det.
- The rate chart `chartParamsFlat M t … x := chartParamsGen (x p) M t (genBlkFlat x) hle : Params M`, where
  `chartParamsGen`'s layers are `Matrix.reindex (chainOfMt …).toChain.A s.val` and `A k = chainA(N_k)(W_k)
  (C(k+1))` (the abstract chain layer). The RATE `routeMCore (paramsEquivFlat ∘ chartParamsFlat) = u²·V` is
  banked. B2 entry-law bricks: `chainA_apply_castAdd/natAdd`, `chainQ_apply_castAdd/natAdd` (opaque widths).

## The B3 goal
`phiFlat_abs_det : |det D(paramsEquivFlat M ∘ chartParamsFlat …)| = ∏_j |u_j|^{leafH j}` (leafH p = minAdm−1,
the q-spectator exponents elsewhere), ∀M + descent t.

## The structural obstacle (the genuine wall)
The per-factor dets live on DIFFERENT spaces (`SchurInc t r c`, `LDUParam t`, …), NOT on `Fin N → ℝ`. To use
`general_composed_clm_abs_det`, every factor must be a FULL-AMBIENT `(Fin N → ℝ) →L (Fin N → ℝ)` reading its
block coords from the N flat slots, identity elsewhere — AND the product must EQUAL `D(paramsEquivFlat ∘
chartParamsFlat)` (the global chart-equality). That requires:
1. A `Fin N ≃ ⊕_s (block spaces of boundary s)` flat coordinatization (the `paramsEquivFlat`/`pack` reshape
   generalized to split each layer into its Schur/LDU/chain/radial sub-blocks), over OPAQUE `Wext`/`Text`
   widths.
2. Each Phase-A factor (on `SchurInc`/`LDUParam`) conjugated into a full-ambient `Fin N → ℝ` CLM via that
   coordinatization (the det is conjugation-invariant, so the value survives — but the embedding + the
   `HasFDerivAt` of the composite + the prefix-pullback all need building).
3. The chart `chartParamsFlat` (built from `chainA`/`chainQ`) proven EQUAL to `Q · ∏ S_s ∘ Ldu_s ∘ chain_s ∘
   radial` (the flat-frame product) — the `chainA`-vs-frame reconciliation over opaque widths.

## QUESTIONS
1. Is step 3 (the global chart-equality, `chainA`-chart = flat-frame-product) genuinely unavoidable, or is
   there a route that gets `|det Dφ_flat|` WITHOUT proving the two charts equal as maps — e.g.:
   (a) Compute `D(chartParamsGen ∘ genBlkFlat)` as a single block-triangular linear map on `Fin N → ℝ`
       (the blocks = the per-boundary block-coordinate groups), and show its det = ∏ (per-block det) by ONE
       `BlockTriangular`/`det_prodMap` argument — where each diagonal block IS (conjugate to) a Schur/LDU
       factor, WITHOUT building the factors as separate full-ambient CLMs or proving a chart-product equality?
       I.e. differentiate the actual chart once and read off the block structure, reusing the Phase-A
       per-block dets as the diagonal-block values.
   (b) Is the `D(chartParamsFlat)` Jacobian block-triangular in the boundary index `s` (later boundaries'
       blocks feed earlier layers via `C_{s+1}`), with diagonal blocks = (Schur_s ⊕ LDU_s ⊕ chain_s) and the
       radial? If so, `LinearMap.det` of a block-triangular map = ∏ diagonal-block dets — could that be the
       spine, avoiding the List/prefix-fold AND the chart-product equality?
2. If the block-triangular-direct route (1a/1b) is viable: what is the cleanest Lean shape — a
   `BlockTriangular` over a `Fin N` grading by boundary+block-role, with the diagonal blocks identified (via
   `det_conj` / `det_prodMap`) as the Phase-A factors? Is THAT a bounded build (the grading + the diagonal
   identifications) or still multi-pass?
3. If NEITHER avoids the multi-pass coordinatization: is the honest call to (i) bank the abstract
   `ChartFactor` prefix-fold scaffold + telescope (reusable, bounded) and report the per-M factor
   construction + global chart-equality as the precise residual, or (ii) something else? What is the ONE
   sub-step that is the true bottleneck?

Be skeptical and concrete. The det side is "one scaffold from complete" per the controller; I need to know
if that scaffold is a bounded build or a genuine multi-pass over opaque widths, and the sharpest route.
