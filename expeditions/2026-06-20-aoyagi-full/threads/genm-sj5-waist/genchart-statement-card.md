# Statement card — GENERAL max-pivot Schur chart change-of-variables (hole (c) step 1)

> **Claim.** For any pivot dimension `t` and residual shape `(r, c)`, and any continuous linear
> equivalence `E : (Fin N → ℝ) ≃L[ℝ] SchurInc t r c × R` presenting the flat ambient as the Schur
> increment space (blocks `(K,N,X,E_blk)`, `K : t×t` the pivot) times a remainder `R`, the max-pivot
> Schur chart `chart = conjBlockMap E schurFrameMap` (the banked Schur frame `S(K,N,X,E_blk) =
> (K, K·N, (X·K, X·K·N + E_blk))` conjugated into the flat ambient) satisfies, on the max-pivot sector
> `{u | (K(u)).det ≠ 0}` (`K(u) = ((E u).1.1)`), the change of variables
> `∫⁻ y in chart '' sector, g y = ∫⁻ u in sector, ofReal(|K(u).det|^(r+c)) · g (chart u)`
> for every `g`. At `t = 1` (rank-1 pivot `K = [p]`), `|K.det|^(r+c) = |p|^(r+c)`, the deep-layer
> waist-charge Jacobian; this generalizes the sorry-free `(3,2,3)` prototype `schurChart_cov`
> (`|det| = |p|³`, `t=1,r=1,c=2,N=6`).
>
> - **Lean:** `DLNFibre.DLN.RLCT.schurChartFactor_cov`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJWaistSchurChartGen.lean` @ `8d0eb6fb`)
>   (+ `schurFrameMap_conj_injOn`, `measurableSet_schurSector`, same file)
> - **Gloss.** The Lebesgue integral of any `g : (Fin N → ℝ) → ℝ≥0∞` over the image of the max-pivot
>   sector under the conjugated Schur chart equals the integral over the sector of the polynomial
>   Jacobian weight `ofReal(|((E u).1.1).det|^(r+c))` times `g` at the chart point. One ordinary
>   `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul` on the flat ambient `Fin N → ℝ`.
> - **Proved.** The CoV identity for arbitrary `(t, r, c, N)`, arbitrary CLE `E`, arbitrary `g`,
>   sorry-free, axiom footprint `[propext, Classical.choice, Quot.sound]`. The three inputs:
>   injectivity of the conjugated chart on the sector (`schurFrameMap_conj_injOn`, from banked
>   `schurFrameMap_inj_of_det_ne_zero_gen` + `E` bijective); measurability of the sector
>   (`measurableSet_schurSector`); the Jacobian `|det| = |K.det|^(r+c)` (banked `schurChartFactor_abs_det`
>   ← `schurFrameD_abs_det` ← `schurFrameDeriv_det`, block-triangular, NO variable-width `fin_cases`).
> - **Assumed.** `E` a continuous linear equiv `(Fin N → ℝ) ≃L SchurInc t r c × R` (the block-reshape
>   presentation); `R` a finite-dim real normed space. The sector `{K(u).det ≠ 0}` (max-pivot).
> - **Cited.** none (all Mathlib + banked repo lemmas, each named).
> - **Deferred.** The DOWNSTREAM steps that consume this CoV are NOT here: (2) the decoration seam
>   (`SJDecoration.integral` d=0/d≥1 split); (3) the L=0 bare-box compose (loss identity
>   `frobSq_mul_eq_sum_eigenvalues` + `qPeelIntegral_lt_top` + `waistCharge_eq_minAdm` → ½·minAdm),
>   which requires reconciling the SPECTRAL decomposition of the loss with the SCHUR-pivot chart
>   coordinates (two different decompositions of `A₁` — the genuinely-new analytic reconciliation);
>   the flag/shell recursion iterating this single peel; (4) reorientation + arity recursion (reversal
>   CoV, matrix-measure diamond) with the Γ-consume-before-hIH soundness; (5) `deeperFlagWaist_finite`
>   assembly. See the tide report.
> - **Structure & ideas observed (pen-and-paper, routeA cert + wall-assessment).** The literal
>   rectangular-SVD / Wishart eigenvalue density is a HEAVY Mathlib-v4.29 wall (no Stiefel, no Haar-on-O(s),
>   no Vandermonde density, no eigenvalue Jacobian). The MODERATE bypass is the max-pivot Schur-flag CoV:
>   at `t=1` this single peel is exactly the deep-layer chart; iterating (flag recursion) resolves the
>   residual down to `s=1`. Codex identified the `(3,2,3)` chart as the cheapest decisive de-risking test.
> - **Route (controller/formaliser).** The determinant that stalled the `(3,2,3)`→general step (a
>   variable-width triangular det, no `fin_cases`) is ENTIRELY BANKED in the achiever-chart pipeline
>   (`schurFrameDeriv_det = K.det^(r+c)`, block-triangular via `lowerTri_det`). Conjugate the banked
>   `schurFrameMap` into the flat ambient `Fin N → ℝ` via `conjBlockFactor` (which the achiever chart
>   already uses) — this sidesteps the `SchurInc`-product-measure diamond (nested products of `Matrix`
>   lack `IsAddHaarMeasure`; only single-level `Fin N → ℝ` has clean pi-Haar). Feed
>   `lintegral_image_eq_lintegral_abs_det_fderiv_mul` the conjugated `hasFDerivAt`, injectivity, and det.
> - **Status.** sorry-free (fidelity review pending).
