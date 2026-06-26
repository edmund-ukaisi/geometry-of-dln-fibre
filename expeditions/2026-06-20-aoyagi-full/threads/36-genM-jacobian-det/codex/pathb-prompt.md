# Lean 4 / Mathlib — can the RATE of a factored chart telescope WITHOUT the full entry-wise bridge?

SETUP. φ_flat : (Fin N → ℝ) → (Fin N → ℝ). routeMCore M x := dlnLoss M 0 (paramsEquivFlat M).symm x,
where paramsEquivFlat : Params M ≃ᵐ (Fin N → ℝ) is a pure reshape/reindex. dlnLoss M 0 P = ‖prod M P‖²
(squared Frobenius of the layer-product). I have BANKED:
- routeMCore_phiFlatStruct: routeMCore M (phiFlatStruct u) = u²·V, where phiFlatStruct u =
  paramsEquivFlat M (chartParamsGen u M t genBlkFlatStruct hle). [chartParamsGen s = reindex(chainA layer
  A_s); the rate is prod M (chartParamsGen) = u•H via the suffix-bridge/chain_telescope_zero.]
- composeFold fs : (Fin N → ℝ) → (Fin N → ℝ) — a product of full-ambient flat ChartFactors
  (radial, Schur_s, LDU_s, chain_s) reading DISJOINT slots (the same slots genBlkFlatStruct reads).
- composeFold_abs_det_leafH: |det (fderiv (composeFold fs) u)| = ∏|u_j|^{leafH j}. (DET done.)

THE ATOM (NodeAchieverChart) bundles ONE map phi with BOTH:
  leaf_integrand: references routeMCore M (phi u)   [RATE]
  cov:            references |det Dφ| = ∏|u_j|^{leafH}  [DET]
With phi := composeFold fs, DET is free, but leaf_integrand needs routeMCore M (composeFold fs u) = u²·V,
NOT banked.

PATH A (fallback): prove composeFold fs = phiFlatStruct (entry-wise stage induction over opaque widths
matching the factored flat product to paramsEquivFlat(chainA layers)), then transport
routeMCore_phiFlatStruct. The deep induction.

PATH B (preferred — want adjudicated): prove routeMCore M (composeFold fs u) = u²·V DIRECTLY by
re-running the chain telescope on the factors, avoiding the entry-wise bridge.

MY DOUBT about PATH B: routeMCore reads its arg via (paramsEquivFlat).symm — so routeMCore (composeFold
fs u) = dlnLoss M 0 ((paramsEquivFlat).symm (composeFold fs u)) = ‖prod M ((paramsEquivFlat).symm
(composeFold fs u))‖². To telescope this I must know the LAYERS of (paramsEquivFlat).symm (composeFold fs
u) — i.e. what Params M does composeFold fs u unflatten to. That IS the bridge (composeFold fs =
paramsEquivFlat ∘ (those layers)). So PATH B seems to REDUCE to PATH A unless composeFold fs's layers are
manifestly the chainA layers BY CONSTRUCTION.

QUESTIONS:
1. Is my doubt correct — does PATH B (rate of composeFold fs) NECESSARILY require identifying
   (paramsEquivFlat).symm (composeFold fs u)'s Params-layers (= the bridge), OR is there a genuine route
   that telescopes routeMCore through the factor composition without that identification?
2. If PATH B reduces to PATH A, is there a THIRD route: do NOT use composeFold fs for the chart at all —
   instead prove the DET of phiFlatStruct (the rate-side chart) directly, so ONE map (phiFlatStruct) has
   both rate (banked) and det? The det of phiFlatStruct = |det (fderiv (paramsEquivFlat ∘ chartParamsGen
   ∘ genBlkFlatStruct) u)|. paramsEquivFlat is linear (|det|=1). So I need |det (fderiv (chartParamsGen ∘
   genBlkFlatStruct) u)|. chartParamsGen ∘ genBlkFlatStruct : (Fin N → ℝ) → Params M. Its fderiv det...
   chainA is LINEAR in (C,W) for fixed N; chainQ CONSTANT in N; C = Bmat·chainQ + u•Rmat; Bmat=[K;XK];
   K from LDU (nonlinear). Is fderiv(chartParamsGen ∘ genBlkFlatStruct) a tractable per-layer product
   whose det telescopes to ∏|u_j|^{leafH}, REUSING the banked schurFrameDeriv_det/lduCoreDeriv_det block
   dets (NOT rebuilding them)? I.e. is there a clean "fderiv of the chain assembly = product of the
   per-layer block fderivs" that lets me apply the banked per-block dets? This would give BOTH fields on
   phiFlatStruct with NO bridge and NO composeFold detour.
3. Which of A / B / C is genuinely least work? Be concrete about where each one's hard step lives.

The endpoints (rate of phiFlatStruct; det of composeFold fs) are both banked. The reconciliation is the
last wall. Tell me the cleanest reconciliation. Be skeptical of PATH B if it just hides PATH A.
