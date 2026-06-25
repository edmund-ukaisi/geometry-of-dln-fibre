# Statement card — (3,3,4) hdiv anchor `routeM334_box_diverges` FULLY sorry-free

**Status:** PROVED (sorry-free), integrated @b72c7364. Axiom footprint
`[propext, Classical.choice, Quot.sound, monomial_rlct]` — the single S2 leaf, no `sorryAx`.

## What is proved
`routeM334_box_diverges` — the R1 hdiv (lower-bound) anchor for the reduced widths `M = (3,3,4)`,
`t = (1,0)`: the achiever-path box integral `∫_{cubeBox} |routeMCore|^{−c'} = ⊤`, giving
`rlctAtOn(dlnLoss M 0) ≤ ½·minAdm` at the (3,3,4) binding node. The genuine geometric resolution
chart (Schur shear ∘ coupled `diag(b)` blow-up, `b = a·β`) is validated end-to-end.

## The change of variables (the soundness-critical content — reviewer-SURVIVED + Codex-corroborated)
- `phi334` is the genuine diffeo chart (`b = a·β` clears the Schur `a⁻¹` pole polynomially; one chart does
  both Layer-1 and the Layer-2 origin reach). `phi334_abs_det = |u₀|⁷·|u₁|²` — the genuine structural
  Jacobian (`pivotBlowupOnDeriv` u₀⁷ ∘ shear det 1 ∘ u₁²), matching the bundle weight `leafH334`.
- `phi334_cov` — the full c-o-v + two-sided `{u₁=0}` null-slice drop, via
  `lintegral_image_eq_lintegral_abs_det_fderiv_mul` + `ae_eq_set`.
- The outer coordinate reshape `Q334 = paramsEquivFlat ∘ pack334` contributes the trivial factor:
  `Q334CLM_abs_det : |det Q334| = 1` (it is a permutation of the 21 flat coordinates), via
  `measurePreserving_Q334CLM`.

## Reusable bedrock banked (`Foundations/ParamsReshapeMP.lean`, axiom-clean, 143 LoC)
The "bank once, share across all `hfin` per-node charts" reshape measure-preservation:
- `measurePreserving_paramsPack_of_flatIdxEquiv` — a coordinate reshape `pack : (Fin N → ℝ) → Params H`
  specified by an EXPLICIT computable slot bijection `e : Fin N ≃ FlatIdx H` (with `pack w q = w (e.symm q)`)
  is measure-preserving. The computable replacement for the opaque `Fintype.equivFin`; the `ParamsFlat222`
  `piCurry`/`arrowCongr'` pattern parametrised by `e`.
- `continuousLinearMap_abs_det_eq_one_of_measurePreserving` — an MP continuous ℝ-linear self-map of a
  finite-dim space has `|det| = 1` (unit-box Haar: `det ≠ 0` from MP + range-nullity, then the smul factor
  `ofReal|det⁻¹| = 1`).

The (3,3,4) instantiation (`fin21EquivFlatIdx334` + `hpack334` + `measurePreserving_pack334`) lives in
`RouteMLayerCoverGEL2.lean`.

## Reusable c-o-v template for the hfin per-node machinery
Schur-shear det-1 (`shear334Deriv` + BlockTriangular) · chain-rule composite det
(`ContinuousLinearMap.coe_comp` + `LinearMap.det_comp`) · outer-reshape `|det|=1` pull-out · the
`lintegral_image_…_abs_det_fderiv` + null-slice assembly. The single fact to share across binding nodes is
the reshape MP `|det Q|=1` (now banked).
