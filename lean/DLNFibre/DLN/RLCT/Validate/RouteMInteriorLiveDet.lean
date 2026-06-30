import DLNFibre.DLN.RLCT.Validate.RouteMKLens

/-!
# `RouteMInteriorLiveDet` — H2b-i: the K-LDU lens Jacobian abs-det (the route-independent atom)

The genuinely-NEW, route-independent determinant atom for the R1-LOWER interior abs_det keystone:
the per-matrix LDU lens `kLens`'s Fréchet-Jacobian abs-det is the diagonal-pivot monomial

  `|det (fderiv ℝ kLens K)| = ∏_i |q_i|^{2(t−1−i)}`,   `q = (matrixSplit K).2.1`.

`kLens K = matrixSplit.symm (lduCoreMap (matrixSplit K))` (`RouteMKLens`), so its fderiv is the
linear-conjugate `matrixSplit.symm ∘ lduCoreD ∘ matrixSplit` of the banked LDU-core differential
`lduCoreD` (`RouteMFactorMaps`), and `LinearMap.det_conj` cancels the two `matrixSplit` factors,
leaving the banked `lduCoreD_abs_det = ∏_i |q_i|^{2(t−1−i)}`.

This is the per-K-core building block of the full-ambient `kLDU` Jacobian det (the lens acts as
`kLens` on each per-boundary K-core block and as the identity on every spectator coordinate). It is
needed under ANY shape of the final `interiorLive_abs_det` assembly (the radial/eihd split does not
touch the LDU-core exponents), so it is built standalone here.

Axiom-clean `[propext, Classical.choice, Quot.sound]` target (calculus chain rule + determinant of a
conjugation; no analysis beyond the banked `lduCoreMap_hasFDerivAt`).
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

/-! ## `kLens` as a conjugate of `lduCoreMap`; its Fréchet derivative -/

/-- `kLens = matrixSplit.symm ∘ lduCoreMap ∘ matrixSplit` as a pointwise function identity. -/
theorem kLens_eq_conj {t : ℕ} (K : Matrix (Fin t) (Fin t) ℝ) :
    kLens K = (matrixSplit (t := t)).symm (lduCoreMap (matrixSplit (t := t) K)) := rfl

/-- **`kLens` has Fréchet derivative the conjugate `matrixSplit.symm ∘ lduCoreD (split K) ∘ matrixSplit`**
(the composite `.comp` auto-builds). The chain rule through the linear `matrixSplit`, the banked
nonlinear `lduCoreMap_hasFDerivAt`, and the linear `matrixSplit.symm`. -/
theorem kLens_hasFDerivAt {t : ℕ} (K : Matrix (Fin t) (Fin t) ℝ) :
    HasFDerivAt (kLens (t := t))
      (((matrixSplit (t := t)).symm.toContinuousLinearMap.comp
          (lduCoreD (matrixSplit (t := t) K))).comp
        (matrixSplit (t := t)).toContinuousLinearMap)
      K := by
  have hsplit : HasFDerivAt (⇑(matrixSplit (t := t)))
      (matrixSplit (t := t)).toContinuousLinearMap K :=
    (matrixSplit (t := t)).toContinuousLinearMap.hasFDerivAt
  have hcore : HasFDerivAt lduCoreMap (lduCoreD (matrixSplit (t := t) K))
      (matrixSplit (t := t) K) := lduCoreMap_hasFDerivAt _
  have hsymm : HasFDerivAt (⇑(matrixSplit (t := t)).symm)
      (matrixSplit (t := t)).symm.toContinuousLinearMap
      (lduCoreMap (matrixSplit (t := t) K)) :=
    (matrixSplit (t := t)).symm.toContinuousLinearMap.hasFDerivAt
  -- `kLens = matrixSplit.symm ∘ (lduCoreMap ∘ matrixSplit)`; `.comp` builds the composite fderiv,
  -- whose CLM `.comp` is associated as `symm' ∘ (lduCoreD ∘ split')`; reassociate to match the
  -- stated `(symm' ∘ lduCoreD) ∘ split'`.
  have h := hsymm.comp K (hcore.comp K hsplit)
  rwa [← ContinuousLinearMap.comp_assoc] at h

/-- **H2b-i (per K-core) — the LDU lens Jacobian abs-det is the diagonal-pivot monomial**:
`|det (fderiv ℝ kLens K)| = ∏_i |q_i|^{2(t−1−i)}` with `q = (matrixSplit K).2.1`. The fderiv is the
linear-conjugate of the banked `lduCoreD`; `LinearMap.det_conj` cancels the `matrixSplit` factors,
then `lduCoreD_abs_det`. -/
theorem kLens_abs_det {t : ℕ} (K : Matrix (Fin t) (Fin t) ℝ) :
    |LinearMap.det (fderiv ℝ (kLens (t := t)) K).toLinearMap|
      = ∏ i : Fin t, |(matrixSplit (t := t) K).2.1 i| ^ (2 * ((t : ℕ) - 1 - (i : ℕ))) := by
  rw [(kLens_hasFDerivAt K).fderiv]
  -- the fderiv `toLinearMap` is `(↑matrixSplit.symm ∘ₗ ↑lduCoreD(split K)) ∘ₗ ↑matrixSplit`;
  -- reassociate to `↑e.symm ∘ₗ f ∘ₗ ↑e.symm.symm` (`e = matrixSplit`), then `det_conj f e.symm`.
  rw [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp,
    LinearMap.coe_toContinuousLinearMap, LinearMap.coe_toContinuousLinearMap,
    LinearMap.comp_assoc]
  rw [show ((matrixSplit (t := t)) : Matrix (Fin t) (Fin t) ℝ ≃ₗ[ℝ] LDUParam t).toLinearMap
      = ((matrixSplit (t := t)).symm).symm.toLinearMap from rfl]
  rw [LinearMap.det_conj (lduCoreD (matrixSplit (t := t) K)) (matrixSplit (t := t)).symm,
    lduCoreD_abs_det]

end DLNFibre.DLN.RLCT
