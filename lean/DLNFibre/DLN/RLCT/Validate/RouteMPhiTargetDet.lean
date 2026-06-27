import DLNFibre.DLN.RLCT.Validate.RouteMPhiFlatDet

/-!
# `RouteMPhiTargetDet` — the factored Jacobian determinant for an ARBITRARY target map

`RouteMPhiFlatDet` banks `composeFold_abs_det_leafH` (the det of `composeFold fs` itself) and
`phiFlat_abs_det_of_factored` (the det of the specific `phiFlat`, given a map equality). This module
factors out the GENERIC step: for ANY target `phi : (Fin N → ℝ) → (Fin N → ℝ)` with a factorization
`composeFold fs = phi`, the Jacobian determinant of `phi` is the per-factor det product
(`∏_j |u_j|^{leafH j}`, given the bookkeeping).

This is the det/cov compatibility step for the general structured achiever chart: take
`phi := phiFlatStructV M t ha hN` (rate already banked), and the bridge `composeFold fs = phiFlatStructV`
delivers `|det Dφ| = ∏_j |u_j|^{leafH j}` via this lemma.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (calculus + determinant; no S2).
-/

open scoped BigOperators

namespace DLNFibre.DLN.RLCT

/-- **`phi` has the factored fderiv** `(foldDerivList fs u).prod`, given `composeFold fs = phi`. -/
theorem phiTarget_hasFDerivAt_of_factored {N : ℕ} (phi : (Fin N → ℝ) → (Fin N → ℝ))
    (fs : List (ChartFactor N)) (hmap : composeFold fs = phi) (u : Fin N → ℝ) :
    HasFDerivAt phi ((foldDerivList fs u).prod) u := by
  rw [← hmap]; exact composeFold_hasFDerivAt fs u

/-- **The factored Jacobian determinant of an arbitrary target** `|det (fderiv phi u)| =
∏_j |u_j|^{leafH j}`, from a map equality `composeFold fs = phi` (which pins `fderiv phi u =
(foldDerivList fs u).prod`) + the per-factor det bookkeeping, via the banked telescope. The
generic det/cov step for any chart presented as a factor fold. -/
theorem phiTarget_abs_det_of_factored {N : ℕ} (phi : (Fin N → ℝ) → (Fin N → ℝ))
    (fs : List (ChartFactor N)) (hmap : composeFold fs = phi)
    (leafH : Fin N → ℕ) (u : Fin N → ℝ)
    (hdet : ((foldDerivList fs u).map
        (fun D : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) ↦ |LinearMap.det D.toLinearMap|)).prod
      = ∏ j, |u j| ^ (leafH j)) :
    |LinearMap.det (fderiv ℝ phi u).toLinearMap| = ∏ j, |u j| ^ (leafH j) := by
  rw [(phiTarget_hasFDerivAt_of_factored phi fs hmap u).fderiv,
    composeFold_abs_det fs u _ rfl, hdet]

end DLNFibre.DLN.RLCT
