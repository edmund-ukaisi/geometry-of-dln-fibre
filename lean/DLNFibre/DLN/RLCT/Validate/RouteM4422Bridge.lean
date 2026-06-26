import DLNFibre.DLN.RLCT.Validate.RouteM4422
import DLNFibre.DLN.RLCT.Validate.RouteMLinearFactor
import DLNFibre.DLN.RLCT.Validate.RouteMRadialFactor
import DLNFibre.DLN.RLCT.Validate.RouteMPhiTargetDet

/-!
# `RouteM4422Bridge` — VALIDATE-SMALL-FIRST: the `(4,4,2,2)` chart AS a factor fold

Before building the general OPTION-1 bridge (`composeFold fs = phiFlatStructV` over opaque widths), this
module validates the factor-fold → real-chart route on the concrete `(4,4,2,2)` anchor: the banked
`phi4422 = paramsEquivFlat ∘ pack4422 ∘ pb4422 = Q4422 ∘ pb4422` (with `Q4422` LINEAR, `|det| = 1`, and
`pb4422 = pivotBlowupOn {0,1,2,3} 0` the radial blow-up) is exactly

  `composeFold [linearFactor Q4422CLM, radialFactor {0,1,2,3} 0]`.

Then the GENERIC `phiTarget_abs_det_of_factored` (consumed by the achiever chart's `cov`) delivers the
chart Jacobian `|det Dφ4422| = ∏_j |u_j|^{leafH4422 j} = |u 0|³` — matching the banked direct det
(`phi4422_abs_det` route). This confirms the factor-fold/det infrastructure (`composeFold`,
`composeFold_abs_det`, `phiTarget_abs_det_of_factored`, `linearFactor`, `radialFactor`) wires to a real
achiever chart end-to-end, on the cleanest anchor (a pure radial blow-up; no Schur/LDU).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (calculus + determinant; no S2).
-/

open scoped BigOperators

namespace DLNFibre.DLN.RLCT

/-- **The `(4,4,2,2)` chart as a 2-factor fold**: `phi4422 = composeFold [linearFactor Q4422CLM,
radialFactor {0,1,2,3} 0]`. The radial blow-up runs first (rightmost), then the linear reshape
`Q4422 = paramsEquivFlat ∘ pack4422`. -/
theorem phi4422_eq_composeFold :
    composeFold [linearFactor Q4422CLM, radialFactor ({0, 1, 2, 3} : Finset (Fin 28)) 0]
      = phi4422 := by
  funext u
  rw [composeFold_cons, composeFold_cons, composeFold_nil, Function.comp_apply,
    Function.comp_apply, id_eq, linearFactor_f, radialFactor_f]
  -- `Q4422CLM (pb4422 u) = phi4422 u`: pb4422 = pivotBlowupOn, Q4422 = paramsEquivFlat ∘ pack4422,
  -- phi4422 = paramsEquivFlat ∘ chartParams4422 = paramsEquivFlat ∘ pack4422 ∘ pb4422.
  change Q4422CLM (pivotBlowupOn ({0, 1, 2, 3} : Finset (Fin 28)) 0 u) = phi4422 u
  rw [show (pivotBlowupOn ({0, 1, 2, 3} : Finset (Fin 28)) 0 u) = pb4422 u from rfl]
  have hQ : Q4422CLM (pb4422 u) = paramsEquivFlatCLE M4422 (pack4422CLM (pb4422 u)) := rfl
  rw [hQ, paramsEquivFlatCLE_coe, pack4422CLM_coe, phi4422, ← chartParams4422_eq_pack_pb]

/-- **The factor-fold det bookkeeping for `(4,4,2,2)`**: the per-factor abs-det product of the 2-factor
fold is `∏_j |u_j|^{leafH4422 j}` — the linear factor contributes `|det Q4422CLM| = 1`, the radial
factor contributes `|u 0|^{4−1} = |u 0|³ = ∏_j |u_j|^{leafH4422 j}`. -/
theorem foldDet_4422_eq (u : Fin 28 → ℝ) :
    ((foldDerivList [linearFactor Q4422CLM, radialFactor ({0, 1, 2, 3} : Finset (Fin 28)) 0] u).map
        (fun D : (Fin 28 → ℝ) →L[ℝ] (Fin 28 → ℝ) ↦ |LinearMap.det D.toLinearMap|)).prod
      = ∏ j, |u j| ^ (leafH4422 j) := by
  simp only [foldDerivList_cons, foldDerivList_nil, composeFold_cons, composeFold_nil, id_eq,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [linearFactor_abs_det, Q4422CLM_abs_det,
    radialFactor_abs_det _ _ (by decide) u, leafH4422_prod_eq]
  rw [show ({0, 1, 2, 3} : Finset (Fin 28)).card = 4 from by decide]
  norm_num

/-- **The `(4,4,2,2)` chart Jacobian via the GENERIC factor-fold det** `|det Dφ4422| =
∏_j |u_j|^{leafH4422 j} = |u 0|³` — `phiTarget_abs_det_of_factored` consumed by the achiever chart's
`cov` field, validated on the concrete anchor. (Matches the banked direct det route.) -/
theorem phi4422_abs_det_via_fold (u : Fin 28 → ℝ) :
    |LinearMap.det (fderiv ℝ phi4422 u).toLinearMap| = ∏ j, |u j| ^ (leafH4422 j) :=
  phiTarget_abs_det_of_factored phi4422
    [linearFactor Q4422CLM, radialFactor ({0, 1, 2, 3} : Finset (Fin 28)) 0]
    phi4422_eq_composeFold leafH4422 u (foldDet_4422_eq u)

end DLNFibre.DLN.RLCT
