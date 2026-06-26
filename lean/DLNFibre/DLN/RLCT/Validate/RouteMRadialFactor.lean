import DLNFibre.DLN.RLCT.Validate.RouteMChartFactorFold
import DLNFibre.DLN.RLCT.Foundations.S1G5Charts

/-!
# `RouteMRadialFactor` — Phase B item 2: the radial-blow-up `ChartFactor` (the first flat factor)

The radial blow-up `pivotBlowupOn` packaged as a `ChartFactor` (`RouteMChartFactorFold`) — the first and
simplest of the full-ambient flat-coordinate factors of the achiever chart's factor product
`Q ∘ composeFold(Schur/LDU/chain/radial)` (item 2 of the det route, B+b1). The radial is already a
full-ambient `(Fin N → ℝ) → (Fin N → ℝ)` map with a banked `HasFDerivWithinAt` (`pivotBlowupOn_hasFDerivWithinAt`)
and a banked determinant (`pivotBlowupOnDeriv_det = |x_p|^{card−1}`), so it slots directly into
`ChartFactor`/`composeFold` with no coordinatization work.

* `radialFactor active p` — the radial blow-up as a `ChartFactor N`.
* `radialFactor_abs_det` — `|det (D u)| = |u_p|^{card−1}` (the radial Jacobian, `= |u_p|^{minAdm−1}` at
  the achiever center `card = minAdm`).

The remaining item-2 factors (Schur, LDU, chain) are NOT yet full-ambient: `schurFrameDeriv` lives on the
increment space `SchurInc t r c`, `lduCoreDeriv` on `LDUParam t`, `chainUnitMap` on a product matrix space.
Each needs conjugation into `(Fin N → ℝ) →L (Fin N → ℝ)` via the item-1 `chartIdxEquiv` coordinatization
(the genuine remaining item-2 work; the radial here is the template `ChartFactor` shape).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (calculus + determinant; no S2).
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators

/-- **The radial blow-up as a `ChartFactor`** — `pivotBlowupOn active p` with its banked fderiv
`pivotBlowupOnDeriv` and `HasFDerivAt` (from `pivotBlowupOn_hasFDerivWithinAt` on `Set.univ`). The first
flat-coordinate factor of the achiever chart's factor product. -/
noncomputable def radialFactor {N : ℕ} (active : Finset (Fin N)) (p : Fin N) : ChartFactor N where
  f := pivotBlowupOn active p
  D := pivotBlowupOnDeriv active p
  hasD := fun u => hasFDerivWithinAt_univ.mp (pivotBlowupOn_hasFDerivWithinAt active p Set.univ u)

@[simp] theorem radialFactor_f {N : ℕ} (active : Finset (Fin N)) (p : Fin N) :
    (radialFactor active p).f = pivotBlowupOn active p := rfl

@[simp] theorem radialFactor_D {N : ℕ} (active : Finset (Fin N)) (p : Fin N) :
    (radialFactor active p).D = pivotBlowupOnDeriv active p := rfl

/-- **The radial factor's abs-det** `|det (D u)| = |u_p|^{active.card − 1}` (the codim-`active.card`
radial blow-up Jacobian; `= |u_p|^{minAdm − 1}` at the achiever center `active.card = minAdm`). The radial
contribution to the `composeFold_abs_det` telescope. -/
theorem radialFactor_abs_det {N : ℕ} (active : Finset (Fin N)) (p : Fin N) (hp : p ∈ active)
    (u : Fin N → ℝ) :
    |LinearMap.det ((radialFactor active p).D u).toLinearMap| = |u p| ^ (active.card - 1) := by
  show |LinearMap.det (pivotBlowupOnDeriv active p u).toLinearMap| = _
  rw [show LinearMap.det (pivotBlowupOnDeriv active p u).toLinearMap
        = (pivotBlowupOnDeriv active p u).det from rfl,
    pivotBlowupOnDeriv_det active p hp, abs_pow]

/-- Non-vacuity: a single-factor `composeFold [radialFactor active p]` has the radial fderiv and abs-det
`|u_p|^{card−1}` (the `ChartFactor`/`composeFold` interface fires on the radial). -/
example {N : ℕ} (active : Finset (Fin N)) (p : Fin N) (hp : p ∈ active) (u : Fin N → ℝ) :
    |LinearMap.det ((foldDerivList [radialFactor active p] u).prod).toLinearMap|
      = |u p| ^ (active.card - 1) * 1 := by
  rw [composeFold_abs_det [radialFactor active p] u [|u p| ^ (active.card - 1)] (by
    simp only [foldDerivList_cons, foldDerivList_nil, List.map_cons, List.map_nil,
      composeFold_nil, id_eq]
    rw [radialFactor_abs_det active p hp])]
  simp [List.prod_cons, List.prod_nil]

end DLNFibre.DLN.RLCT
