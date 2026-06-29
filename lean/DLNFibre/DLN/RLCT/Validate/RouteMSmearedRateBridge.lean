import DLNFibre.DLN.RLCT.Validate.RouteMSmearedTelescope
import DLNFibre.DLN.RLCT.Validate.RouteMExtraction

/-!
# `RouteMSmearedRateBridge` — `routeMCore` rate from a COLLAPSED deep product (the chart consumer)

The bridge from the abstract telescope (`RouteMSmearedTelescope`) to the genuine `routeMCore`, at the
loss level. `routeMCore M x = dlnLoss M 0 ((paramsEquivFlat M).symm x) = ∑ᵢⱼ (prod M …)ᵢⱼ²`, so once the
chart supplies the deepest product in COLLAPSED form `prod M (chart params) = z • X` (the telescope's
`z • (P₁·H̄)`, the shear having cancelled), the rate is immediate: `routeMCore = z²·‖X‖²`.

This is the cast-free consumer of the smeared chart's telescoping eval: the dependent-`Fin` width
bookkeeping lives entirely in producing `prod M (chart params) = z • X` (the chart bridge / the named
gap), NOT in deriving the rate from it. With `X = P₁·H̄`, `U := ‖X‖²_F` is the `z`-free polynomial unit.

* `routeMCore_eq_frobeniusSq_prod` — the loss-form identity `routeMCore M x = ∑ᵢⱼ (prod M …)ᵢⱼ²`.
* `routeMCore_rate_of_prod_collapsed` — `prod M (chart) = z • X ⟹ routeMCore M (φ) = z²·‖X‖²`.
-/

open Matrix MeasureTheory
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The loss-form identity** `routeMCore M x = ∑ᵢⱼ (prod M ((paramsEquivFlat M).symm x))ᵢⱼ²`. Unfolds
`routeMCore = dlnLoss M 0 ∘ symm` and `dlnLoss M 0 A = ∑ᵢⱼ ((prod M A − 0)ᵢⱼ)²` (`sub_zero`). -/
theorem routeMCore_eq_frobeniusSq_prod (M : Fin (L + 1) → ℕ) (x : Fin (routeMAmbient M) → ℝ) :
    routeMCore M x
      = ∑ i, ∑ j, (prod M ((paramsEquivFlat M).symm x) i j) ^ 2 := by
  rw [routeMCore, dlnLoss]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [Matrix.sub_apply]
  simp only [Pi.zero_apply, Matrix.zero_apply, sub_zero]

/-- **The smeared rate from a collapsed product.** If the chart's deepest product is the pure radial
`prod M ((paramsEquivFlat M).symm (φ u)) = z • X` (the telescope collapse, shear cancelled), then
`routeMCore M (φ u) = z²·‖X‖²_F`. The cast-free rate the `NodeAchieverChart`/contract consume, with
`U = ‖X‖²_F` (`= ‖P₁·H̄‖²` when `X = P₁·H̄`). -/
theorem routeMCore_rate_of_prod_collapsed (M : Fin (L + 1) → ℕ)
    (φ : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ))
    (u : Fin (routeMAmbient M) → ℝ) (z : ℝ)
    (X : Matrix (Fin (M 0)) (Fin (M (Fin.last L))) ℝ)
    (hcollapse : prod M ((paramsEquivFlat M).symm (φ u)) = z • X) :
    routeMCore M (φ u) = z ^ 2 * ∑ i, ∑ j, (X i j) ^ 2 := by
  rw [routeMCore_eq_frobeniusSq_prod, hcollapse, frobeniusSq_smul]

end DLNFibre.DLN.RLCT
