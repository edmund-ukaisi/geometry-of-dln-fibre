import DLNFibre.DLN.RLCT.Validate.RouteMChartFactorFold
import Mathlib.LinearAlgebra.Determinant

/-!
# `RouteMLinearFactor` — a linear (constant-fderiv) `ChartFactor`

A continuous linear self-map `T : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)` as a `ChartFactor N` (its own
constant fderiv). The reshape/permutation factors of the achiever chart (`paramsEquivFlat`, `pack`,
the role-slot reshape) are all linear with `|det| = 1`; this packages them for `composeFold`.

* `linearFactor T` — the `ChartFactor N` of a CLM `T`.
* `linearFactor_abs_det` — `|det (D u)| = |det T|` (constant in `u`).

Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

variable {N : ℕ}

/-- **A linear `ChartFactor`** — a CLM `T` as a chart factor (its own constant fderiv). -/
noncomputable def linearFactor (T : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) : ChartFactor N where
  f := T
  D := fun _ => T
  hasD := fun u => T.hasFDerivAt

@[simp] theorem linearFactor_f (T : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) :
    (linearFactor T).f = T := rfl

@[simp] theorem linearFactor_D (T : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) (u : Fin N → ℝ) :
    (linearFactor T).D u = T := rfl

/-- **The linear factor's abs-det** `|det (D u)| = |det T|` (constant). -/
theorem linearFactor_abs_det (T : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) (u : Fin N → ℝ) :
    |LinearMap.det ((linearFactor T).D u).toLinearMap| = |LinearMap.det T.toLinearMap| := by
  rw [linearFactor_D]

end DLNFibre.DLN.RLCT
