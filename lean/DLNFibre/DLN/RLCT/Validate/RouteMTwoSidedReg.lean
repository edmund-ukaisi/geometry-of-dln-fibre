import DLNFibre.DLN.RLCT.Validate.RouteMStairTwoSided
import DLNFibre.DLN.RLCT.Foundations.ParamsReshapeMP

/-!
# `RouteMTwoSidedReg` — the `hreg` discharge for the two-sided staircase conjugacy

The two-sided staircase keystone `RouteMStairTwoSided.stairMap_abs_det_twoConj` carries one
volume hypothesis: `hreg : |det (eOut.symm ∘ eIn)| = 1`, the input/output regauge factor is
abs-det-`1`. The decorrelated review flagged this as the riskiest sub-goal. It is in fact the
LEANEST: when `eIn` and `eOut` are coordinate-regrouping `ContinuousLinearEquiv`s (the role-split
engine `RouteMRoleCLE` builds them from `piCongrLeft`/`sumPiEquivProdPi`, which are measure-preserving
coordinate permutations), the COMPOSITE `eOut.symm ∘ eIn` is a measure-preserving self-map of the flat
space `Fin (flatDim M) → ℝ`, so its abs-det is `1` by the banked
`continuousLinearMap_abs_det_eq_one_of_measurePreserving` (the same spine `QMcle_abs_det` uses). No
comparison of `eIn` vs `eOut` is needed — the composite alone is measure-preserving.

* `hreg_of_measurePreserving_comp` — `hreg` from the composite endo `eOut.symm ∘ eIn` being
  measure-preserving on the flat space.

The eventual concrete `eIn`/`eOut` (the role-split CLEs into `StairProd V 2`) discharge `hreg` by
exhibiting their composite as a chain of `piCongrLeft`/`sumPiEquivProdPi` measure-preserving maps.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (the banked MP→|det|=1 spine; no analysis).
-/

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace DLNFibre.DLN.RLCT

universe u

variable {L : ℕ}

/-- **`hreg` from a measure-preserving regauge composite.** Let `E = Fin N → ℝ` be the flat space and
`eIn eOut : E ≃ₗ StairProd V n` two layer-collecting linear equivs. If the regauge endomorphism
`eOut.symm ∘ eIn : E →ₗ E` agrees (as a function) with a measure-preserving self-map of `E`, then the
two-sided keystone's `hreg` hypothesis holds. The composite of the coordinate-regrouping CLEs is such
a map (each `piCongrLeft`/`sumPiEquivProdPi` factor is measure-preserving). -/
theorem hreg_of_measurePreserving_comp {N n : ℕ}
    (V : ℕ → Type) [∀ k, AddCommGroup (V k)] [∀ k, Module ℝ (V k)]
    [∀ k, FiniteDimensional ℝ (V k)]
    (eIn eOut : (Fin N → ℝ) ≃ₗ[ℝ] StairProd V n)
    (hMP : MeasurePreserving
      (((eOut.symm : StairProd V n →ₗ[ℝ] (Fin N → ℝ))
          ∘ₗ (eIn : (Fin N → ℝ) →ₗ[ℝ] StairProd V n)) : (Fin N → ℝ) → (Fin N → ℝ))
      (volume : Measure (Fin N → ℝ)) volume) :
    |LinearMap.det ((eOut.symm : StairProd V n →ₗ[ℝ] (Fin N → ℝ))
        ∘ₗ (eIn : (Fin N → ℝ) →ₗ[ℝ] StairProd V n))| = 1 := by
  -- the regauge composite is a continuous ℝ-linear endo of the flat space; apply the MP→|det|=1 spine
  set g : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) :=
    (eOut.symm : StairProd V n →ₗ[ℝ] (Fin N → ℝ)) ∘ₗ (eIn : (Fin N → ℝ) →ₗ[ℝ] StairProd V n) with hg
  -- promote `g` to a `ContinuousLinearMap` (finite-dimensional domain ⟹ continuous)
  set gC : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) := LinearMap.toContinuousLinearMap g with hgC
  have hcoe : (gC : (Fin N → ℝ) → (Fin N → ℝ)) = (g : (Fin N → ℝ) → (Fin N → ℝ)) :=
    LinearMap.coe_toContinuousLinearMap' g
  have hMP' : MeasurePreserving (gC : (Fin N → ℝ) → (Fin N → ℝ))
      (volume : Measure (Fin N → ℝ)) volume := by rw [hcoe]; exact hMP
  have hdet := continuousLinearMap_abs_det_eq_one_of_measurePreserving gC hMP'
  -- `det (gC : →ₗ) = det g` since `gC`'s underlying linear map is `g` (`coe_toContinuousLinearMap`)
  rwa [LinearMap.coe_toContinuousLinearMap g] at hdet

end DLNFibre.DLN.RLCT

end
