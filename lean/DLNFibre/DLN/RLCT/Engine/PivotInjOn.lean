import DLNFibre.DLN.RLCT.Engine.PivotCover
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# `DLNFibre.DLN.RLCT.Engine.PivotInjOn` — the pivot chart's a.e.-injectivity atom (rung 3)

The o5-INDEPENDENT building block of the a.e.-`InjOn` `ChartBridge` clause: the pivot chart
`pivotChart i` is INJECTIVE off its exceptional hyperplane `{u i = 0}`, and that hyperplane is
`volume`-NULL. A blow-up chart is not injective on the exceptional fibre (compass finding 6); the
null exceptional set is exactly `{pivot = 0}`. The real leaf chart `ψ ∘ β` inherits a.e.-injectivity
from `β` (built from `pivotChart`) composed with the homeomorphism `ψ` — the transport is a rung-3
step once the o5 realization supplies the concrete `β`/`ψ`; this atom is its core.
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open MeasureTheory Set

variable {d : ℕ}

/-- **The pivot chart is injective off its exceptional hyperplane** `{u i = 0}`: where the pivot is
nonzero, the ratios `u k = (pivotChart i u) k / u i` are recovered, so `pivotChart i` is injective.
(On `{u i = 0}` the whole image collapses — the exceptional fibre, finding 6.) -/
theorem pivotChart_injOn (i : Fin d) : Set.InjOn (pivotChart i) {u | u i ≠ 0} := by
  intro u hu v hv h
  simp only [Set.mem_setOf_eq] at hu hv
  have hi : u i = v i := by have := congrFun h i; simpa [pivotChart] using this
  funext k
  by_cases hk : k = i
  · subst hk; exact hi
  · have hik : u i * u k = v i * v k := by
      have := congrFun h k; simpa [pivotChart, hk] using this
    rw [hi] at hik
    exact mul_left_cancel₀ hv hik

/-- **The pivot chart's exceptional set is null**: the hyperplane `{u i = 0}` has `volume` zero
(`Measure.pi_hyperplane`; `ℝ` has no atoms). So `pivotChart i` is a.e.-injective — injective off a
null set — the shape the `ChartBridge` a.e.-`InjOn` clause needs. -/
theorem pivotChart_exceptional_null (i : Fin d) :
    volume {u : Fin d → ℝ | u i = 0} = 0 := by
  rw [MeasureTheory.volume_pi]
  apply Measure.pi_hyperplane

/-- **A.e.-injectivity of the pivot chart** (the `ChartBridge`-clause shape at the atom level): a
null set `N = {u i = 0}` off which `pivotChart i` is injective. -/
theorem pivotChart_ae_injOn (i : Fin d) :
    ∃ N : Set (Fin d → ℝ), volume N = 0 ∧ Set.InjOn (pivotChart i) (Set.univ \ N) := by
  refine ⟨{u | u i = 0}, pivotChart_exceptional_null i, ?_⟩
  intro u hu v hv h
  simp only [Set.mem_diff, Set.mem_univ, true_and, Set.mem_setOf_eq] at hu hv
  exact pivotChart_injOn i hu hv h

end DLNFibre.DLN.RLCT.Engine
