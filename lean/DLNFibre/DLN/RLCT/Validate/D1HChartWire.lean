import DLNFibre.DLN.RLCT.Validate.D1HChartConstruction
import DLNFibre.DLN.RLCT.Validate.D1HChartInverse
import DLNFibre.DLN.RLCT.Validate.D1HChartFlatten

/-!
# `DLNFibre.DLN.RLCT.Validate.D1HChartWire` — germ-decomposition building blocks for the #231 wire

The structural germ facts that turn the post-chart loss `F = lossFlatShift ∘ Ψsymm` into the
`∑ (selected coords)² + ∑ (residual)²` shape the engine consumer
(`deepest_le_of_optimal_of_iftResidual`) expects. These are the bounded, verified building blocks;
the remaining #231 work (partition the `H0·H2` loss entries into the `nReg` selected `er k` plus the
residual, the global-`C¹` bump cutoff on the residual, and the `ℝ^N ≅ ℝ^nReg × Y` MP reindex) sits
on top of them.

- `lossFlatShift_eq_sum_sq` — `lossFlatShift H B v w = ∑ᵢⱼ ((prod (gmapAt H v w) − B) i j)²` (the
  loss is a double sum of squared entries; `rfl`-level).
- `lossEntry_zero_of_optimal` — at an optimal `v` (`prod v = B`), every loss entry vanishes at the
  flat origin: `(prod (gmapAt H v 0) − B) i j = 0`.
- `selected_lossEntry_germ` — near the flat origin, the `k`-th SELECTED loss entry composed with the
  chart inverse reads the `ec k` flat coordinate
  (`(prod (gmapAt H v (Ψsymm w)) − B) (er k) =ᶠ w (ec k)`), from the chart's selected identity
  `chartΦ … (ec k) = gShift k` + the right-inverse germ + `lossEntry_zero_of_optimal`.

STATUS: building blocks sorry-free, axiom-clean. The partition + bump + reindex remain.
-/

open Matrix Module MeasureTheory Set Filter
open scoped ENNReal Topology
namespace DLNFibre.DLN.RLCT

variable {H : Fin (2 + 1) → ℕ} {B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ} {v : Params H}
  {m : ℕ} {er : Fin m → Fin (H 0) × Fin (H 2)} {ec : Fin m → Fin (flatDim H)}

/-- The flat-shifted loss is the double sum of its squared entries. -/
theorem lossFlatShift_eq_sum_sq (H : Fin (2 + 1) → ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (v : Params H) (w : Fin (flatDim H) → ℝ) :
    lossFlatShift H B v w = ∑ i, ∑ j, ((prod H (gmapAt H v w) - B) i j) ^ 2 := by
  rw [lossFlatShift, dlnLoss]; rfl

/-- At an optimal `v` (`prod v = B`), every loss entry vanishes at the flat origin. -/
theorem lossEntry_zero_of_optimal (hopt : prod H v = B) (i : Fin (H 0)) (j : Fin (H (Fin.last 2))) :
    (prod H (gmapAt H v 0) - B) i j = 0 := by
  rw [gmapAt_zero, hopt, sub_self]; rfl

/-- **The selected loss-entry germ.** Near the flat origin, the `k`-th selected loss entry composed
with the chart inverse `Ψsymm` reads the `ec k` flat coordinate. Combines the chart's selected
identity (`chartΦ … (ec k) = gShift k`, with `gShift k 0 = 0` since the entry vanishes at `0`) with
the right-inverse germ `chartΦ (Ψsymm w) = w`. -/
theorem selected_lossEntry_germ (hopt : prod H v = B) (hec : Function.Injective ec)
    (Ψsymm : (Fin (flatDim H) → ℝ) → (Fin (flatDim H) → ℝ))
    (hrinv : ∀ᶠ w in 𝓝 (0 : Fin (flatDim H) → ℝ), chartΦ H B v er ec (Ψsymm w) = w) (k : Fin m) :
    ∀ᶠ w in 𝓝 (0 : Fin (flatDim H) → ℝ),
      (prod H (gmapAt H v (Ψsymm w)) - B) (er k).1 (er k).2 = w (ec k) := by
  filter_upwards [hrinv] with w hw
  have h1 : chartΦ H B v er ec (Ψsymm w) (ec k) = w (ec k) := by rw [hw]
  rw [chartΦ_sel hec k, gShift, lossEntry_zero_of_optimal hopt (er k).1 (er k).2, sub_zero] at h1
  exact h1

end DLNFibre.DLN.RLCT
