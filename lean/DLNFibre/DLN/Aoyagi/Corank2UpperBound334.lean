import DLNFibre.DLN.Aoyagi.Corank2Chart334

/-!
# `DLN.Aoyagi.Corank2UpperBound334` — the single-chart RLCT upper bound (cite-free)

The Watanabe universal upper bound `rlct ≤ ½·codim` is, for a resolution, just the single-chart
change-of-variables — an ELEMENTARY direction that needs ONE certified `Chart` (no atlas, no cover,
no `θ`). `rlctAt_sumSqFam_le_chartMin_half` proves it cite-free from `Chart`'s banked per-chart CoV
leg (`Chart.mem_wLocalAdmissible_of_localAdmissible`) + the per-chart value
(`Chart.two_mul_wrlctAt_eq_chartMin`). The (3,3,4) instance via `chart334` gives
`rlctAt (∑(coreGen dvec eWrap)ᵢ²) 0 ≤ 4 = ½·minAdm(3,3,4)` — the cite-free upper half of the payoff
(salvage of the dead flat-fan cover; the LOWER bound genuinely needs the whole-neighbourhood
resolution, so it is NOT here).
-/

open MeasureTheory Set Topology
open DLNFibre.Core.Aoyagi RLCT
open DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap DLNFibre.DLN.Aoyagi.Corank2ChartJac

namespace DLNFibre.DLN.Aoyagi

/-- **Single-chart upper bound (cite-free).** One certified `Chart` of `∑Fᵢ²` at `x₀` gives
`rlctAt (∑Fᵢ²) x₀ ≤ chartMin/2` — the elementary CoV upper direction (no atlas/cover/`θ`). This is
the Watanabe universal `rlct ≤ ½·codim` for the BUILT object, from a single chart. -/
theorem rlctAt_sumSqFam_le_chartMin_half {M D : ℕ} {F : Fin M → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ}
    (c : Chart F x₀) :
    rlctAt (sumSqFam F) x₀ ≤ c.chartMin / 2 := by
  have hincl : localAdmissibleExponents (sumSqFam F) x₀ ⊆
      wLocalAdmissibleExponents c.jacWeightFn (sumSqFam (fun i ↦ F i ∘ c.g)) 0 :=
    fun cc hcc ↦ c.mem_wLocalAdmissible_of_localAdmissible hcc
  have hbdd : BddAbove
      (wLocalAdmissibleExponents c.jacWeightFn (sumSqFam (fun i ↦ F i ∘ c.g)) 0) := by
    rw [c.wLocalAdmissibleExponents_eq_Ico]; exact bddAbove_Ico
  -- `0` is locally admissible (`K⁰ = 1` integrable on a small ball) → the set is nonempty.
  have hint : IntegrableAtFilter (fun _ : Fin D → ℝ ↦ (1 : ℝ)) (𝓝 x₀) :=
    ⟨Metric.ball x₀ 1, Metric.ball_mem_nhds x₀ one_pos,
      integrableOn_const (μ := volume) (s := Metric.ball x₀ 1) (measure_ball_lt_top.ne)⟩
  have hne : (localAdmissibleExponents (sumSqFam F) x₀).Nonempty :=
    ⟨0, zero_mem_localAdmissibleExponents hint⟩
  have h1 : rlctAt (sumSqFam F) x₀
      ≤ wrlctAt c.jacWeightFn (sumSqFam (fun i ↦ F i ∘ c.g)) 0 :=
    csSup_le_csSup hbdd hne hincl
  have h2 := c.two_mul_wrlctAt_eq_chartMin
  linarith

/-- `chart334`'s divisor minimum is `≤ 8`: the `E`-axis `0 ∈ bindingAxes` gives
`chartMin ≤ jac E + 1 = 8` (`Finset.inf'_le`). Enough for the `≤ 4` bound (it is in fact `= 8`
`= minAdm(3,3,4)`, but `≤` suffices). -/
theorem chart334_chartMin_le : chart334.chartMin ≤ 8 := by
  have h0 : (0 : Fin 21) ∈ bindingAxes (chart334.bexp chart334.k₀) := by
    rw [chart334_bindingAxes]; decide
  calc chart334.chartMin ≤ ((chart334.jac (0 : Fin 21) : ℝ) + 1) := Finset.inf'_le _ h0
    _ = 8 := by rw [chart334_jac_E]; norm_num

/-- **The (3,3,4) single-chart upper bound (cite-free).** `rlctAt (∑(coreGen dvec eWrap)ᵢ²) 0 ≤ 4`
`= ½·minAdm(3,3,4)` — the Watanabe upper half, from `chart334` alone (no atlas). -/
theorem rlctAt_coreGen334_le_four :
    rlctAt (sumSqFam (coreGen dvec eWrap)) (0 : Fin 21 → ℝ) ≤ 4 := by
  have h := rlctAt_sumSqFam_le_chartMin_half chart334
  have hcm := chart334_chartMin_le
  linarith

end DLNFibre.DLN.Aoyagi
