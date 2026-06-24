import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# One-sided integrability for ENNReal regular suspensions

This file records a narrow Tonelli/comparison brick toward the regular-square
suspension theorem.  It proves that adding a nonnegative ENNReal term over a
finite extra factor preserves finiteness of a nonnegative singular integral.

It does not prove a threshold shift, a polar-coordinate estimate, a
regular-coordinate additivity theorem, a p. 13 analytic chart, or any RLCT
extraction.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- Adding a nonnegative ENNReal term decreases a nonnegative negative-power
integrand pointwise, hence decreases its lower integral. -/
theorem lintegral_rpow_neg_add_right_le_prod_fst
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {a : α → ℝ≥0∞} {q : β → ℝ≥0∞} {s : ℝ}
    (hs : 0 ≤ s) :
    (∫⁻ z : α × β, (a z.1 + q z.2) ^ (-s) ∂ μ.prod ν)
      ≤ ∫⁻ z : α × β, (a z.1) ^ (-s) ∂ μ.prod ν := by
  refine lintegral_mono fun z ↦ ?_
  rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
  exact ENNReal.inv_le_inv.mpr
    (ENNReal.rpow_le_rpow (le_add_right le_rfl) hs)

/-- Over a finite extra factor, adding a nonnegative ENNReal term preserves
finiteness of the singular integral pulled back from the first factor. -/
theorem lintegral_rpow_neg_add_right_lt_top_of_lintegral_rpow_neg_lt_top
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsFiniteMeasure ν]
    {a : α → ℝ≥0∞} {q : β → ℝ≥0∞} {s : ℝ}
    (ha : AEMeasurable a μ) (hs : 0 ≤ s)
    (hbase : (∫⁻ x, a x ^ (-s) ∂μ) < ∞) :
    (∫⁻ z : α × β, (a z.1 + q z.2) ^ (-s) ∂ μ.prod ν) < ∞ := by
  refine lt_of_le_of_lt (lintegral_rpow_neg_add_right_le_prod_fst
    (μ := μ) (ν := ν) (a := a) (q := q) hs) ?_
  have hpow : AEMeasurable (fun x ↦ a x ^ (-s)) μ :=
    ENNReal.continuous_rpow_const.aemeasurable.comp_aemeasurable ha
  have hprod :
      (∫⁻ z : α × β, (a z.1) ^ (-s) ∂ μ.prod ν) =
        (∫⁻ x, a x ^ (-s) ∂ μ) * ν Set.univ := by
    calc
      (∫⁻ z : α × β, (a z.1) ^ (-s) ∂ μ.prod ν) =
          ∫⁻ z : α × β, (a z.1) ^ (-s) * (1 : ℝ≥0∞) ∂ μ.prod ν := by
        simp
      _ = (∫⁻ x, a x ^ (-s) ∂ μ) * ∫⁻ y : β, (1 : ℝ≥0∞) ∂ν := by
        rw [lintegral_prod_mul hpow aemeasurable_const]
      _ = (∫⁻ x, a x ^ (-s) ∂ μ) * ν Set.univ := by
        simp
  rw [hprod]
  exact ENNReal.mul_lt_top hbase (measure_lt_top ν Set.univ)

/-- Restricted-neighborhood version of finite-factor one-sided preservation. -/
theorem lintegral_rpow_neg_add_right_restrict_lt_top_of_lintegral_rpow_neg_restrict_lt_top
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {u : Set α} {t : Set β}
    {a : α → ℝ≥0∞} {q : β → ℝ≥0∞} {s : ℝ}
    (ha : AEMeasurable a (μ.restrict u)) (hs : 0 ≤ s) (ht : ν t < ∞)
    (hbase : (∫⁻ x, a x ^ (-s) ∂μ.restrict u) < ∞) :
    (∫⁻ z : α × β, (a z.1 + q z.2) ^ (-s)
      ∂ (μ.restrict u).prod (ν.restrict t)) < ∞ := by
  haveI : IsFiniteMeasure (ν.restrict t) :=
    isFiniteMeasure_restrict.2 (ne_of_lt ht)
  exact
    lintegral_rpow_neg_add_right_lt_top_of_lintegral_rpow_neg_lt_top
      (μ := μ.restrict u) (ν := ν.restrict t) (a := a) (q := q) ha hs hbase

end Aoyagi
end DLN
end DLNFibre

end
