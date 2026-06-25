import DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates
import DLNFibre.DLN.Aoyagi.RegularSuspensionIntegrability

/-!
# Square-sum specialisations of regular-suspension integrability

This file connects the variable-base square-model product estimate with
Aoyagi's finite coordinate square-sum convention.  It only specialises the base
parameter to a coordinate square-sum; positivity and residual negative-power
integrability remain explicit hypotheses.

It does not prove residual-base integrability, construct the p. 13 analytic
chart, prove bounded-density/prior transport, produce normal crossings, or
extract pole order/RLCT.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DLNFibre
namespace DLN
namespace Aoyagi

set_option linter.style.longLine false

/-- Coordinate-square-sum form of the residual-power product estimate. -/
theorem lintegral_ofReal_coordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_le_residual_power_scale
    {α η E : Type*} [MeasurableSpace α] [Fintype η]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure α} {ν : Measure E} [ν.IsAddHaarMeasure]
    {b : α → η → ℝ} {t R : ℝ}
    (hpos : ∀ᵐ x ∂μ, 0 < aoyagiCoordinateSquareSum (b x)) (ht : 0 < t) :
    (∫⁻ z : α × E, ENNReal.ofReal
      ((Metric.ball (0 : E) R).indicator
        (fun u : E =>
          (aoyagiCoordinateSquareSum (b z.1) + ‖u‖ ^ 2) ^
            (-(t + (Module.finrank ℝ E : ℝ) / 2))) z.2) ∂ μ.prod ν) ≤
      (∫⁻ x : α, ENNReal.ofReal
        ((aoyagiCoordinateSquareSum (b x)) ^ (-t)) ∂μ) *
        ∫⁻ u : E, ENNReal.ofReal
          (((1 : ℝ) + ‖u‖ ^ 2) ^
            (-(t + (Module.finrank ℝ E : ℝ) / 2))) ∂ν := by
  exact
    lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_le_residual_power_scale
      (E := E) (μ := μ) (ν := ν)
      (a := fun x => aoyagiCoordinateSquareSum (b x))
      (t := t) (R := R) hpos ht

/-- Coordinate-square-sum finite-side threshold-shift corollary. -/
theorem lintegral_ofReal_coordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_residual_power_lt_top
    {α η E : Type*} [MeasurableSpace α] [Fintype η]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure α} {ν : Measure E} [ν.IsAddHaarMeasure]
    {b : α → η → ℝ} {t R : ℝ}
    (hpos : ∀ᵐ x ∂μ, 0 < aoyagiCoordinateSquareSum (b x)) (ht : 0 < t)
    (hbase :
      (∫⁻ x : α, ENNReal.ofReal
        ((aoyagiCoordinateSquareSum (b x)) ^ (-t)) ∂μ) < ∞) :
    (∫⁻ z : α × E, ENNReal.ofReal
      ((Metric.ball (0 : E) R).indicator
        (fun u : E =>
          (aoyagiCoordinateSquareSum (b z.1) + ‖u‖ ^ 2) ^
            (-(t + (Module.finrank ℝ E : ℝ) / 2))) z.2) ∂ μ.prod ν) < ∞ := by
  exact
    lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_residual_power_lt_top
      (E := E) (μ := μ) (ν := ν)
      (a := fun x => aoyagiCoordinateSquareSum (b x))
      (t := t) (R := R) hpos ht hbase

/-- Residual-block square-sum finite-side threshold-shift corollary. -/
theorem lintegral_ofReal_residualBlockSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_residual_power_lt_top
    {α ι κ E : Type*} [MeasurableSpace α] [Fintype ι] [Fintype κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure α} {ν : Measure E} [ν.IsAddHaarMeasure]
    {D : α → Matrix ι κ ℝ} {t R : ℝ}
    (hpos : ∀ᵐ x ∂μ,
      0 < aoyagiCoordinateSquareSum
        (AoyagiResidualBlockCoordinateIndex.value (D x)))
    (ht : 0 < t)
    (hbase :
      (∫⁻ x : α, ENNReal.ofReal
        ((aoyagiCoordinateSquareSum
          (AoyagiResidualBlockCoordinateIndex.value (D x))) ^ (-t)) ∂μ) < ∞) :
    (∫⁻ z : α × E, ENNReal.ofReal
      ((Metric.ball (0 : E) R).indicator
        (fun u : E =>
          (aoyagiCoordinateSquareSum
              (AoyagiResidualBlockCoordinateIndex.value (D z.1)) +
            ‖u‖ ^ 2) ^
            (-(t + (Module.finrank ℝ E : ℝ) / 2))) z.2) ∂ μ.prod ν) < ∞ := by
  exact
    lintegral_ofReal_coordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_residual_power_lt_top
      (E := E) (μ := μ) (ν := ν)
      (b := fun x => AoyagiResidualBlockCoordinateIndex.value (D x))
      (t := t) (R := R) hpos ht hbase

end Aoyagi
end DLN
end DLNFibre

end
