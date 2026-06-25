import DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates
import DLNFibre.DLN.Aoyagi.RegularSuspensionIntegrability
import Mathlib.Analysis.InnerProductSpace.PiL2

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

/-- Euclidean coordinate square-sums are strictly positive away from the
origin. -/
theorem aoyagiEuclideanCoordinateSquareSum_pos_of_ne_zero
    {η : Type*} [Fintype η] (x : EuclideanSpace ℝ η) (hx : x ≠ 0) :
    0 < aoyagiCoordinateSquareSum (fun i : η => x i) := by
  have hnormpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x)
    (fun hnorm => hx (norm_eq_zero.mp hnorm.symm))
  have hsqpos : 0 < ‖x‖ ^ 2 := sq_pos_of_pos hnormpos
  simpa [aoyagiCoordinateSquareSum, EuclideanSpace.real_norm_sq_eq] using hsqpos

/-- Euclidean coordinate square-sums are almost everywhere strictly positive
for a nonatomic measure. -/
theorem ae_aoyagiEuclideanCoordinateSquareSum_pos
    {η : Type*} [Fintype η] {μ : Measure (EuclideanSpace ℝ η)} [NoAtoms μ] :
    ∀ᵐ x ∂μ, 0 < aoyagiCoordinateSquareSum (fun i : η => x i) := by
  filter_upwards [Measure.ae_ne μ (0 : EuclideanSpace ℝ η)] with x hx
  exact aoyagiEuclideanCoordinateSquareSum_pos_of_ne_zero x hx

/-- Restricted-measure version of a.e. positivity for Euclidean coordinate
square-sums. -/
theorem ae_aoyagiEuclideanCoordinateSquareSum_pos_restrict
    {η : Type*} [Fintype η] {μ : Measure (EuclideanSpace ℝ η)} [NoAtoms μ]
    (s : Set (EuclideanSpace ℝ η)) :
    ∀ᵐ x ∂μ.restrict s, 0 < aoyagiCoordinateSquareSum (fun i : η => x i) :=
  ae_restrict_of_ae (ae_aoyagiEuclideanCoordinateSquareSum_pos (η := η) (μ := μ))

/-- Ball-local negative-power integrability for Aoyagi's finite coordinate
square-sum on Euclidean coordinate space. -/
theorem lintegral_ofReal_euclideanCoordinateSquareSum_rpow_neg_indicator_ball_lt_top
    {η : Type*} [Fintype η] [Nonempty η]
    {μ : Measure (EuclideanSpace ℝ η)} [μ.IsAddHaarMeasure]
    {t R : ℝ} (hR : 0 < R) (ht_nonneg : 0 ≤ t)
    (hcrit : 2 * t < (Fintype.card η : ℝ)) :
    (∫⁻ x : EuclideanSpace ℝ η,
      (Metric.ball (0 : EuclideanSpace ℝ η) R).indicator
        (fun x : EuclideanSpace ℝ η =>
          ENNReal.ofReal ((aoyagiCoordinateSquareSum (fun i : η => x i)) ^ (-t))) x ∂μ) < ∞ := by
  have hcrit' :
      2 * t < (Module.finrank ℝ (EuclideanSpace ℝ η) : ℝ) := by
    simpa [finrank_euclideanSpace] using hcrit
  have hnorm :=
    lintegral_ofReal_norm_sq_add_rpow_neg_indicator_ball_lt_top
      (E := EuclideanSpace ℝ η) (μ := μ) (a := (0 : ℝ)) (s := t) (R := R)
      hR (by norm_num) ht_nonneg hcrit'
  have hlin :
      (∫⁻ x : EuclideanSpace ℝ η,
        (Metric.ball (0 : EuclideanSpace ℝ η) R).indicator
          (fun x : EuclideanSpace ℝ η =>
            ENNReal.ofReal ((aoyagiCoordinateSquareSum (fun i : η => x i)) ^ (-t))) x ∂μ) =
      (∫⁻ x : EuclideanSpace ℝ η, ENNReal.ofReal
        ((Metric.ball (0 : EuclideanSpace ℝ η) R).indicator
          (fun x : EuclideanSpace ℝ η => (‖x‖ ^ 2 + (0 : ℝ)) ^ (-t)) x) ∂μ) := by
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ η) R
    · simp [hx, aoyagiCoordinateSquareSum, EuclideanSpace.real_norm_sq_eq]
    · simp [hx]
  rwa [hlin]

/-- Restricted-ball form of Euclidean coordinate square-sum negative-power
integrability. -/
theorem lintegral_ofReal_euclideanCoordinateSquareSum_rpow_neg_restrict_ball_lt_top
    {η : Type*} [Fintype η] [Nonempty η]
    {μ : Measure (EuclideanSpace ℝ η)} [μ.IsAddHaarMeasure]
    {t R : ℝ} (hR : 0 < R) (ht_nonneg : 0 ≤ t)
    (hcrit : 2 * t < (Fintype.card η : ℝ)) :
    (∫⁻ x : EuclideanSpace ℝ η, ENNReal.ofReal
      ((aoyagiCoordinateSquareSum (fun i : η => x i)) ^ (-t))
      ∂ μ.restrict (Metric.ball (0 : EuclideanSpace ℝ η) R)) < ∞ := by
  have hind :=
    lintegral_ofReal_euclideanCoordinateSquareSum_rpow_neg_indicator_ball_lt_top
      (η := η) (μ := μ) (t := t) (R := R) hR ht_nonneg hcrit
  rwa [lintegral_indicator Metric.isOpen_ball.measurableSet] at hind

/-- Free Euclidean residual-coordinate model for the square-suspension product
estimate.  This discharges the residual base hypotheses in the special case
where the residual variables themselves are Euclidean coordinates. -/
theorem lintegral_ofReal_euclideanCoordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top
    {η E : Type*} [Fintype η] [Nonempty η]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure (EuclideanSpace ℝ η)} [μ.IsAddHaarMeasure]
    {ν : Measure E} [ν.IsAddHaarMeasure]
    {t Rbase Rfiber : ℝ} (hRbase : 0 < Rbase) (ht : 0 < t)
    (hcrit : 2 * t < (Fintype.card η : ℝ)) :
    (∫⁻ z : EuclideanSpace ℝ η × E, ENNReal.ofReal
      ((Metric.ball (0 : E) Rfiber).indicator
        (fun u : E =>
          (aoyagiCoordinateSquareSum (fun i : η => z.1 i) + ‖u‖ ^ 2) ^
            (-(t + (Module.finrank ℝ E : ℝ) / 2))) z.2)
      ∂ (μ.restrict (Metric.ball (0 : EuclideanSpace ℝ η) Rbase)).prod ν) < ∞ := by
  have hpos :
      ∀ᵐ x ∂μ.restrict (Metric.ball (0 : EuclideanSpace ℝ η) Rbase),
        0 < aoyagiCoordinateSquareSum (fun i : η => x i) :=
    ae_aoyagiEuclideanCoordinateSquareSum_pos_restrict
      (η := η) (μ := μ) (Metric.ball (0 : EuclideanSpace ℝ η) Rbase)
  have hbase :
      (∫⁻ x : EuclideanSpace ℝ η, ENNReal.ofReal
        ((aoyagiCoordinateSquareSum (fun i : η => x i)) ^ (-t))
        ∂ μ.restrict (Metric.ball (0 : EuclideanSpace ℝ η) Rbase)) < ∞ :=
    lintegral_ofReal_euclideanCoordinateSquareSum_rpow_neg_restrict_ball_lt_top
      (η := η) (μ := μ) (t := t) (R := Rbase) hRbase ht.le hcrit
  exact
    lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_residual_power_lt_top
      (E := E) (μ := μ.restrict (Metric.ball (0 : EuclideanSpace ℝ η) Rbase))
      (ν := ν)
      (a := fun x : EuclideanSpace ℝ η => aoyagiCoordinateSquareSum (fun i : η => x i))
      (t := t) (R := Rfiber)
      hpos ht hbase

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
