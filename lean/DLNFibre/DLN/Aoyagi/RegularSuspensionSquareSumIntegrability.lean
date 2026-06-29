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

/-- Coordinate-square-sum reverse finite-side threshold shift. -/
theorem lintegral_ofReal_residual_power_lt_top_of_coordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top
    {α η E : Type*} [MeasurableSpace α] [Fintype η]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure α} {ν : Measure E} [SFinite ν] [ν.IsAddHaarMeasure]
    {b : α → η → ℝ} {t R : ℝ}
    (hmeas : AEMeasurable (fun x : α => aoyagiCoordinateSquareSum (b x)) μ)
    (hR : 0 < R)
    (hpos : ∀ᵐ x ∂μ, 0 < aoyagiCoordinateSquareSum (b x))
    (hle : ∀ᵐ x ∂μ, aoyagiCoordinateSquareSum (b x) ≤ R ^ 2)
    (ht : 0 < t)
    (hprod :
      (∫⁻ z : α × E, ENNReal.ofReal
        ((Metric.ball (0 : E) R).indicator
          (fun u : E =>
            (aoyagiCoordinateSquareSum (b z.1) + ‖u‖ ^ 2) ^
              (-(t + (Module.finrank ℝ E : ℝ) / 2))) z.2) ∂ μ.prod ν) < ∞) :
    (∫⁻ x : α, ENNReal.ofReal
      ((aoyagiCoordinateSquareSum (b x)) ^ (-t)) ∂μ) < ∞ := by
  exact
    lintegral_ofReal_residual_power_lt_top_of_product_lt_top
      (E := E) (μ := μ) (ν := ν)
      (a := fun x : α => aoyagiCoordinateSquareSum (b x))
      (t := t) (R := R) hmeas hR hpos hle ht hprod

/-- Coordinate-square-sum local threshold-shift iff for the square model. -/
theorem lintegral_ofReal_coordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_iff_residual_power_lt_top
    {α η E : Type*} [MeasurableSpace α] [Fintype η]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure α} {ν : Measure E} [SFinite ν] [ν.IsAddHaarMeasure]
    {b : α → η → ℝ} {t R : ℝ}
    (hmeas : AEMeasurable (fun x : α => aoyagiCoordinateSquareSum (b x)) μ)
    (hR : 0 < R)
    (hpos : ∀ᵐ x ∂μ, 0 < aoyagiCoordinateSquareSum (b x))
    (hle : ∀ᵐ x ∂μ, aoyagiCoordinateSquareSum (b x) ≤ R ^ 2)
    (ht : 0 < t) :
    (∫⁻ z : α × E, ENNReal.ofReal
      ((Metric.ball (0 : E) R).indicator
        (fun u : E =>
          (aoyagiCoordinateSquareSum (b z.1) + ‖u‖ ^ 2) ^
            (-(t + (Module.finrank ℝ E : ℝ) / 2))) z.2) ∂ μ.prod ν) < ∞
      ↔
    (∫⁻ x : α, ENNReal.ofReal
      ((aoyagiCoordinateSquareSum (b x)) ^ (-t)) ∂μ) < ∞ := by
  exact
    lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_iff_residual_power_lt_top
      (E := E) (μ := μ) (ν := ν)
      (a := fun x : α => aoyagiCoordinateSquareSum (b x))
      (t := t) (R := R) hmeas hR hpos hle ht

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

/-- Residual-block square-sum reverse finite-side threshold shift. -/
theorem lintegral_ofReal_residual_power_lt_top_of_residualBlockSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top
    {α ι κ E : Type*} [MeasurableSpace α] [Fintype ι] [Fintype κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure α} {ν : Measure E} [SFinite ν] [ν.IsAddHaarMeasure]
    {D : α → Matrix ι κ ℝ} {t R : ℝ}
    (hmeas : AEMeasurable
      (fun x : α => aoyagiCoordinateSquareSum
        (AoyagiResidualBlockCoordinateIndex.value (D x))) μ)
    (hR : 0 < R)
    (hpos : ∀ᵐ x ∂μ,
      0 < aoyagiCoordinateSquareSum
        (AoyagiResidualBlockCoordinateIndex.value (D x)))
    (hle : ∀ᵐ x ∂μ,
      aoyagiCoordinateSquareSum
        (AoyagiResidualBlockCoordinateIndex.value (D x)) ≤ R ^ 2)
    (ht : 0 < t)
    (hprod :
      (∫⁻ z : α × E, ENNReal.ofReal
        ((Metric.ball (0 : E) R).indicator
          (fun u : E =>
            (aoyagiCoordinateSquareSum
                (AoyagiResidualBlockCoordinateIndex.value (D z.1)) +
              ‖u‖ ^ 2) ^
              (-(t + (Module.finrank ℝ E : ℝ) / 2))) z.2) ∂ μ.prod ν) < ∞) :
    (∫⁻ x : α, ENNReal.ofReal
      ((aoyagiCoordinateSquareSum
        (AoyagiResidualBlockCoordinateIndex.value (D x))) ^ (-t)) ∂μ) < ∞ := by
  exact
    lintegral_ofReal_residual_power_lt_top_of_coordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top
      (E := E) (μ := μ) (ν := ν)
      (b := fun x => AoyagiResidualBlockCoordinateIndex.value (D x))
      (t := t) (R := R) hmeas hR hpos hle ht hprod

/-- Residual-block square-sum local threshold-shift iff for the square model. -/
theorem lintegral_ofReal_residualBlockSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_iff_residual_power_lt_top
    {α ι κ E : Type*} [MeasurableSpace α] [Fintype ι] [Fintype κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure α} {ν : Measure E} [SFinite ν] [ν.IsAddHaarMeasure]
    {D : α → Matrix ι κ ℝ} {t R : ℝ}
    (hmeas : AEMeasurable
      (fun x : α => aoyagiCoordinateSquareSum
        (AoyagiResidualBlockCoordinateIndex.value (D x))) μ)
    (hR : 0 < R)
    (hpos : ∀ᵐ x ∂μ,
      0 < aoyagiCoordinateSquareSum
        (AoyagiResidualBlockCoordinateIndex.value (D x)))
    (hle : ∀ᵐ x ∂μ,
      aoyagiCoordinateSquareSum
        (AoyagiResidualBlockCoordinateIndex.value (D x)) ≤ R ^ 2)
    (ht : 0 < t) :
    (∫⁻ z : α × E, ENNReal.ofReal
      ((Metric.ball (0 : E) R).indicator
        (fun u : E =>
          (aoyagiCoordinateSquareSum
              (AoyagiResidualBlockCoordinateIndex.value (D z.1)) +
            ‖u‖ ^ 2) ^
            (-(t + (Module.finrank ℝ E : ℝ) / 2))) z.2) ∂ μ.prod ν) < ∞
      ↔
    (∫⁻ x : α, ENNReal.ofReal
      ((aoyagiCoordinateSquareSum
        (AoyagiResidualBlockCoordinateIndex.value (D x))) ^ (-t)) ∂μ) < ∞ := by
  exact
    lintegral_ofReal_coordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_iff_residual_power_lt_top
      (E := E) (μ := μ) (ν := ν)
      (b := fun x => AoyagiResidualBlockCoordinateIndex.value (D x))
      (t := t) (R := R) hmeas hR hpos hle ht

/-- Coordinate-square-sum regular-suspension comparison with bounded density.
If an actual loss is bounded below on the regular ball by a positive constant
times `coordinateSquareSum + ‖u‖^2`, and the transported density is bounded
between `0` and a constant there, then the actual loss-density lower integral
is finite whenever the residual negative `t`-power input is finite.

This is a one-sided supplied-bound theorem.  It does not construct Aoyagi's
p. 13 chart, prove the lower loss bound, prove density/Jacobian transport, or
establish threshold equality. -/
theorem lintegral_ofReal_loss_rpow_neg_mul_density_coordinateSquareSum_add_norm_sq_indicator_ball_prod_lt_top_of_residual_power_lt_top
    {α η E : Type*} [MeasurableSpace α] [Fintype η]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure α} {ν : Measure E} [ν.IsAddHaarMeasure]
    {b : α → η → ℝ} {loss density : α × E → ℝ} {t R c C : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (ht : 0 < t)
    (hpos : ∀ᵐ x ∂μ, 0 < aoyagiCoordinateSquareSum (b x))
    (hbase :
      (∫⁻ x : α, ENNReal.ofReal
        ((aoyagiCoordinateSquareSum (b x)) ^ (-t)) ∂μ) < ∞)
    (hloss : ∀ᵐ z : α × E ∂μ.prod ν,
      z.2 ∈ Metric.ball (0 : E) R →
        c * (aoyagiCoordinateSquareSum (b z.1) + ‖z.2‖ ^ 2) ≤ loss z)
    (hdensity_nonneg : ∀ᵐ z : α × E ∂μ.prod ν,
      z.2 ∈ Metric.ball (0 : E) R → 0 ≤ density z)
    (hdensity_le : ∀ᵐ z : α × E ∂μ.prod ν,
      z.2 ∈ Metric.ball (0 : E) R → density z ≤ C) :
    (∫⁻ z : α × E, ENNReal.ofReal
      ((Metric.ball (0 : E) R).indicator
        (fun u : E =>
          (loss (z.1, u)) ^ (-(t + (Module.finrank ℝ E : ℝ) / 2)) *
            density (z.1, u)) z.2) ∂μ.prod ν) < ∞ := by
  let s : ℝ := t + (Module.finrank ℝ E : ℝ) / 2
  let A : ℝ := c ^ (-s) * C
  let model : α × E → ℝ := fun z =>
    (Metric.ball (0 : E) R).indicator
      (fun u : E =>
        (aoyagiCoordinateSquareSum (b z.1) + ‖u‖ ^ 2) ^ (-s)) z.2
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    have hdim : 0 ≤ (Module.finrank ℝ E : ℝ) / 2 := by positivity
    linarith
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (Real.rpow_nonneg hc.le _) hC
  have hmodelFin :
      (∫⁻ z : α × E, ENNReal.ofReal (model z) ∂μ.prod ν) < ∞ := by
    dsimp [model, s]
    exact
      lintegral_ofReal_coordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_residual_power_lt_top
        (E := E) (μ := μ) (ν := ν) (b := b) (t := t) (R := R)
        hpos ht hbase
  have hmono :
      (∫⁻ z : α × E, ENNReal.ofReal
        ((Metric.ball (0 : E) R).indicator
          (fun u : E =>
            (loss (z.1, u)) ^ (-s) * density (z.1, u)) z.2) ∂μ.prod ν) ≤
        ∫⁻ z : α × E, ENNReal.ofReal (A * model z) ∂μ.prod ν := by
    apply lintegral_mono_ae
    have hpos_prod : ∀ᵐ z : α × E ∂μ.prod ν,
        0 < aoyagiCoordinateSquareSum (b z.1) :=
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hpos
    filter_upwards [hpos_prod, hloss, hdensity_nonneg, hdensity_le] with
      z hzpos hzloss hzdensity_nonneg hzdensity_le
    by_cases hzball : z.2 ∈ Metric.ball (0 : E) R
    · simp only [Set.indicator_of_mem hzball]
      apply ENNReal.ofReal_le_ofReal
      let q : ℝ := aoyagiCoordinateSquareSum (b z.1) + ‖z.2‖ ^ 2
      have hqpos : 0 < q := by
        dsimp [q]
        nlinarith [sq_nonneg ‖z.2‖]
      have hcqpos : 0 < c * q := mul_pos hc hqpos
      have hpow_le : (loss z) ^ (-s) ≤ c ^ (-s) * q ^ (-s) := by
        have hle : (loss z) ^ (-s) ≤ (c * q) ^ (-s) :=
          Real.rpow_le_rpow_of_nonpos hcqpos (hzloss hzball) (by linarith [hs_nonneg])
        have hmul : (c * q) ^ (-s) = c ^ (-s) * q ^ (-s) := by
          rw [Real.mul_rpow hc.le hqpos.le]
        exact hle.trans_eq hmul
      have hscale_nonneg : 0 ≤ c ^ (-s) * q ^ (-s) :=
        mul_nonneg (Real.rpow_nonneg hc.le _) (Real.rpow_nonneg hqpos.le _)
      calc
        (loss z) ^ (-s) * density z ≤
            (c ^ (-s) * q ^ (-s)) * density z :=
          mul_le_mul_of_nonneg_right hpow_le (hzdensity_nonneg hzball)
        _ ≤ (c ^ (-s) * q ^ (-s)) * C :=
          mul_le_mul_of_nonneg_left (hzdensity_le hzball) hscale_nonneg
        _ = A * q ^ (-s) := by
          dsimp [A]
          ring
        _ = A * model z := by
          simp [model, hzball, q]
    · simp [model, hzball]
  refine lt_of_le_of_lt hmono ?_
  have hscale :
      (∫⁻ z : α × E, ENNReal.ofReal (A * model z) ∂μ.prod ν) =
        ENNReal.ofReal A * ∫⁻ z : α × E, ENNReal.ofReal (model z) ∂μ.prod ν := by
    calc
      (∫⁻ z : α × E, ENNReal.ofReal (A * model z) ∂μ.prod ν) =
          ∫⁻ z : α × E, ENNReal.ofReal A * ENNReal.ofReal (model z) ∂μ.prod ν := by
        apply lintegral_congr
        intro z
        rw [ENNReal.ofReal_mul hA]
      _ = ENNReal.ofReal A * ∫⁻ z : α × E, ENNReal.ofReal (model z) ∂μ.prod ν := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [hscale]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmodelFin

/-- Reverse supplied-bound comparison for coordinate-square-sum regular
suspensions.  If the actual loss is positive and bounded above by a positive
constant times the square model, and the transported density is bounded below
by a positive constant on the regular ball, then finite actual loss-density
integrability forces finite residual negative-power integrability.

This is a supplied-bound theorem.  It does not construct Aoyagi's p. 13 chart,
prove either loss/density bound, prove measure transport, or establish
pole-order/RLCT. -/
theorem lintegral_ofReal_residual_power_lt_top_of_loss_rpow_neg_mul_density_coordinateSquareSum_add_norm_sq_indicator_ball_prod_lt_top_of_loss_pos_of_loss_le_const_mul_of_const_le_density
    {α η E : Type*} [MeasurableSpace α] [Fintype η]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure α} {ν : Measure E} [SFinite ν] [ν.IsAddHaarMeasure]
    {b : α → η → ℝ} {loss density : α × E → ℝ} {t R C d : ℝ}
    (hmeas : AEMeasurable (fun x : α => aoyagiCoordinateSquareSum (b x)) μ)
    (hR : 0 < R)
    (hpos : ∀ᵐ x ∂μ, 0 < aoyagiCoordinateSquareSum (b x))
    (hle_base : ∀ᵐ x ∂μ, aoyagiCoordinateSquareSum (b x) ≤ R ^ 2)
    (hC : 0 < C) (hd : 0 < d) (ht : 0 < t)
    (hloss_pos : ∀ᵐ z : α × E ∂μ.prod ν,
      z.2 ∈ Metric.ball (0 : E) R → 0 < loss z)
    (hloss_le : ∀ᵐ z : α × E ∂μ.prod ν,
      z.2 ∈ Metric.ball (0 : E) R →
        loss z ≤ C * (aoyagiCoordinateSquareSum (b z.1) + ‖z.2‖ ^ 2))
    (hdensity_ge : ∀ᵐ z : α × E ∂μ.prod ν,
      z.2 ∈ Metric.ball (0 : E) R → d ≤ density z)
    (hactual :
      (∫⁻ z : α × E, ENNReal.ofReal
        ((Metric.ball (0 : E) R).indicator
          (fun u : E =>
            (loss (z.1, u)) ^ (-(t + (Module.finrank ℝ E : ℝ) / 2)) *
              density (z.1, u)) z.2) ∂μ.prod ν) < ∞) :
    (∫⁻ x : α, ENNReal.ofReal
      ((aoyagiCoordinateSquareSum (b x)) ^ (-t)) ∂μ) < ∞ := by
  let s : ℝ := t + (Module.finrank ℝ E : ℝ) / 2
  let K : ℝ := d * C ^ (-s)
  let model : α × E → ℝ := fun z =>
    (Metric.ball (0 : E) R).indicator
      (fun u : E =>
        (aoyagiCoordinateSquareSum (b z.1) + ‖u‖ ^ 2) ^ (-s)) z.2
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    have hdim : 0 ≤ (Module.finrank ℝ E : ℝ) / 2 := by positivity
    linarith
  have hK_pos : 0 < K := by
    dsimp [K]
    exact mul_pos hd (Real.rpow_pos_of_pos hC _)
  have hK_nonneg : 0 ≤ K := hK_pos.le
  have hmono :
      (∫⁻ z : α × E, ENNReal.ofReal (K * model z) ∂μ.prod ν) ≤
        (∫⁻ z : α × E, ENNReal.ofReal
          ((Metric.ball (0 : E) R).indicator
            (fun u : E =>
              (loss (z.1, u)) ^ (-s) * density (z.1, u)) z.2) ∂μ.prod ν) := by
    apply lintegral_mono_ae
    have hpos_prod : ∀ᵐ z : α × E ∂μ.prod ν,
        0 < aoyagiCoordinateSquareSum (b z.1) :=
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hpos
    filter_upwards [hpos_prod, hloss_pos, hloss_le, hdensity_ge] with
      z hzpos hzloss_pos hzloss_le hzdensity_ge
    by_cases hzball : z.2 ∈ Metric.ball (0 : E) R
    · simp only [Set.indicator_of_mem hzball]
      apply ENNReal.ofReal_le_ofReal
      let q : ℝ := aoyagiCoordinateSquareSum (b z.1) + ‖z.2‖ ^ 2
      have hqpos : 0 < q := by
        dsimp [q]
        nlinarith [sq_nonneg ‖z.2‖]
      have hmodel_eq : model z = q ^ (-s) := by
        simp [model, hzball, q]
      have hCqpos : 0 < C * q := mul_pos hC hqpos
      have hpow_le : C ^ (-s) * q ^ (-s) ≤ (loss z) ^ (-s) := by
        have hle : (C * q) ^ (-s) ≤ (loss z) ^ (-s) :=
          Real.rpow_le_rpow_of_nonpos (hzloss_pos hzball)
            (by simpa [q] using hzloss_le hzball) (by linarith [hs_nonneg])
        have hmul : (C * q) ^ (-s) = C ^ (-s) * q ^ (-s) := by
          rw [Real.mul_rpow hC.le hqpos.le]
        rwa [← hmul]
      have hloss_pow_nonneg : 0 ≤ (loss z) ^ (-s) :=
        Real.rpow_nonneg (hzloss_pos hzball).le _
      calc
        K * model z = K * q ^ (-s) := by
          rw [hmodel_eq]
        _ = d * (C ^ (-s) * q ^ (-s)) := by
          dsimp [K]
          ring
        _ ≤ d * (loss z) ^ (-s) :=
          mul_le_mul_of_nonneg_left hpow_le hd.le
        _ ≤ density z * (loss z) ^ (-s) :=
          mul_le_mul_of_nonneg_right (hzdensity_ge hzball) hloss_pow_nonneg
        _ = (loss z) ^ (-s) * density z := by
          ring
    · simp [model, hzball]
  have hmodelFin :
      (∫⁻ z : α × E, ENNReal.ofReal (model z) ∂μ.prod ν) < ∞ := by
    have hscale :
        (∫⁻ z : α × E, ENNReal.ofReal (K * model z) ∂μ.prod ν) =
          ENNReal.ofReal K * ∫⁻ z : α × E, ENNReal.ofReal (model z) ∂μ.prod ν := by
      calc
        (∫⁻ z : α × E, ENNReal.ofReal (K * model z) ∂μ.prod ν) =
            ∫⁻ z : α × E, ENNReal.ofReal K * ENNReal.ofReal (model z) ∂μ.prod ν := by
          apply lintegral_congr
          intro z
          rw [ENNReal.ofReal_mul hK_nonneg]
        _ = ENNReal.ofReal K * ∫⁻ z : α × E, ENNReal.ofReal (model z) ∂μ.prod ν := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hmul_lt :
        ENNReal.ofReal K * ∫⁻ z : α × E,
          ENNReal.ofReal (model z) ∂μ.prod ν < ∞ := by
      rw [← hscale]
      exact lt_of_le_of_lt hmono hactual
    have hK_ne_zero : ENNReal.ofReal K ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr hK_pos
    have hmul_lt' :
        (∫⁻ z : α × E, ENNReal.ofReal (model z) ∂μ.prod ν) *
            ENNReal.ofReal K < ∞ := by
      simpa [mul_comm] using hmul_lt
    exact ENNReal.lt_top_of_mul_ne_top_left hmul_lt'.ne hK_ne_zero
  have hiff :=
    lintegral_ofReal_coordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_iff_residual_power_lt_top
      (E := E) (μ := μ) (ν := ν) (b := b) (t := t) (R := R)
      hmeas hR hpos hle_base ht
  exact hiff.mp (by simpa [model, s] using hmodelFin)

/-- Two-sided supplied-bound comparison for coordinate-square-sum regular
suspensions.  If an actual transported loss and density are uniformly
comparable to the square model on the regular ball, then actual
loss-density integrability is equivalent to residual negative-power
integrability.

This is still a supplied-bound theorem: it does not construct Aoyagi's p. 13
chart, prove the comparison hypotheses, prove measure transport, or establish
pole-order/RLCT. -/
theorem lintegral_ofReal_loss_rpow_neg_mul_density_coordinateSquareSum_add_norm_sq_indicator_ball_prod_lt_top_iff_residual_power_lt_top_of_two_sided_bounds
    {α η E : Type*} [MeasurableSpace α] [Fintype η]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure α} {ν : Measure E} [SFinite ν] [ν.IsAddHaarMeasure]
    {b : α → η → ℝ} {loss density : α × E → ℝ}
    {t R cL CL dρ Dρ : ℝ}
    (hmeas : AEMeasurable (fun x : α => aoyagiCoordinateSquareSum (b x)) μ)
    (hR : 0 < R)
    (hpos : ∀ᵐ x ∂μ, 0 < aoyagiCoordinateSquareSum (b x))
    (hle_base : ∀ᵐ x ∂μ, aoyagiCoordinateSquareSum (b x) ≤ R ^ 2)
    (hcL : 0 < cL) (hCL : 0 < CL) (hdρ : 0 < dρ) (hDρ : 0 ≤ Dρ)
    (ht : 0 < t)
    (hloss_lower : ∀ᵐ z : α × E ∂μ.prod ν,
      z.2 ∈ Metric.ball (0 : E) R →
        cL * (aoyagiCoordinateSquareSum (b z.1) + ‖z.2‖ ^ 2) ≤ loss z)
    (hloss_upper : ∀ᵐ z : α × E ∂μ.prod ν,
      z.2 ∈ Metric.ball (0 : E) R →
        loss z ≤ CL * (aoyagiCoordinateSquareSum (b z.1) + ‖z.2‖ ^ 2))
    (hdensity_lower : ∀ᵐ z : α × E ∂μ.prod ν,
      z.2 ∈ Metric.ball (0 : E) R → dρ ≤ density z)
    (hdensity_upper : ∀ᵐ z : α × E ∂μ.prod ν,
      z.2 ∈ Metric.ball (0 : E) R → density z ≤ Dρ) :
    (∫⁻ z : α × E, ENNReal.ofReal
      ((Metric.ball (0 : E) R).indicator
        (fun u : E =>
          (loss (z.1, u)) ^ (-(t + (Module.finrank ℝ E : ℝ) / 2)) *
            density (z.1, u)) z.2) ∂μ.prod ν) < ∞
      ↔
    (∫⁻ x : α, ENNReal.ofReal
      ((aoyagiCoordinateSquareSum (b x)) ^ (-t)) ∂μ) < ∞ := by
  constructor
  · intro hactual
    have hloss_pos : ∀ᵐ z : α × E ∂μ.prod ν,
        z.2 ∈ Metric.ball (0 : E) R → 0 < loss z := by
      have hpos_prod : ∀ᵐ z : α × E ∂μ.prod ν,
          0 < aoyagiCoordinateSquareSum (b z.1) :=
        (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hpos
      filter_upwards [hpos_prod, hloss_lower] with z hzpos hzloss_lower
      intro hzball
      let q : ℝ := aoyagiCoordinateSquareSum (b z.1) + ‖z.2‖ ^ 2
      have hqpos : 0 < q := by
        dsimp [q]
        nlinarith [sq_nonneg ‖z.2‖]
      exact lt_of_lt_of_le (mul_pos hcL hqpos) (hzloss_lower hzball)
    exact
      lintegral_ofReal_residual_power_lt_top_of_loss_rpow_neg_mul_density_coordinateSquareSum_add_norm_sq_indicator_ball_prod_lt_top_of_loss_pos_of_loss_le_const_mul_of_const_le_density
        (E := E) (μ := μ) (ν := ν) (b := b)
        (loss := loss) (density := density) (t := t) (R := R)
        (C := CL) (d := dρ)
        hmeas hR hpos hle_base hCL hdρ ht hloss_pos hloss_upper
        hdensity_lower hactual
  · intro hbase
    have hdensity_nonneg : ∀ᵐ z : α × E ∂μ.prod ν,
        z.2 ∈ Metric.ball (0 : E) R → 0 ≤ density z := by
      filter_upwards [hdensity_lower] with z hzdensity_lower
      intro hzball
      exact le_trans hdρ.le (hzdensity_lower hzball)
    exact
      lintegral_ofReal_loss_rpow_neg_mul_density_coordinateSquareSum_add_norm_sq_indicator_ball_prod_lt_top_of_residual_power_lt_top
        (E := E) (μ := μ) (ν := ν) (b := b)
        (loss := loss) (density := density) (t := t) (R := R)
        (c := cL) (C := Dρ)
        hcL hDρ ht hpos hbase hloss_lower hdensity_nonneg hdensity_upper

/-- Residual-block square-sum regular-suspension comparison with bounded
density.  This is the matrix-residual specialisation of
`lintegral_ofReal_loss_rpow_neg_mul_density_coordinateSquareSum_add_norm_sq_indicator_ball_prod_lt_top_of_residual_power_lt_top`. -/
theorem lintegral_ofReal_loss_rpow_neg_mul_density_residualBlockSquareSum_add_norm_sq_indicator_ball_prod_lt_top_of_residual_power_lt_top
    {α ι κ E : Type*} [MeasurableSpace α] [Fintype ι] [Fintype κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure α} {ν : Measure E} [ν.IsAddHaarMeasure]
    {D : α → Matrix ι κ ℝ} {loss density : α × E → ℝ} {t R c C : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (ht : 0 < t)
    (hpos : ∀ᵐ x ∂μ,
      0 < aoyagiCoordinateSquareSum
        (AoyagiResidualBlockCoordinateIndex.value (D x)))
    (hbase :
      (∫⁻ x : α, ENNReal.ofReal
        ((aoyagiCoordinateSquareSum
          (AoyagiResidualBlockCoordinateIndex.value (D x))) ^ (-t)) ∂μ) < ∞)
    (hloss : ∀ᵐ z : α × E ∂μ.prod ν,
      z.2 ∈ Metric.ball (0 : E) R →
        c * (aoyagiCoordinateSquareSum
            (AoyagiResidualBlockCoordinateIndex.value (D z.1)) +
          ‖z.2‖ ^ 2) ≤ loss z)
    (hdensity_nonneg : ∀ᵐ z : α × E ∂μ.prod ν,
      z.2 ∈ Metric.ball (0 : E) R → 0 ≤ density z)
    (hdensity_le : ∀ᵐ z : α × E ∂μ.prod ν,
      z.2 ∈ Metric.ball (0 : E) R → density z ≤ C) :
    (∫⁻ z : α × E, ENNReal.ofReal
      ((Metric.ball (0 : E) R).indicator
        (fun u : E =>
          (loss (z.1, u)) ^ (-(t + (Module.finrank ℝ E : ℝ) / 2)) *
            density (z.1, u)) z.2) ∂μ.prod ν) < ∞ := by
  exact
    lintegral_ofReal_loss_rpow_neg_mul_density_coordinateSquareSum_add_norm_sq_indicator_ball_prod_lt_top_of_residual_power_lt_top
      (E := E) (μ := μ) (ν := ν)
      (b := fun x => AoyagiResidualBlockCoordinateIndex.value (D x))
      (loss := loss) (density := density) (t := t) (R := R)
      (c := c) (C := C) hc hC ht hpos hbase hloss hdensity_nonneg hdensity_le

/-- Residual-block square-sum two-sided supplied-bound comparison. -/
theorem lintegral_ofReal_loss_rpow_neg_mul_density_residualBlockSquareSum_add_norm_sq_indicator_ball_prod_lt_top_iff_residual_power_lt_top_of_two_sided_bounds
    {α ι κ E : Type*} [MeasurableSpace α] [Fintype ι] [Fintype κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure α} {ν : Measure E} [SFinite ν] [ν.IsAddHaarMeasure]
    {D : α → Matrix ι κ ℝ} {loss density : α × E → ℝ}
    {t R cL CL dρ Dρ : ℝ}
    (hmeas : AEMeasurable
      (fun x : α => aoyagiCoordinateSquareSum
        (AoyagiResidualBlockCoordinateIndex.value (D x))) μ)
    (hR : 0 < R)
    (hpos : ∀ᵐ x ∂μ,
      0 < aoyagiCoordinateSquareSum
        (AoyagiResidualBlockCoordinateIndex.value (D x)))
    (hle_base : ∀ᵐ x ∂μ,
      aoyagiCoordinateSquareSum
        (AoyagiResidualBlockCoordinateIndex.value (D x)) ≤ R ^ 2)
    (hcL : 0 < cL) (hCL : 0 < CL) (hdρ : 0 < dρ) (hDρ : 0 ≤ Dρ)
    (ht : 0 < t)
    (hloss_lower : ∀ᵐ z : α × E ∂μ.prod ν,
      z.2 ∈ Metric.ball (0 : E) R →
        cL * (aoyagiCoordinateSquareSum
            (AoyagiResidualBlockCoordinateIndex.value (D z.1)) +
          ‖z.2‖ ^ 2) ≤ loss z)
    (hloss_upper : ∀ᵐ z : α × E ∂μ.prod ν,
      z.2 ∈ Metric.ball (0 : E) R →
        loss z ≤ CL * (aoyagiCoordinateSquareSum
            (AoyagiResidualBlockCoordinateIndex.value (D z.1)) +
          ‖z.2‖ ^ 2))
    (hdensity_lower : ∀ᵐ z : α × E ∂μ.prod ν,
      z.2 ∈ Metric.ball (0 : E) R → dρ ≤ density z)
    (hdensity_upper : ∀ᵐ z : α × E ∂μ.prod ν,
      z.2 ∈ Metric.ball (0 : E) R → density z ≤ Dρ) :
    (∫⁻ z : α × E, ENNReal.ofReal
      ((Metric.ball (0 : E) R).indicator
        (fun u : E =>
          (loss (z.1, u)) ^ (-(t + (Module.finrank ℝ E : ℝ) / 2)) *
            density (z.1, u)) z.2) ∂μ.prod ν) < ∞
      ↔
    (∫⁻ x : α, ENNReal.ofReal
      ((aoyagiCoordinateSquareSum
        (AoyagiResidualBlockCoordinateIndex.value (D x))) ^ (-t)) ∂μ) < ∞ := by
  exact
    lintegral_ofReal_loss_rpow_neg_mul_density_coordinateSquareSum_add_norm_sq_indicator_ball_prod_lt_top_iff_residual_power_lt_top_of_two_sided_bounds
      (E := E) (μ := μ) (ν := ν)
      (b := fun x => AoyagiResidualBlockCoordinateIndex.value (D x))
      (loss := loss) (density := density) (t := t) (R := R)
      (cL := cL) (CL := CL) (dρ := dρ) (Dρ := Dρ)
      hmeas hR hpos hle_base hcL hCL hdρ hDρ ht
      hloss_lower hloss_upper hdensity_lower hdensity_upper

section FixedBaseP13EuclideanRegularCoordinates

variable {N : ℕ}
  {W : Fin (N + 1) → Type*} [∀ i, AddCommGroup (W i)]
  [∀ i, TopologicalSpace (W i)] [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, Module ℝ (W i)]
  [∀ i, ContinuousSMul ℝ (W i)]
  {B : ∀ i : Fin N, W i.succ →ₗ[ℝ] W i.castSucc}

namespace PaperEndpointFixedBaseRegularCoordinateSourceData

set_option linter.unusedSectionVars false in
/-- The Euclidean space indexed by the p. 13 regular block coordinates has
dimension Aoyagi's regular-variable count. -/
theorem regularCoordinateEuclidean_finrank_eq_regularVariableCount
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge) :
    Module.finrank ℝ
        (EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0))) =
      aoyagiTheorem2RegularVariableCount N H r := by
  rw [finrank_euclideanSpace]
  exact sourceData.regularCoordinateIndex_card_eq_regularVariableCount

set_option linter.unusedSectionVars false in
/-- p. 13 fixed-base regular-coordinate model threshold-shift iff.

This is only the square model
`residualSquareSum + regularSquareSum`.  It does not include an actual loss,
density, Jacobian, chart-coverage, pole-order, or RLCT assertion. -/
theorem lintegral_ofReal_p13RegularCoordinates_model_lt_top_iff_residual_power_lt_top
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [SFinite ν] [ν.IsAddHaarMeasure]
    {t R : ℝ}
    (hmeas : AEMeasurable
      (fun x : α =>
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x)) μ)
    (hR : 0 < R)
    (hpos : ∀ᵐ x ∂μ,
      0 < aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀ Cedge x))
    (hle : ∀ᵐ x ∂μ,
      aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀ Cedge x) ≤ R ^ 2)
    (ht : 0 < t) :
    (∫⁻ z : α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)),
      ENNReal.ofReal
        ((Metric.ball
          (0 : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0))) R).indicator
          (fun u =>
            (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge z.1) +
              aoyagiCoordinateSquareSum (fun i => u i)) ^
              (-(t + (aoyagiTheorem2RegularVariableCount N H r : ℝ) / 2))) z.2)
      ∂ μ.prod ν) < ∞
      ↔
    (∫⁻ x : α, ENNReal.ofReal
      ((aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀ Cedge x)) ^ (-t)) ∂μ) < ∞ := by
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  have hfinrank_nat :
      Module.finrank ℝ (EuclideanSpace ℝ ρ) =
        aoyagiTheorem2RegularVariableCount N H r := by
    simpa [ρ] using
      sourceData.regularCoordinateEuclidean_finrank_eq_regularVariableCount
  have hfinrank :
      (Module.finrank ℝ (EuclideanSpace ℝ ρ) : ℝ) =
        (aoyagiTheorem2RegularVariableCount N H r : ℝ) := by
    exact_mod_cast hfinrank_nat
  have hiff :=
    lintegral_ofReal_coordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_iff_residual_power_lt_top
      (E := EuclideanSpace ℝ ρ) (μ := μ) (ν := ν)
      (b := fun x =>
        paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀ Cedge x)
      (t := t) (R := R) hmeas hR hpos hle ht
  rw [hfinrank] at hiff
  have hregular_sq (u : EuclideanSpace ℝ ρ) :
      aoyagiCoordinateSquareSum (fun i : ρ => u i) = ‖u‖ ^ 2 := by
    simpa [aoyagiCoordinateSquareSum] using (EuclideanSpace.real_norm_sq_eq u).symm
  simpa [ρ, hregular_sq] using hiff

set_option linter.unusedSectionVars false in
/-- p. 13 fixed-base regular-coordinate-space specialisation of the
bounded-density finite-side square-suspension theorem.

The theorem consumes product-measure hypotheses for the residual base and the
Euclidean regular-coordinate fiber.  It does not turn the source-stratum
filter facts into product-chart a.e. hypotheses, construct the p. 13 analytic
chart, compare with the original DLN loss, or prove density/Jacobian
transport. -/
theorem lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residual_power_lt_top
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {loss density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t R c C : ℝ}
    (_hR : 0 < R) (hc : 0 < c) (hC : 0 ≤ C) (ht : 0 < t)
    (hpos : ∀ᵐ x ∂μ,
      0 < aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀ Cedge x))
    (hbase :
      (∫⁻ x : α, ENNReal.ofReal
        ((aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x)) ^ (-t)) ∂μ) < ∞)
    (hloss : ∀ᵐ z ∂μ.prod ν,
      z.2 ∈ Metric.ball
          (0 : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
        c * (aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge z.1) +
          aoyagiCoordinateSquareSum (fun i => z.2 i)) ≤ loss z)
    (hdensity_nonneg : ∀ᵐ z ∂μ.prod ν,
      z.2 ∈ Metric.ball
          (0 : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
        0 ≤ density z)
    (hdensity_le : ∀ᵐ z ∂μ.prod ν,
      z.2 ∈ Metric.ball
          (0 : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
        density z ≤ C) :
    (∫⁻ z : α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)),
      ENNReal.ofReal
        ((Metric.ball
          (0 : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0))) R).indicator
          (fun u =>
            (loss (z.1, u)) ^
              (-(t + (aoyagiTheorem2RegularVariableCount N H r : ℝ) / 2)) *
              density (z.1, u)) z.2) ∂μ.prod ν) < ∞ := by
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  have hfinrank_nat :
      Module.finrank ℝ (EuclideanSpace ℝ ρ) =
        aoyagiTheorem2RegularVariableCount N H r := by
    simpa [ρ] using
      sourceData.regularCoordinateEuclidean_finrank_eq_regularVariableCount
  have hfinrank :
      (Module.finrank ℝ (EuclideanSpace ℝ ρ) : ℝ) =
        (aoyagiTheorem2RegularVariableCount N H r : ℝ) := by
    exact_mod_cast hfinrank_nat
  have hloss_norm : ∀ᵐ z : α × EuclideanSpace ℝ ρ ∂μ.prod ν,
      z.2 ∈ Metric.ball (0 : EuclideanSpace ℝ ρ) R →
        c * (aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge z.1) +
          ‖z.2‖ ^ 2) ≤ loss z := by
    filter_upwards [hloss] with z hzloss
    intro hzball
    simpa [ρ, aoyagiCoordinateSquareSum, EuclideanSpace.real_norm_sq_eq] using
      hzloss hzball
  have hfin :=
    lintegral_ofReal_loss_rpow_neg_mul_density_coordinateSquareSum_add_norm_sq_indicator_ball_prod_lt_top_of_residual_power_lt_top
      (E := EuclideanSpace ℝ ρ) (μ := μ) (ν := ν)
      (b := fun x =>
        paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀ Cedge x)
      (loss := loss) (density := density) (t := t) (R := R)
      (c := c) (C := C) hc hC ht hpos hbase hloss_norm hdensity_nonneg hdensity_le
  rw [hfinrank] at hfin
  simpa [ρ] using hfin

set_option linter.unusedSectionVars false in
/-- p. 13 fixed-base regular-coordinate specialisation of the two-sided
supplied-bound threshold iff for an actual loss-density integrand.

The loss and density comparisons are hypotheses.  This theorem does not
construct Aoyagi's p. 13 analytic chart, prove source-prior/Jacobian transport,
or establish pole-order/RLCT. -/
theorem lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_two_sided_bounds
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [SFinite ν] [ν.IsAddHaarMeasure]
    {loss density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t R cL CL dρ Dρ : ℝ}
    (hmeas : AEMeasurable
      (fun x : α =>
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x)) μ)
    (hR : 0 < R)
    (hpos : ∀ᵐ x ∂μ,
      0 < aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀ Cedge x))
    (hle_base : ∀ᵐ x ∂μ,
      aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀ Cedge x) ≤ R ^ 2)
    (hcL : 0 < cL) (hCL : 0 < CL) (hdρ : 0 < dρ) (hDρ : 0 ≤ Dρ)
    (ht : 0 < t)
    (hloss_lower : ∀ᵐ z ∂μ.prod ν,
      z.2 ∈ Metric.ball
          (0 : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
        cL * (aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge z.1) +
          aoyagiCoordinateSquareSum (fun i => z.2 i)) ≤ loss z)
    (hloss_upper : ∀ᵐ z ∂μ.prod ν,
      z.2 ∈ Metric.ball
          (0 : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
        loss z ≤ CL * (aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge z.1) +
          aoyagiCoordinateSquareSum (fun i => z.2 i)))
    (hdensity_lower : ∀ᵐ z ∂μ.prod ν,
      z.2 ∈ Metric.ball
          (0 : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
        dρ ≤ density z)
    (hdensity_upper : ∀ᵐ z ∂μ.prod ν,
      z.2 ∈ Metric.ball
          (0 : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
        density z ≤ Dρ) :
    (∫⁻ z : α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)),
      ENNReal.ofReal
        ((Metric.ball
          (0 : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0))) R).indicator
          (fun u =>
            (loss (z.1, u)) ^
              (-(t + (aoyagiTheorem2RegularVariableCount N H r : ℝ) / 2)) *
              density (z.1, u)) z.2) ∂μ.prod ν) < ∞
      ↔
    (∫⁻ x : α, ENNReal.ofReal
      ((aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀ Cedge x)) ^ (-t)) ∂μ) < ∞ := by
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  have hfinrank_nat :
      Module.finrank ℝ (EuclideanSpace ℝ ρ) =
        aoyagiTheorem2RegularVariableCount N H r := by
    simpa [ρ] using
      sourceData.regularCoordinateEuclidean_finrank_eq_regularVariableCount
  have hfinrank :
      (Module.finrank ℝ (EuclideanSpace ℝ ρ) : ℝ) =
        (aoyagiTheorem2RegularVariableCount N H r : ℝ) := by
    exact_mod_cast hfinrank_nat
  have hloss_lower_norm : ∀ᵐ z : α × EuclideanSpace ℝ ρ ∂μ.prod ν,
      z.2 ∈ Metric.ball (0 : EuclideanSpace ℝ ρ) R →
        cL * (aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge z.1) +
          ‖z.2‖ ^ 2) ≤ loss z := by
    filter_upwards [hloss_lower] with z hzloss
    intro hzball
    simpa [ρ, aoyagiCoordinateSquareSum, EuclideanSpace.real_norm_sq_eq] using
      hzloss hzball
  have hloss_upper_norm : ∀ᵐ z : α × EuclideanSpace ℝ ρ ∂μ.prod ν,
      z.2 ∈ Metric.ball (0 : EuclideanSpace ℝ ρ) R →
        loss z ≤ CL * (aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge z.1) +
          ‖z.2‖ ^ 2) := by
    filter_upwards [hloss_upper] with z hzloss
    intro hzball
    simpa [ρ, aoyagiCoordinateSquareSum, EuclideanSpace.real_norm_sq_eq] using
      hzloss hzball
  have hiff :=
    lintegral_ofReal_loss_rpow_neg_mul_density_coordinateSquareSum_add_norm_sq_indicator_ball_prod_lt_top_iff_residual_power_lt_top_of_two_sided_bounds
      (E := EuclideanSpace ℝ ρ) (μ := μ) (ν := ν)
      (b := fun x =>
        paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀ Cedge x)
      (loss := loss) (density := density) (t := t) (R := R)
      (cL := cL) (CL := CL) (dρ := dρ) (Dρ := Dρ)
      hmeas hR hpos hle_base hcL hCL hdρ hDρ ht
      hloss_lower_norm hloss_upper_norm hdensity_lower hdensity_upper
  rw [hfinrank] at hiff
  simpa [ρ] using hiff

end PaperEndpointFixedBaseRegularCoordinateSourceData

end FixedBaseP13EuclideanRegularCoordinates

end Aoyagi
end DLN
end DLNFibre

end
