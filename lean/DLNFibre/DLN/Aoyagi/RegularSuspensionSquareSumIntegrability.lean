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

end Aoyagi
end DLN
end DLNFibre

end
