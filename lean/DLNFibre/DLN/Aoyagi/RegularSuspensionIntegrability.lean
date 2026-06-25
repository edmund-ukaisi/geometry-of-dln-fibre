import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# One-sided integrability for ENNReal regular suspensions

This file records a narrow Tonelli/comparison brick toward the regular-square
suspension theorem.  It proves that adding a nonnegative ENNReal term over a
finite extra factor preserves finiteness of a nonnegative singular integral.

It does not prove a threshold shift, a Euclidean ball polar-coordinate equality
or asymptotic, a regular-coordinate additivity theorem, a p. 13 analytic chart,
or any RLCT extraction.
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

section RadialFiniteSide

/-- Radial punctured-ball integrability for the model `r^(-t)` below the
finite-dimensional critical exponent. -/
theorem integrable_norm_rpow_neg_indicator_Ioo
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {t R : ℝ}
    (hR : 0 < R) (ht : t < (Module.finrank ℝ E : ℝ)) :
    Integrable (fun x : E =>
      (Set.Ioo (0 : ℝ) R).indicator (fun y : ℝ => y ^ (-t)) ‖x‖) μ := by
  rw [integrable_fun_norm_addHaar (μ := μ)]
  rw [← Set.indicator_smul]
  rw [IntegrableOn]
  rw [integrable_indicator_iff measurableSet_Ioo]
  have hpow : IntegrableOn
      (fun y : ℝ => y ^ ((Module.finrank ℝ E : ℝ) - 1 - t)) (Set.Ioo 0 R) := by
    rw [intervalIntegral.integrableOn_Ioo_rpow_iff hR]
    linarith
  refine (hpow.restrict (t := Set.Ioi (0 : ℝ))).congr_fun ?_ measurableSet_Ioo
  intro y hy
  have hy0 : 0 < y := hy.1
  have hdimpos : 0 < Module.finrank ℝ E := Module.finrank_pos
  have hdimle : 1 ≤ Module.finrank ℝ E := Nat.succ_le_of_lt hdimpos
  have hcast : ((Module.finrank ℝ E - 1 : ℕ) : ℝ) =
      (Module.finrank ℝ E : ℝ) - 1 := by
    rw [Nat.cast_sub hdimle]
    norm_num
  calc
    y ^ ((Module.finrank ℝ E : ℝ) - 1 - t)
        = y ^ (((Module.finrank ℝ E : ℝ) - 1) + (-t)) := by ring_nf
    _ = y ^ ((Module.finrank ℝ E : ℝ) - 1) * y ^ (-t) := by
          rw [Real.rpow_add hy0]
    _ = y ^ (((Module.finrank ℝ E - 1 : ℕ) : ℝ)) * y ^ (-t) := by
          rw [hcast]
    _ = y ^ (Module.finrank ℝ E - 1) • y ^ (-t) := by
          simp [Real.rpow_natCast]

/-- Finite-side radial integrability for `(r^2+a)^(-s)` on a punctured ball,
under the critical inequality `2*s < finrank`. -/
theorem integrable_norm_sq_add_rpow_neg_indicator_Ioo
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {a s R : ℝ}
    (hR : 0 < R) (ha : 0 ≤ a) (hs : 0 ≤ s)
    (hcrit : 2 * s < (Module.finrank ℝ E : ℝ)) :
    Integrable (fun x : E =>
      (Set.Ioo (0 : ℝ) R).indicator
        (fun y : ℝ => (y ^ 2 + a) ^ (-s)) ‖x‖) μ := by
  have hmodel := integrable_norm_rpow_neg_indicator_Ioo
    (E := E) (μ := μ) (t := 2 * s) (R := R) hR hcrit
  refine hmodel.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · apply Measurable.aestronglyMeasurable
    exact (Measurable.indicator
      (((measurable_id.pow_const (2 : ℕ)).add measurable_const).pow_const (-s))
      measurableSet_Ioo).comp continuous_norm.measurable
  · by_cases hxI : ‖x‖ ∈ Set.Ioo (0 : ℝ) R
    · simp only [Set.indicator_of_mem hxI, Real.norm_eq_abs]
      have hx0 : 0 < ‖x‖ := hxI.1
      have hle_base : ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 + a := by linarith [ha]
      have hpow_le : (‖x‖ ^ 2 + a) ^ (-s) ≤ (‖x‖ ^ 2) ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hx0) hle_base (by linarith)
      have hsq_pow : (‖x‖ ^ 2) ^ (-s) = ‖x‖ ^ (-(2 * s)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hx0)]
        ring_nf
      have hadd_pos : 0 < ‖x‖ ^ 2 + a := by positivity
      have hnonneg_left : 0 ≤ (‖x‖ ^ 2 + a) ^ (-s) :=
        Real.rpow_nonneg (le_of_lt hadd_pos) _
      rw [abs_of_nonneg hnonneg_left]
      exact hpow_le.trans_eq hsq_pow
    · simp only [Set.indicator_of_notMem hxI, norm_zero, le_refl]

/-- `ENNReal.ofReal` lower-integral handoff for the finite-side radial
quadratic estimate. -/
theorem lintegral_ofReal_norm_sq_add_rpow_neg_indicator_Ioo_lt_top
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {a s R : ℝ}
    (hR : 0 < R) (ha : 0 ≤ a) (hs : 0 ≤ s)
    (hcrit : 2 * s < (Module.finrank ℝ E : ℝ)) :
    (∫⁻ x : E, ENNReal.ofReal
      ((Set.Ioo (0 : ℝ) R).indicator
        (fun y : ℝ => (y ^ 2 + a) ^ (-s)) ‖x‖) ∂μ) < ∞ := by
  have h := integrable_norm_sq_add_rpow_neg_indicator_Ioo
    (E := E) (μ := μ) (a := a) (s := s) (R := R) hR ha hs hcrit
  have hnonneg : ∀ x : E, 0 ≤
      (Set.Ioo (0 : ℝ) R).indicator
        (fun y : ℝ => (y ^ 2 + a) ^ (-s)) ‖x‖ := by
    intro x
    by_cases hxI : ‖x‖ ∈ Set.Ioo (0 : ℝ) R
    · simp only [Set.indicator_of_mem hxI]
      have hx0 : 0 < ‖x‖ := hxI.1
      have hadd_pos : 0 < ‖x‖ ^ 2 + a := by positivity
      exact Real.rpow_nonneg (le_of_lt hadd_pos) _
    · simp only [Set.indicator_of_notMem hxI, le_refl]
  rw [← lintegral_enorm_of_nonneg hnonneg]
  exact h.hasFiniteIntegral

/-- A radial puncture at the origin can be removed almost everywhere for a
nonatomic measure.  This is only an equality of representatives, not a
pointwise statement at the origin. -/
theorem ae_eq_norm_indicator_Ioo_Iio
    {β E : Type*} [Zero β] [NormedAddCommGroup E] [MeasurableSpace E]
    {μ : Measure E} [NoAtoms μ] (R : ℝ) (φ : ℝ → β) :
    (fun x : E => (Set.Ioo (0 : ℝ) R).indicator φ ‖x‖) =ᵐ[μ]
      (fun x : E => (Set.Iio R).indicator φ ‖x‖) := by
  filter_upwards [Measure.ae_ne μ (0 : E)] with x hx
  have hxnorm : ‖x‖ ≠ 0 := fun h0 => hx (norm_eq_zero.mp h0)
  have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hxnorm)
  by_cases hxR : ‖x‖ < R
  · have hxIoo : ‖x‖ ∈ Set.Ioo (0 : ℝ) R := ⟨hxpos, hxR⟩
    have hxIio : ‖x‖ ∈ Set.Iio R := hxR
    simp only [Set.indicator_of_mem hxIoo, Set.indicator_of_mem hxIio]
  · have hxIoo : ‖x‖ ∉ Set.Ioo (0 : ℝ) R := fun h => hxR h.2
    have hxIio : ‖x‖ ∉ Set.Iio R := hxR
    simp only [Set.indicator_of_notMem hxIoo, Set.indicator_of_notMem hxIio]

/-- Nonpunctured radial-support version of the finite-side quadratic estimate.
The origin is included only through a.e. congruence from the punctured theorem. -/
theorem integrable_norm_sq_add_rpow_neg_indicator_Iio
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {a s R : ℝ}
    (hR : 0 < R) (ha : 0 ≤ a) (hs : 0 ≤ s)
    (hcrit : 2 * s < (Module.finrank ℝ E : ℝ)) :
    Integrable (fun x : E =>
      (Set.Iio R).indicator
        (fun y : ℝ => (y ^ 2 + a) ^ (-s)) ‖x‖) μ := by
  exact (integrable_norm_sq_add_rpow_neg_indicator_Ioo
    (E := E) (μ := μ) (a := a) (s := s) (R := R) hR ha hs hcrit).congr
      (ae_eq_norm_indicator_Ioo_Iio
        (E := E) (μ := μ) (R := R)
        (φ := fun y : ℝ => (y ^ 2 + a) ^ (-s)))

/-- `ENNReal.ofReal` lower-integral handoff for the nonpunctured radial-support
quadratic estimate. -/
theorem lintegral_ofReal_norm_sq_add_rpow_neg_indicator_Iio_lt_top
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {a s R : ℝ}
    (hR : 0 < R) (ha : 0 ≤ a) (hs : 0 ≤ s)
    (hcrit : 2 * s < (Module.finrank ℝ E : ℝ)) :
    (∫⁻ x : E, ENNReal.ofReal
      ((Set.Iio R).indicator
        (fun y : ℝ => (y ^ 2 + a) ^ (-s)) ‖x‖) ∂μ) < ∞ := by
  have hpunct := lintegral_ofReal_norm_sq_add_rpow_neg_indicator_Ioo_lt_top
    (E := E) (μ := μ) (a := a) (s := s) (R := R) hR ha hs hcrit
  have hlin := lintegral_congr_ae
    ((ae_eq_norm_indicator_Ioo_Iio
      (E := E) (μ := μ) (R := R)
      (φ := fun y : ℝ => (y ^ 2 + a) ^ (-s))).mono
        fun _ hx => by simpa using congrArg ENNReal.ofReal hx)
  rwa [← hlin]

/-- Pointwise rewrite from open-ball support to radial `Iio` support. -/
theorem norm_sq_add_rpow_neg_indicator_ball_eq_indicator_Iio
    {E : Type*} [NormedAddCommGroup E] {a s R : ℝ} :
    (fun x : E =>
      (Metric.ball (0 : E) R).indicator
        (fun x : E => (‖x‖ ^ 2 + a) ^ (-s)) x) =
      fun x : E =>
        (Set.Iio R).indicator
          (fun y : ℝ => (y ^ 2 + a) ^ (-s)) ‖x‖ := by
  funext x
  have hball : Metric.ball (0 : E) R = (fun x : E => ‖x‖) ⁻¹' Set.Iio R := by
    ext x
    simp [Metric.mem_ball, dist_zero_right]
  rw [hball]
  exact Set.indicator_comp_right
    (s := Set.Iio R) (f := fun x : E => ‖x‖)
    (g := fun y : ℝ => (y ^ 2 + a) ^ (-s)) (x := x)

/-- Open-ball support version of the finite-side quadratic estimate. -/
theorem integrable_norm_sq_add_rpow_neg_indicator_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {a s R : ℝ}
    (hR : 0 < R) (ha : 0 ≤ a) (hs : 0 ≤ s)
    (hcrit : 2 * s < (Module.finrank ℝ E : ℝ)) :
    Integrable (fun x : E =>
      (Metric.ball (0 : E) R).indicator
        (fun x : E => (‖x‖ ^ 2 + a) ^ (-s)) x) μ := by
  rw [norm_sq_add_rpow_neg_indicator_ball_eq_indicator_Iio]
  exact integrable_norm_sq_add_rpow_neg_indicator_Iio
    (E := E) (μ := μ) (a := a) (s := s) (R := R) hR ha hs hcrit

/-- `ENNReal.ofReal` lower-integral handoff for the open-ball support quadratic
estimate. -/
theorem lintegral_ofReal_norm_sq_add_rpow_neg_indicator_ball_lt_top
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {a s R : ℝ}
    (hR : 0 < R) (ha : 0 ≤ a) (hs : 0 ≤ s)
    (hcrit : 2 * s < (Module.finrank ℝ E : ℝ)) :
    (∫⁻ x : E, ENNReal.ofReal
      ((Metric.ball (0 : E) R).indicator
        (fun x : E => (‖x‖ ^ 2 + a) ^ (-s)) x) ∂μ) < ∞ := by
  have hpoint := norm_sq_add_rpow_neg_indicator_ball_eq_indicator_Iio
    (E := E) (a := a) (s := s) (R := R)
  have hlin :
      (∫⁻ x : E, ENNReal.ofReal
        ((Metric.ball (0 : E) R).indicator
          (fun x : E => (‖x‖ ^ 2 + a) ^ (-s)) x) ∂μ) =
      (∫⁻ x : E, ENNReal.ofReal
        ((Set.Iio R).indicator
          (fun y : ℝ => (y ^ 2 + a) ^ (-s)) ‖x‖) ∂μ) := by
    apply lintegral_congr
    intro x
    exact congrArg ENNReal.ofReal (congrFun hpoint x)
  rw [hlin]
  exact lintegral_ofReal_norm_sq_add_rpow_neg_indicator_Iio_lt_top
    (E := E) (μ := μ) (a := a) (s := s) (R := R) hR ha hs hcrit

/-- Product-coordinate finite-side estimate in the below-regular-critical
case.  This only covers `2*s < finrank`; it is not the regular-variable
threshold-shift theorem. -/
theorem lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
    {μ : Measure α} [IsFiniteMeasure μ]
    {ν : Measure E} [ν.IsAddHaarMeasure]
    {a : α → ℝ} {s R : ℝ}
    (hR : 0 < R) (ha : ∀ᵐ x ∂μ, 0 ≤ a x) (hs : 0 ≤ s)
    (hcrit : 2 * s < (Module.finrank ℝ E : ℝ)) :
    (∫⁻ z : α × E, ENNReal.ofReal
      ((Metric.ball (0 : E) R).indicator
        (fun u : E => (a z.1 + ‖u‖ ^ 2) ^ (-s)) z.2) ∂ μ.prod ν) < ∞ := by
  let g : E → ℝ≥0∞ := fun u =>
    ENNReal.ofReal ((Metric.ball (0 : E) R).indicator
      (fun u : E => (‖u‖ ^ 2 + (0 : ℝ)) ^ (-s)) u)
  have hg : AEMeasurable g ν := by
    dsimp [g]
    have hreal : Measurable (fun u : E => (‖u‖ ^ 2 + (0 : ℝ)) ^ (-s)) :=
      ((continuous_norm.measurable.pow_const (2 : ℕ)).add measurable_const).pow_const (-s)
    exact (ENNReal.measurable_ofReal.comp
      (hreal.indicator Metric.isOpen_ball.measurableSet)).aemeasurable
  have hgfin : (∫⁻ u : E, g u ∂ν) < ∞ := by
    dsimp [g]
    simpa using
      (lintegral_ofReal_norm_sq_add_rpow_neg_indicator_ball_lt_top
        (E := E) (μ := ν) (a := (0 : ℝ)) (s := s) (R := R)
        hR (by norm_num) hs hcrit)
  have hmono :
      (∫⁻ z : α × E, ENNReal.ofReal
        ((Metric.ball (0 : E) R).indicator
          (fun u : E => (a z.1 + ‖u‖ ^ 2) ^ (-s)) z.2) ∂ μ.prod ν)
        ≤ ∫⁻ z : α × E, g z.2 ∂ μ.prod ν := by
    apply lintegral_mono_ae
    have ha_prod : ∀ᵐ z : α × E ∂ μ.prod ν, 0 ≤ a z.1 :=
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae ha
    have hne : ∀ᵐ z : α × E ∂ μ.prod ν, z.2 ≠ (0 : E) :=
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae
        (Measure.ae_ne ν (0 : E))
    filter_upwards [ha_prod, hne] with z haz hz
    dsimp [g]
    by_cases hzball : z.2 ∈ Metric.ball (0 : E) R
    · simp only [Set.indicator_of_mem hzball]
      apply ENNReal.ofReal_le_ofReal
      have hnormpos : 0 < ‖z.2‖ :=
        lt_of_le_of_ne (norm_nonneg z.2) (fun hnorm => hz (norm_eq_zero.mp hnorm.symm))
      have hbasepos : 0 < ‖z.2‖ ^ 2 := sq_pos_of_pos hnormpos
      have hle : ‖z.2‖ ^ 2 ≤ a z.1 + ‖z.2‖ ^ 2 := by linarith
      simpa using Real.rpow_le_rpow_of_nonpos hbasepos hle (by linarith)
    · simp only [Set.indicator_of_notMem hzball, le_rfl]
  have hprod :
      (∫⁻ z : α × E, g z.2 ∂ μ.prod ν) =
        μ Set.univ * ∫⁻ u : E, g u ∂ν := by
    simpa using
      (lintegral_prod_mul (μ := μ) (ν := ν)
        (f := fun _ : α => (1 : ℝ≥0∞)) (g := g) aemeasurable_const hg)
  exact lt_of_le_of_lt hmono
    (by rw [hprod]; exact ENNReal.mul_lt_top (measure_lt_top μ Set.univ) hgfin)

/-- Product-coordinate finite estimate away from the residual zero set.  If the
base term is bounded below by a positive constant almost everywhere, the
regular variables introduce no singularity on a regular ball. -/
theorem lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_ae_pos_le
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
    {μ : Measure α} [IsFiniteMeasure μ]
    {ν : Measure E} [ν.IsAddHaarMeasure]
    {a : α → ℝ} {s R ε : ℝ}
    (hε : 0 < ε) (ha : ∀ᵐ x ∂μ, ε ≤ a x) (hs : 0 ≤ s) :
    (∫⁻ z : α × E, ENNReal.ofReal
      ((Metric.ball (0 : E) R).indicator
        (fun u : E => (a z.1 + ‖u‖ ^ 2) ^ (-s)) z.2) ∂ μ.prod ν) < ∞ := by
  let C : ℝ := ε ^ (-s)
  let g : E → ℝ≥0∞ := fun u =>
    (Metric.ball (0 : E) R).indicator (fun _ : E => ENNReal.ofReal C) u
  have hg : AEMeasurable g ν := by
    dsimp [g]
    exact (measurable_const.indicator Metric.isOpen_ball.measurableSet).aemeasurable
  have hgfin : (∫⁻ u : E, g u ∂ν) < ∞ := by
    have hball : ν (Metric.ball (0 : E) R) < ∞ := measure_ball_lt_top
    have hCtop : ENNReal.ofReal C < ∞ := ENNReal.ofReal_lt_top
    dsimp [g]
    rw [lintegral_indicator_const Metric.isOpen_ball.measurableSet]
    exact ENNReal.mul_lt_top hCtop hball
  have hmono :
      (∫⁻ z : α × E, ENNReal.ofReal
        ((Metric.ball (0 : E) R).indicator
          (fun u : E => (a z.1 + ‖u‖ ^ 2) ^ (-s)) z.2) ∂ μ.prod ν)
        ≤ ∫⁻ z : α × E, g z.2 ∂ μ.prod ν := by
    apply lintegral_mono_ae
    have ha_prod : ∀ᵐ z : α × E ∂ μ.prod ν, ε ≤ a z.1 :=
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae ha
    filter_upwards [ha_prod] with z haz
    dsimp [g, C]
    by_cases hzball : z.2 ∈ Metric.ball (0 : E) R
    · simp only [Set.indicator_of_mem hzball]
      apply ENNReal.ofReal_le_ofReal
      have hε_le : ε ≤ a z.1 + ‖z.2‖ ^ 2 := by nlinarith [sq_nonneg ‖z.2‖]
      simpa using Real.rpow_le_rpow_of_nonpos hε hε_le (by linarith)
    · simp [Set.indicator_of_notMem hzball]
  have hprod :
      (∫⁻ z : α × E, g z.2 ∂ μ.prod ν) =
        μ Set.univ * ∫⁻ u : E, g u ∂ν := by
    simpa using
      (lintegral_prod_mul (μ := μ) (ν := ν)
        (f := fun _ : α => (1 : ℝ≥0∞)) (g := g) aemeasurable_const hg)
  exact lt_of_le_of_lt hmono
    (by rw [hprod]; exact ENNReal.mul_lt_top (measure_lt_top μ Set.univ) hgfin)

/-- Real integrability of the Japanese-bracket square model on the
supercritical side `finrank / 2 < s`. -/
theorem integrable_one_add_norm_sq_rpow_neg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {s : ℝ}
    (hs : (Module.finrank ℝ E : ℝ) / 2 < s) :
    Integrable (fun x : E => ((1 : ℝ) + ‖x‖ ^ 2) ^ (-s)) μ := by
  have hdim : (Module.finrank ℝ E : ℝ) < 2 * s := by linarith
  have hint0 := integrable_rpow_neg_one_add_norm_sq
    (E := E) (μ := μ) (r := 2 * s) hdim
  have hfun :
      (fun x : E => ((1 : ℝ) + ‖x‖ ^ 2) ^ (-(2 * s) / 2)) =
        (fun x : E => ((1 : ℝ) + ‖x‖ ^ 2) ^ (-s)) := by
    funext x
    congr 1
    ring
  simpa [hfun] using hint0

/-- Global Japanese-bracket model lower integral for the supercritical side
`finrank / 2 < s`.  This is the finite constant needed before a scaled
positive-parameter fiber bound. -/
theorem lintegral_ofReal_one_add_norm_sq_rpow_neg_lt_top
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {s : ℝ}
    (hs : (Module.finrank ℝ E : ℝ) / 2 < s) :
    (∫⁻ x : E, ENNReal.ofReal (((1 : ℝ) + ‖x‖ ^ 2) ^ (-s)) ∂μ) < ∞ := by
  have hint := integrable_one_add_norm_sq_rpow_neg (E := E) (μ := μ) hs
  have hnonneg : ∀ x : E, 0 ≤ ((1 : ℝ) + ‖x‖ ^ 2) ^ (-s) := by
    intro x
    exact Real.rpow_nonneg (by positivity) _
  rw [← lintegral_enorm_of_nonneg hnonneg]
  exact hint.hasFiniteIntegral

/-- Lower-integral scaling for the inverse scalar map on a finite-dimensional
real vector space with additive Haar measure. -/
theorem lintegral_comp_inv_smul_eq_mul_addHaar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure E} [μ.IsAddHaarMeasure] (f : E → ℝ≥0∞) {r : ℝ}
    (hr : r ≠ 0) :
    (∫⁻ x : E, f (r⁻¹ • x) ∂ μ) =
      ENNReal.ofReal (|r ^ Module.finrank ℝ E|) * ∫⁻ x : E, f x ∂ μ := by
  let e : E ≃ᵐ E :=
    (Homeomorph.smul (isUnit_iff_ne_zero.2 (inv_ne_zero hr)).unit).toMeasurableEquiv
  have hmap :
      Measure.map (fun x : E => r⁻¹ • x) μ =
        ENNReal.ofReal (|r ^ Module.finrank ℝ E|) • μ := by
    rw [Measure.map_addHaar_smul (μ := μ) (r := r⁻¹) (inv_ne_zero hr)]
    congr 1
    rw [inv_pow, inv_inv]
  calc
    (∫⁻ x : E, f (r⁻¹ • x) ∂ μ) =
        ∫⁻ y : E, f y ∂ Measure.map (fun x : E => r⁻¹ • x) μ := by
      simpa [e] using (MeasureTheory.lintegral_map_equiv (μ := μ) f e).symm
    _ = ∫⁻ y : E, f y ∂ ENNReal.ofReal (|r ^ Module.finrank ℝ E|) • μ := by
      rw [hmap]
    _ = ENNReal.ofReal (|r ^ Module.finrank ℝ E|) * ∫⁻ x : E, f x ∂ μ := by
      simp [smul_eq_mul]

/-- Pointwise positive-parameter square model identity behind the sharp
scaling estimate. -/
theorem ofReal_add_norm_sq_pos_rpow_neg_eq_mul_one_add_norm_sq_inv_sqrt_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a s : ℝ}
    (ha : 0 < a) (x : E) :
    ENNReal.ofReal ((a + ‖x‖ ^ 2) ^ (-s)) =
      ENNReal.ofReal (a ^ (-s)) *
        ENNReal.ofReal (((1 : ℝ) + ‖(Real.sqrt a)⁻¹ • x‖ ^ 2) ^ (-s)) := by
  have hreal :
      (a + ‖x‖ ^ 2) ^ (-s) =
        a ^ (-s) * (((1 : ℝ) + ‖(Real.sqrt a)⁻¹ • x‖ ^ 2) ^ (-s)) := by
    have hsqrtpos : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
    have hnormsq : ‖(Real.sqrt a)⁻¹ • x‖ ^ 2 = ‖x‖ ^ 2 / a := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsqrtpos)]
      rw [mul_pow, inv_pow, Real.sq_sqrt ha.le]
      field_simp [ha.ne']
    have hbase : a * ((1 : ℝ) + ‖(Real.sqrt a)⁻¹ • x‖ ^ 2) = a + ‖x‖ ^ 2 := by
      rw [hnormsq]
      field_simp [ha.ne']
    calc
      (a + ‖x‖ ^ 2) ^ (-s) =
          (a * ((1 : ℝ) + ‖(Real.sqrt a)⁻¹ • x‖ ^ 2)) ^ (-s) := by
        rw [hbase]
      _ = a ^ (-s) * (((1 : ℝ) + ‖(Real.sqrt a)⁻¹ • x‖ ^ 2) ^ (-s)) := by
        rw [Real.mul_rpow ha.le (by positivity)]
  rw [hreal]
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _)]

/-- Sharp whole-space positive-parameter scaling identity for the square
model.  Supercriticality is needed only in later finiteness applications. -/
theorem lintegral_ofReal_add_norm_sq_pos_rpow_neg_eq_scale
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {a s : ℝ}
    (ha : 0 < a) :
    (∫⁻ x : E, ENNReal.ofReal ((a + ‖x‖ ^ 2) ^ (-s)) ∂ μ) =
      ENNReal.ofReal (a ^ ((Module.finrank ℝ E : ℝ) / 2 - s)) *
        ∫⁻ x : E, ENNReal.ofReal (((1 : ℝ) + ‖x‖ ^ 2) ^ (-s)) ∂ μ := by
  let r : ℝ := Real.sqrt a
  let f : E → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (((1 : ℝ) + ‖x‖ ^ 2) ^ (-s))
  have hrpos : 0 < r := Real.sqrt_pos.2 ha
  have hr : r ≠ 0 := hrpos.ne'
  have hpoint : ∀ x : E,
      ENNReal.ofReal ((a + ‖x‖ ^ 2) ^ (-s)) =
        ENNReal.ofReal (a ^ (-s)) * f (r⁻¹ • x) := by
    intro x
    dsimp [f, r]
    exact ofReal_add_norm_sq_pos_rpow_neg_eq_mul_one_add_norm_sq_inv_sqrt_smul
      (a := a) (s := s) ha x
  have hlin :
      (∫⁻ x : E, ENNReal.ofReal ((a + ‖x‖ ^ 2) ^ (-s)) ∂ μ) =
        ENNReal.ofReal (a ^ (-s)) * ∫⁻ x : E, f (r⁻¹ • x) ∂ μ := by
    calc
      (∫⁻ x : E, ENNReal.ofReal ((a + ‖x‖ ^ 2) ^ (-s)) ∂ μ) =
          ∫⁻ x : E, ENNReal.ofReal (a ^ (-s)) * f (r⁻¹ • x) ∂ μ := by
        apply lintegral_congr
        exact hpoint
      _ = ENNReal.ofReal (a ^ (-s)) * ∫⁻ x : E, f (r⁻¹ • x) ∂ μ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [hlin]
  rw [lintegral_comp_inv_smul_eq_mul_addHaar (μ := μ) f hr]
  change ENNReal.ofReal (a ^ (-s)) *
        (ENNReal.ofReal (|r ^ Module.finrank ℝ E|) * ∫⁻ x : E, f x ∂ μ) =
      ENNReal.ofReal (a ^ ((Module.finrank ℝ E : ℝ) / 2 - s)) *
        ∫⁻ x : E, f x ∂ μ
  rw [← mul_assoc]
  congr 1
  have hrpow_nonneg : 0 ≤ a ^ (-s) := Real.rpow_nonneg ha.le _
  rw [← ENNReal.ofReal_mul hrpow_nonneg]
  congr 1
  dsimp [r]
  have hsqrtnonneg : 0 ≤ Real.sqrt a := (Real.sqrt_pos.2 ha).le
  have habs : |Real.sqrt a ^ Module.finrank ℝ E| = Real.sqrt a ^ Module.finrank ℝ E := by
    exact abs_of_nonneg (pow_nonneg hsqrtnonneg _)
  rw [habs]
  have hsqrtpow :
      Real.sqrt a ^ Module.finrank ℝ E =
        a ^ ((Module.finrank ℝ E : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul ha.le]
    congr 1
    ring
  rw [hsqrtpow]
  rw [← Real.rpow_add ha]
  congr 1
  ring

/-- Ball-restricted positive-parameter square model bound obtained by
restricting the sharp whole-space scaling identity. -/
theorem lintegral_ofReal_add_norm_sq_pos_rpow_neg_indicator_ball_le_scale
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {a s R : ℝ}
    (ha : 0 < a) :
    (∫⁻ x : E, ENNReal.ofReal
      ((Metric.ball (0 : E) R).indicator
        (fun x : E => (a + ‖x‖ ^ 2) ^ (-s)) x) ∂ μ) ≤
      ENNReal.ofReal (a ^ ((Module.finrank ℝ E : ℝ) / 2 - s)) *
        ∫⁻ x : E, ENNReal.ofReal (((1 : ℝ) + ‖x‖ ^ 2) ^ (-s)) ∂ μ := by
  have hmono :
      (∫⁻ x : E, ENNReal.ofReal
        ((Metric.ball (0 : E) R).indicator
          (fun x : E => (a + ‖x‖ ^ 2) ^ (-s)) x) ∂ μ) ≤
        ∫⁻ x : E, ENNReal.ofReal ((a + ‖x‖ ^ 2) ^ (-s)) ∂ μ := by
    apply lintegral_mono
    intro x
    by_cases hx : x ∈ Metric.ball (0 : E) R
    · simp only [Set.indicator_of_mem hx, le_rfl]
    · simp only [Set.indicator_of_notMem hx]
      simp
  exact hmono.trans_eq
    (lintegral_ofReal_add_norm_sq_pos_rpow_neg_eq_scale
      (E := E) (μ := μ) (a := a) (s := s) ha)

/-- Supercritical finiteness of the ball-restricted positive-parameter square
model with the sharp scaling bound as the controlling estimate. -/
theorem lintegral_ofReal_add_norm_sq_pos_rpow_neg_indicator_ball_lt_top_of_supercritical
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {a s R : ℝ}
    (ha : 0 < a) (hs : (Module.finrank ℝ E : ℝ) / 2 < s) :
    (∫⁻ x : E, ENNReal.ofReal
      ((Metric.ball (0 : E) R).indicator
        (fun x : E => (a + ‖x‖ ^ 2) ^ (-s)) x) ∂μ) < ∞ := by
  have hle :=
    lintegral_ofReal_add_norm_sq_pos_rpow_neg_indicator_ball_le_scale
      (E := E) (μ := μ) (a := a) (s := s) (R := R) ha
  have hmodel :=
    lintegral_ofReal_one_add_norm_sq_rpow_neg_lt_top
      (E := E) (μ := μ) (s := s) hs
  exact lt_of_le_of_lt hle
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmodel)

/-- Variable-base product estimate from the sharp positive-parameter fiber
bound.  The base measure need not be finite; all base-side control is carried
by the displayed lower-integral hypothesis. -/
theorem lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_le_scale
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure α} {ν : Measure E} [ν.IsAddHaarMeasure]
    {a : α → ℝ} {s R : ℝ}
    (ha_pos : ∀ᵐ x ∂μ, 0 < a x)
    (hs : (Module.finrank ℝ E : ℝ) / 2 < s) :
    (∫⁻ z : α × E, ENNReal.ofReal
      ((Metric.ball (0 : E) R).indicator
        (fun u : E => (a z.1 + ‖u‖ ^ 2) ^ (-s)) z.2) ∂ μ.prod ν) ≤
      (∫⁻ x : α, ENNReal.ofReal
        ((a x) ^ ((Module.finrank ℝ E : ℝ) / 2 - s)) ∂μ) *
        ∫⁻ u : E, ENNReal.ofReal (((1 : ℝ) + ‖u‖ ^ 2) ^ (-s)) ∂ν := by
  let p : ℝ := (Module.finrank ℝ E : ℝ) / 2 - s
  let K : ℝ≥0∞ :=
    ∫⁻ u : E, ENNReal.ofReal (((1 : ℝ) + ‖u‖ ^ 2) ^ (-s)) ∂ν
  let F : α × E → ℝ≥0∞ := fun z =>
    ENNReal.ofReal
      ((Metric.ball (0 : E) R).indicator
        (fun u : E => (a z.1 + ‖u‖ ^ 2) ^ (-s)) z.2)
  have hKlt : K < ∞ := by
    dsimp [K]
    exact lintegral_ofReal_one_add_norm_sq_rpow_neg_lt_top
      (E := E) (μ := ν) (s := s) hs
  have hfiber : ∀ᵐ x ∂μ,
      (∫⁻ u : E, F (x, u) ∂ν) ≤
        ENNReal.ofReal ((a x) ^ p) * K := by
    filter_upwards [ha_pos] with x hx
    dsimp [F, K, p]
    exact lintegral_ofReal_add_norm_sq_pos_rpow_neg_indicator_ball_le_scale
      (E := E) (μ := ν) (a := a x) (s := s) (R := R) hx
  have htotal :
      (∫⁻ z : α × E, F z ∂ μ.prod ν) ≤
        ∫⁻ x : α, ∫⁻ u : E, F (x, u) ∂ν ∂μ :=
    lintegral_prod_le F
  have hiter :
      (∫⁻ x : α, ∫⁻ u : E, F (x, u) ∂ν ∂μ) ≤
        ∫⁻ x : α, ENNReal.ofReal ((a x) ^ p) * K ∂μ :=
    lintegral_mono_ae hfiber
  exact (htotal.trans hiter).trans_eq (by
    rw [lintegral_mul_const' K _ hKlt.ne])

/-- Variable-base product finiteness from the sharp positive-parameter fiber
bound and a finite base-power lower integral. -/
theorem lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_ae_pos_of_base_lt_top
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure α} {ν : Measure E} [ν.IsAddHaarMeasure]
    {a : α → ℝ} {s R : ℝ}
    (ha_pos : ∀ᵐ x ∂μ, 0 < a x)
    (hs : (Module.finrank ℝ E : ℝ) / 2 < s)
    (hbase :
      (∫⁻ x : α, ENNReal.ofReal
        ((a x) ^ ((Module.finrank ℝ E : ℝ) / 2 - s)) ∂μ) < ∞) :
    (∫⁻ z : α × E, ENNReal.ofReal
      ((Metric.ball (0 : E) R).indicator
        (fun u : E => (a z.1 + ‖u‖ ^ 2) ^ (-s)) z.2) ∂ μ.prod ν) < ∞ := by
  let K : ℝ≥0∞ :=
    ∫⁻ u : E, ENNReal.ofReal (((1 : ℝ) + ‖u‖ ^ 2) ^ (-s)) ∂ν
  have hKlt : K < ∞ := by
    dsimp [K]
    exact lintegral_ofReal_one_add_norm_sq_rpow_neg_lt_top
      (E := E) (μ := ν) (s := s) hs
  have hle :=
    lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_le_scale
      (E := E) (μ := μ) (ν := ν) (a := a) (s := s) (R := R) ha_pos hs
  exact lt_of_le_of_lt hle (ENNReal.mul_lt_top hbase hKlt)

/-- Threshold-shift form of the variable-base product estimate: the product
lower integral at exponent `t + finrank ℝ E / 2` is bounded by the residual
negative `t`-power lower integral times the Japanese-bracket factor. -/
theorem lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_le_residual_power_scale
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure α} {ν : Measure E} [ν.IsAddHaarMeasure]
    {a : α → ℝ} {t R : ℝ}
    (ha_pos : ∀ᵐ x ∂μ, 0 < a x) (ht : 0 < t) :
    (∫⁻ z : α × E, ENNReal.ofReal
      ((Metric.ball (0 : E) R).indicator
        (fun u : E =>
          (a z.1 + ‖u‖ ^ 2) ^
            (-(t + (Module.finrank ℝ E : ℝ) / 2))) z.2) ∂ μ.prod ν) ≤
      (∫⁻ x : α, ENNReal.ofReal ((a x) ^ (-t)) ∂μ) *
        ∫⁻ u : E, ENNReal.ofReal
          (((1 : ℝ) + ‖u‖ ^ 2) ^
            (-(t + (Module.finrank ℝ E : ℝ) / 2))) ∂ν := by
  let s : ℝ := t + (Module.finrank ℝ E : ℝ) / 2
  have hs : (Module.finrank ℝ E : ℝ) / 2 < s := by
    dsimp [s]
    linarith
  have hexp : (Module.finrank ℝ E : ℝ) / 2 - s = -t := by
    dsimp [s]
    ring
  have hle :=
    lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_le_scale
      (E := E) (μ := μ) (ν := ν) (a := a) (s := s) (R := R) ha_pos hs
  simpa [s, hexp] using hle

/-- Finite-side threshold-shift corollary of the variable-base product
estimate.  This is the analytic bridge from a residual negative `t`-power
integrability input to the full square-suspension integrability input. -/
theorem lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_residual_power_lt_top
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure α} {ν : Measure E} [ν.IsAddHaarMeasure]
    {a : α → ℝ} {t R : ℝ}
    (ha_pos : ∀ᵐ x ∂μ, 0 < a x) (ht : 0 < t)
    (hbase :
      (∫⁻ x : α, ENNReal.ofReal ((a x) ^ (-t)) ∂μ) < ∞) :
    (∫⁻ z : α × E, ENNReal.ofReal
      ((Metric.ball (0 : E) R).indicator
        (fun u : E =>
          (a z.1 + ‖u‖ ^ 2) ^
            (-(t + (Module.finrank ℝ E : ℝ) / 2))) z.2) ∂ μ.prod ν) < ∞ := by
  let s : ℝ := t + (Module.finrank ℝ E : ℝ) / 2
  have hs : (Module.finrank ℝ E : ℝ) / 2 < s := by
    dsimp [s]
    linarith
  have hexp : (Module.finrank ℝ E : ℝ) / 2 - s = -t := by
    dsimp [s]
    ring
  have hbase' :
      (∫⁻ x : α, ENNReal.ofReal
        ((a x) ^ ((Module.finrank ℝ E : ℝ) / 2 - s)) ∂μ) < ∞ := by
    simpa [hexp] using hbase
  have hfin :=
    lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_ae_pos_of_base_lt_top
      (E := E) (μ := μ) (ν := ν) (a := a) (s := s) (R := R)
      ha_pos hs hbase'
  simpa [s] using hfin

/-- Positive-parameter global finite-side estimate in the supercritical
regime.  This comparison proof gives finiteness for each fixed `a > 0`; the
sharper dependence on `a` is supplied by the scaling equality above. -/
theorem lintegral_ofReal_norm_sq_add_pos_rpow_neg_lt_top
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {a s : ℝ}
    (ha : 0 < a) (hs : (Module.finrank ℝ E : ℝ) / 2 < s) :
    (∫⁻ x : E, ENNReal.ofReal ((a + ‖x‖ ^ 2) ^ (-s)) ∂μ) < ∞ := by
  let c : ℝ := min a 1
  have hcpos : 0 < c := lt_min ha zero_lt_one
  have hclea : c ≤ a := min_le_left _ _
  have hcle1 : c ≤ 1 := min_le_right _ _
  have hs_nonneg : 0 ≤ s := by
    have hdim_nonneg : 0 ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
    linarith
  have hmodel := integrable_one_add_norm_sq_rpow_neg (E := E) (μ := μ) hs
  have hdom : Integrable
      (fun x : E => c ^ (-s) * ((1 : ℝ) + ‖x‖ ^ 2) ^ (-s)) μ :=
    hmodel.const_mul (c ^ (-s))
  have hint : Integrable (fun x : E => (a + ‖x‖ ^ 2) ^ (-s)) μ := by
    refine hdom.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · apply Measurable.aestronglyMeasurable
      exact (measurable_const.add
        (continuous_norm.measurable.pow_const (2 : ℕ))).pow_const (-s)
    · have hx2 : 0 ≤ ‖x‖ ^ 2 := sq_nonneg ‖x‖
      have hbase_pos : 0 < a + ‖x‖ ^ 2 := by positivity
      have hmodel_pos : 0 < (1 : ℝ) + ‖x‖ ^ 2 := by positivity
      have hcbase_pos : 0 < c * ((1 : ℝ) + ‖x‖ ^ 2) := mul_pos hcpos hmodel_pos
      have hlebase : c * ((1 : ℝ) + ‖x‖ ^ 2) ≤ a + ‖x‖ ^ 2 := by
        nlinarith
      have hpow_le :
          (a + ‖x‖ ^ 2) ^ (-s) ≤ (c * ((1 : ℝ) + ‖x‖ ^ 2)) ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos hcbase_pos hlebase (by linarith [hs_nonneg])
      have hmul :
          (c * ((1 : ℝ) + ‖x‖ ^ 2)) ^ (-s) =
            c ^ (-s) * ((1 : ℝ) + ‖x‖ ^ 2) ^ (-s) := by
        rw [Real.mul_rpow (le_of_lt hcpos) (le_of_lt hmodel_pos)]
      have hnonneg_left : 0 ≤ (a + ‖x‖ ^ 2) ^ (-s) :=
        Real.rpow_nonneg (le_of_lt hbase_pos) _
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg_left]
      exact hpow_le.trans_eq hmul
  have hnonneg : ∀ x : E, 0 ≤ (a + ‖x‖ ^ 2) ^ (-s) := by
    intro x
    exact Real.rpow_nonneg (by positivity) _
  rw [← lintegral_enorm_of_nonneg hnonneg]
  exact hint.hasFiniteIntegral

end RadialFiniteSide

end Aoyagi
end DLN
end DLNFibre

end
