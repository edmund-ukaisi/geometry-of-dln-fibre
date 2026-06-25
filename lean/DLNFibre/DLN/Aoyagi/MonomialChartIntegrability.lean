import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Monomial chart integrability on positive and signed boxes

This file records elementary finite-side monomial integrability estimates
needed by Aoyagi-style normal-crossing chart calculations.  It proves
integrability of products of coordinate factors on positive boxes and
absolute-coordinate factors on signed boxes under the strict one-dimensional
inequalities `2*t*k_i < h_i + 1`, and comparison theorems that consume
supplied loss and density/prior bounds.

It does not construct Aoyagi charts, prove the supplied loss or density/prior
bounds for those charts, handle endpoints or divergent sides, produce a
normal-crossing certificate, or extract pole order/RLCT.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- The positive-box product measure is almost everywhere supported on points
whose coordinates are strictly positive. -/
theorem ae_forall_pos_measure_pi_restrict_Ioo
    {ι : Type*} [Fintype ι] {R : ι → ℝ} :
    ∀ᵐ x : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (0 : ℝ) (R i))),
      ∀ i, 0 < x i := by
  rw [Filter.eventually_all]
  intro i
  let μ : ι → Measure ℝ := fun i => volume.restrict (Set.Ioo (0 : ℝ) (R i))
  have hi : ∀ᵐ y : ℝ ∂ μ i, 0 < y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact hy.1
  simpa [μ] using (Measure.quasiMeasurePreserving_eval (μ := μ) i).ae hi

/-- The signed-box product measure is almost everywhere supported on points
whose coordinates are nonzero, equivalently have positive absolute value. -/
theorem ae_forall_abs_pos_measure_pi_restrict_Ioo_neg
    {ι : Type*} [Fintype ι] {R : ι → ℝ} :
    ∀ᵐ x : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i))),
      ∀ i, 0 < |x i| := by
  rw [Filter.eventually_all]
  intro i
  let μ : ι → Measure ℝ := fun i => volume.restrict (Set.Ioo (-(R i)) (R i))
  have hne_volume : ∀ᵐ y : ℝ ∂ volume, y ≠ 0 := by
    simp [ae_iff, measure_singleton]
  have hi : ∀ᵐ y : ℝ ∂ μ i, 0 < |y| := by
    filter_upwards [ae_restrict_of_ae hne_volume] with y hy
    exact abs_pos.mpr hy
  simpa [μ] using (Measure.quasiMeasurePreserving_eval (μ := μ) i).ae hi

/-- One-dimensional positive-interval finite-side power integrability in
`ENNReal.ofReal` form. -/
theorem lintegral_ofReal_rpow_restrict_Ioo_lt_top
    {p R : ℝ} (hR : 0 < R) (hp : -1 < p) :
    (∫⁻ x : ℝ, ENNReal.ofReal (x ^ p)
      ∂ volume.restrict (Set.Ioo (0 : ℝ) R)) < ∞ := by
  have hintOn : IntegrableOn (fun x : ℝ => x ^ p) (Set.Ioo (0 : ℝ) R) volume :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hR).2 hp
  have hint : Integrable (fun x : ℝ => x ^ p)
      (volume.restrict (Set.Ioo (0 : ℝ) R)) := by
    simpa [IntegrableOn] using hintOn
  exact lt_of_le_of_lt
    (lintegral_ofReal_le_lintegral_enorm
      (μ := volume.restrict (Set.Ioo (0 : ℝ) R))
      (fun x : ℝ => x ^ p))
    (hasFiniteIntegral_iff_enorm.mp hint.hasFiniteIntegral)

/-- One-dimensional signed-interval finite-side power integrability, with
absolute-value coordinate factor. -/
theorem integrableOn_abs_rpow_Ioo_neg_pos
    {p R : ℝ} (hR : 0 < R) (hp : -1 < p) :
    IntegrableOn (fun x : ℝ => (|x|) ^ p) (Set.Ioo (-R) R) volume := by
  let f : ℝ → ℝ := fun x => (|x|) ^ p
  have hposPow : IntegrableOn (fun x : ℝ => x ^ p) (Set.Ioo (0 : ℝ) R) volume :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hR).2 hp
  have hpos : IntegrableOn f (Set.Ioo (0 : ℝ) R) volume := by
    refine hposPow.congr_fun ?_ measurableSet_Ioo
    intro x hx
    dsimp [f]
    rw [abs_of_pos hx.1]
  have hneg : IntegrableOn f (Set.Ioo (-R) (0 : ℝ)) volume := by
    rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
        (Homeomorph.neg ℝ).measurableEmbedding]
    simpa [f, Function.comp_def, Set.preimage, Set.Ioo, abs_neg, neg_lt, lt_neg, and_comm]
      using hpos
  have hzero : IntegrableOn f ({(0 : ℝ)} : Set ℝ) volume := by
    exact integrableOn_singleton (hfx := by simp [f]) (hx := by simp)
  have hnegZero : IntegrableOn f (Set.Ioc (-R) (0 : ℝ)) volume := by
    simpa [Set.Ioo_union_right (by linarith : -R < (0 : ℝ))] using hneg.union hzero
  simpa [f, Set.Ioc_union_Ioo_eq_Ioo (by linarith : -R ≤ (0 : ℝ)) hR] using
    hnegZero.union hpos

/-- One-dimensional signed-interval finite-side power integrability in
`ENNReal.ofReal` form, with absolute-value coordinate factor. -/
theorem lintegral_ofReal_abs_rpow_restrict_Ioo_neg_lt_top
    {p R : ℝ} (hR : 0 < R) (hp : -1 < p) :
    (∫⁻ x : ℝ, ENNReal.ofReal ((|x|) ^ p)
      ∂ volume.restrict (Set.Ioo (-R) R)) < ∞ := by
  have hfull : IntegrableOn (fun x : ℝ => (|x|) ^ p) (Set.Ioo (-R) R) volume :=
    integrableOn_abs_rpow_Ioo_neg_pos hR hp
  have hint : Integrable (fun x : ℝ => (|x|) ^ p)
      (volume.restrict (Set.Ioo (-R) R)) := by
    simpa [IntegrableOn] using hfull
  exact lt_of_le_of_lt
    (lintegral_ofReal_le_lintegral_enorm
      (μ := volume.restrict (Set.Ioo (-R) R))
      (fun x : ℝ => (|x|) ^ p))
    (hasFiniteIntegral_iff_enorm.mp hint.hasFiniteIntegral)

/-- One-dimensional monomial-chart factor integrability under Aoyagi's strict
finite-side inequality `2*t*k < h+1`. -/
theorem lintegral_ofReal_monomialFactor_restrict_Ioo_lt_top
    {h k : ℕ} {t R : ℝ} (hR : 0 < R)
    (hcrit : 2 * t * (k : ℝ) < (h : ℝ) + 1) :
    (∫⁻ x : ℝ, ENNReal.ofReal
      (x ^ ((h : ℝ) - 2 * t * (k : ℝ)))
      ∂ volume.restrict (Set.Ioo (0 : ℝ) R)) < ∞ := by
  exact lintegral_ofReal_rpow_restrict_Ioo_lt_top hR (by linarith)

/-- Finite positive-box power-product integrability under the strict
one-dimensional inequalities `-1 < p_i`. -/
theorem lintegral_ofReal_fintype_rpow_positiveBox_lt_top
    {ι : Type*} [Fintype ι] {p R : ι → ℝ}
    (hR : ∀ i, 0 < R i) (hp : ∀ i, -1 < p i) :
    (∫⁻ x : ι → ℝ, ENNReal.ofReal
      (∏ i, (x i) ^ (p i))
      ∂ Measure.pi (fun i : ι => volume.restrict (Set.Ioo (0 : ℝ) (R i)))) < ∞ := by
  let μ : ι → Measure ℝ := fun i => volume.restrict (Set.Ioo (0 : ℝ) (R i))
  let f : ι → ℝ → ℝ := fun i x => x ^ p i
  have hf : ∀ i, Integrable (f i) (μ i) := by
    intro i
    dsimp [f, μ]
    have hintOn : IntegrableOn (fun x : ℝ => x ^ p i)
        (Set.Ioo (0 : ℝ) (R i)) volume :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff (hR i)).2 (hp i)
    simpa [IntegrableOn] using hintOn
  have hint : Integrable (fun x : ι → ℝ => ∏ i, f i (x i)) (Measure.pi μ) :=
    MeasureTheory.Integrable.fintype_prod (μ := μ) (f := f) hf
  simpa [μ, f] using lt_of_le_of_lt
    (lintegral_ofReal_le_lintegral_enorm
      (μ := Measure.pi μ) (fun x : ι → ℝ => ∏ i, f i (x i)))
    (hasFiniteIntegral_iff_enorm.mp hint.hasFiniteIntegral)

/-- Finite lower-integral transfer from an a.e. upper bound by a constant
multiple of a positive-box power-product model. -/
theorem lintegral_ofReal_le_const_mul_fintype_rpow_positiveBox_lt_top
    {ι : Type*} [Fintype ι] {p R : ι → ℝ} {A : ℝ}
    {f : (ι → ℝ) → ℝ}
    (hA : 0 ≤ A) (hR : ∀ i, 0 < R i) (hp : ∀ i, -1 < p i)
    (hle : ∀ᵐ x : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (0 : ℝ) (R i))),
      f x ≤ A * ∏ i, (x i) ^ (p i)) :
    (∫⁻ x : ι → ℝ, ENNReal.ofReal (f x)
      ∂ Measure.pi (fun i : ι => volume.restrict (Set.Ioo (0 : ℝ) (R i)))) < ∞ := by
  let μ : Measure (ι → ℝ) :=
    Measure.pi (fun i : ι => volume.restrict (Set.Ioo (0 : ℝ) (R i)))
  let g : (ι → ℝ) → ℝ := fun x => ∏ i, (x i) ^ (p i)
  have hbase : (∫⁻ x : ι → ℝ, ENNReal.ofReal (g x) ∂ μ) < ∞ := by
    dsimp [g, μ]
    exact lintegral_ofReal_fintype_rpow_positiveBox_lt_top (R := R) hR hp
  have hmono :
      (∫⁻ x : ι → ℝ, ENNReal.ofReal (f x) ∂ μ) ≤
        ∫⁻ x : ι → ℝ, ENNReal.ofReal (A * g x) ∂ μ := by
    apply lintegral_mono_ae
    filter_upwards [hle] with x hx
    exact ENNReal.ofReal_le_ofReal hx
  refine lt_of_le_of_lt hmono ?_
  have hscale :
      (∫⁻ x : ι → ℝ, ENNReal.ofReal (A * g x) ∂ μ) =
        ENNReal.ofReal A * ∫⁻ x : ι → ℝ, ENNReal.ofReal (g x) ∂ μ := by
    calc
      (∫⁻ x : ι → ℝ, ENNReal.ofReal (A * g x) ∂ μ) =
          ∫⁻ x : ι → ℝ, ENNReal.ofReal A * ENNReal.ofReal (g x) ∂ μ := by
        apply lintegral_congr
        intro x
        rw [ENNReal.ofReal_mul hA]
      _ = ENNReal.ofReal A * ∫⁻ x : ι → ℝ, ENNReal.ofReal (g x) ∂ μ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [hscale]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hbase

/-- Finite positive-box monomial-chart integrability for the product of
coordinate factors `x_i^(h_i - 2*t*k_i)`. -/
theorem lintegral_ofReal_fintype_monomialFactor_positiveBox_lt_top
    {ι : Type*} [Fintype ι] {h k : ι → ℕ} {t : ℝ} {R : ι → ℝ}
    (hR : ∀ i, 0 < R i)
    (hcrit : ∀ i, 2 * t * (k i : ℝ) < (h i : ℝ) + 1) :
    (∫⁻ x : ι → ℝ, ENNReal.ofReal
      (∏ i, (x i) ^ ((h i : ℝ) - 2 * t * (k i : ℝ)))
      ∂ Measure.pi (fun i : ι => volume.restrict (Set.Ioo (0 : ℝ) (R i)))) < ∞ := by
  exact lintegral_ofReal_fintype_rpow_positiveBox_lt_top
    (R := R) hR (fun i => by linarith [hcrit i])

/-- Finite signed-box absolute-power-product integrability under the strict
one-dimensional inequalities `-1 < p_i`. -/
theorem lintegral_ofReal_fintype_abs_rpow_signedBox_lt_top
    {ι : Type*} [Fintype ι] {p R : ι → ℝ}
    (hR : ∀ i, 0 < R i) (hp : ∀ i, -1 < p i) :
    (∫⁻ x : ι → ℝ, ENNReal.ofReal
      (∏ i, (|x i|) ^ (p i))
      ∂ Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))) < ∞ := by
  let μ : ι → Measure ℝ := fun i => volume.restrict (Set.Ioo (-(R i)) (R i))
  let f : ι → ℝ → ℝ := fun i x => (|x|) ^ p i
  have hf : ∀ i, Integrable (f i) (μ i) := by
    intro i
    dsimp [f, μ]
    have hintOn : IntegrableOn (fun x : ℝ => (|x|) ^ p i)
        (Set.Ioo (-(R i)) (R i)) volume := by
      exact integrableOn_abs_rpow_Ioo_neg_pos (hR i) (hp i)
    simpa [IntegrableOn] using hintOn
  have hint : Integrable (fun x : ι → ℝ => ∏ i, f i (x i)) (Measure.pi μ) :=
    MeasureTheory.Integrable.fintype_prod (μ := μ) (f := f) hf
  simpa [μ, f] using lt_of_le_of_lt
    (lintegral_ofReal_le_lintegral_enorm
      (μ := Measure.pi μ) (fun x : ι → ℝ => ∏ i, f i (x i)))
    (hasFiniteIntegral_iff_enorm.mp hint.hasFiniteIntegral)

/-- Finite signed-box monomial-chart integrability for the product of
absolute-coordinate factors `|x_i|^(h_i - 2*t*k_i)`. -/
theorem lintegral_ofReal_fintype_abs_monomialFactor_signedBox_lt_top
    {ι : Type*} [Fintype ι] {h k : ι → ℕ} {t : ℝ} {R : ι → ℝ}
    (hR : ∀ i, 0 < R i)
    (hcrit : ∀ i, 2 * t * (k i : ℝ) < (h i : ℝ) + 1) :
    (∫⁻ x : ι → ℝ, ENNReal.ofReal
      (∏ i, (|x i|) ^ ((h i : ℝ) - 2 * t * (k i : ℝ)))
      ∂ Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))) < ∞ := by
  exact lintegral_ofReal_fintype_abs_rpow_signedBox_lt_top
    (R := R) hR (fun i => by linarith [hcrit i])

/-- Finite lower-integral transfer from an a.e. upper bound by a constant
multiple of a signed-box absolute-power-product model. -/
theorem lintegral_ofReal_le_const_mul_fintype_abs_rpow_signedBox_lt_top
    {ι : Type*} [Fintype ι] {p R : ι → ℝ} {A : ℝ}
    {f : (ι → ℝ) → ℝ}
    (hA : 0 ≤ A) (hR : ∀ i, 0 < R i) (hp : ∀ i, -1 < p i)
    (hle : ∀ᵐ x : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i))),
      f x ≤ A * ∏ i, (|x i|) ^ (p i)) :
    (∫⁻ x : ι → ℝ, ENNReal.ofReal (f x)
      ∂ Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))) < ∞ := by
  let μ : Measure (ι → ℝ) :=
    Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))
  let g : (ι → ℝ) → ℝ := fun x => ∏ i, (|x i|) ^ (p i)
  have hbase : (∫⁻ x : ι → ℝ, ENNReal.ofReal (g x) ∂ μ) < ∞ := by
    dsimp [g, μ]
    exact lintegral_ofReal_fintype_abs_rpow_signedBox_lt_top (R := R) hR hp
  have hmono :
      (∫⁻ x : ι → ℝ, ENNReal.ofReal (f x) ∂ μ) ≤
        ∫⁻ x : ι → ℝ, ENNReal.ofReal (A * g x) ∂ μ := by
    apply lintegral_mono_ae
    filter_upwards [hle] with x hx
    exact ENNReal.ofReal_le_ofReal hx
  refine lt_of_le_of_lt hmono ?_
  have hscale :
      (∫⁻ x : ι → ℝ, ENNReal.ofReal (A * g x) ∂ μ) =
        ENNReal.ofReal A * ∫⁻ x : ι → ℝ, ENNReal.ofReal (g x) ∂ μ := by
    calc
      (∫⁻ x : ι → ℝ, ENNReal.ofReal (A * g x) ∂ μ) =
          ∫⁻ x : ι → ℝ, ENNReal.ofReal A * ENNReal.ofReal (g x) ∂ μ := by
        apply lintegral_congr
        intro x
        rw [ENNReal.ofReal_mul hA]
      _ = ENNReal.ofReal A * ∫⁻ x : ι → ℝ, ENNReal.ofReal (g x) ∂ μ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [hscale]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hbase

/-- Aoyagi-exponent form of finite lower-integral transfer from an a.e. upper
bound by a constant multiple of the signed-box absolute monomial model. -/
theorem lintegral_ofReal_le_const_mul_fintype_abs_monomialFactor_signedBox_lt_top
    {ι : Type*} [Fintype ι] {h k : ι → ℕ} {t : ℝ} {R : ι → ℝ} {A : ℝ}
    {f : (ι → ℝ) → ℝ}
    (hA : 0 ≤ A) (hR : ∀ i, 0 < R i)
    (hcrit : ∀ i, 2 * t * (k i : ℝ) < (h i : ℝ) + 1)
    (hle : ∀ᵐ x : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i))),
      f x ≤ A * ∏ i, (|x i|) ^ ((h i : ℝ) - 2 * t * (k i : ℝ))) :
    (∫⁻ x : ι → ℝ, ENNReal.ofReal (f x)
      ∂ Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))) < ∞ := by
  exact lintegral_ofReal_le_const_mul_fintype_abs_rpow_signedBox_lt_top
    (p := fun i => (h i : ℝ) - 2 * t * (k i : ℝ)) (R := R)
    hA hR (fun i => by linarith [hcrit i]) hle

/-- Aoyagi-exponent form of finite lower-integral transfer from an a.e. upper
bound by a constant multiple of the positive-box monomial model. -/
theorem lintegral_ofReal_le_const_mul_fintype_monomialFactor_positiveBox_lt_top
    {ι : Type*} [Fintype ι] {h k : ι → ℕ} {t : ℝ} {R : ι → ℝ} {A : ℝ}
    {f : (ι → ℝ) → ℝ}
    (hA : 0 ≤ A) (hR : ∀ i, 0 < R i)
    (hcrit : ∀ i, 2 * t * (k i : ℝ) < (h i : ℝ) + 1)
    (hle : ∀ᵐ x : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (0 : ℝ) (R i))),
      f x ≤ A * ∏ i, (x i) ^ ((h i : ℝ) - 2 * t * (k i : ℝ))) :
    (∫⁻ x : ι → ℝ, ENNReal.ofReal (f x)
      ∂ Measure.pi (fun i : ι => volume.restrict (Set.Ioo (0 : ℝ) (R i)))) < ∞ := by
  exact lintegral_ofReal_le_const_mul_fintype_rpow_positiveBox_lt_top
    (p := fun i => (h i : ℝ) - 2 * t * (k i : ℝ)) (R := R)
    hA hR (fun i => by linarith [hcrit i]) hle

/-- Pointwise positive-box loss-density domination.  If a loss is bounded
below by a positive constant times the squared monomial model and a
nonnegative density is bounded above by a constant times the Jacobian/prior
monomial, then `loss^(-t) * density` is bounded by the Aoyagi finite-side
monomial. -/
theorem loss_rpow_neg_mul_density_le_const_mul_monomialFactor_of_pos
    {ι : Type*} [Fintype ι] {h k : ι → ℕ} {t c C loss density : ℝ}
    {x : ι → ℝ}
    (hc : 0 < c) (ht : 0 ≤ t) (hxpos : ∀ i, 0 < x i)
    (hloss : c * ∏ i, (x i) ^ (2 * (k i : ℝ)) ≤ loss)
    (hdensity_nonneg : 0 ≤ density)
    (hdensity_le : density ≤ C * ∏ i, (x i) ^ (h i : ℝ)) :
    loss ^ (-t) * density ≤
      (c ^ (-t) * C) *
        ∏ i, (x i) ^ ((h i : ℝ) - 2 * t * (k i : ℝ)) := by
  let M : ℝ := ∏ i, (x i) ^ (2 * (k i : ℝ))
  let H : ℝ := ∏ i, (x i) ^ (h i : ℝ)
  have hMpos : 0 < M := by
    dsimp [M]
    exact Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hxpos i) _
  have hcMpos : 0 < c * M := mul_pos hc hMpos
  have hloss_pos : 0 < loss := lt_of_lt_of_le hcMpos hloss
  have hpow_le : loss ^ (-t) ≤ c ^ (-t) * M ^ (-t) := by
    have hle : loss ^ (-t) ≤ (c * M) ^ (-t) :=
      Real.rpow_le_rpow_of_nonpos hcMpos hloss (by linarith)
    have hmul : (c * M) ^ (-t) = c ^ (-t) * M ^ (-t) := by
      rw [Real.mul_rpow hc.le hMpos.le]
    exact hle.trans_eq hmul
  have hscale_nonneg : 0 ≤ c ^ (-t) * M ^ (-t) :=
    mul_nonneg (Real.rpow_nonneg hc.le _) (Real.rpow_nonneg hMpos.le _)
  have hmodel :
      M ^ (-t) * H =
        ∏ i, (x i) ^ ((h i : ℝ) - 2 * t * (k i : ℝ)) := by
    have hMpow :
        M ^ (-t) = ∏ i, (x i) ^ (-(2 * t * (k i : ℝ))) := by
      dsimp [M]
      rw [← Real.finset_prod_rpow Finset.univ
        (fun i => (x i) ^ (2 * (k i : ℝ))) (fun i _ =>
          (Real.rpow_nonneg (hxpos i).le _)) (-t)]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Real.rpow_mul (hxpos i).le (2 * (k i : ℝ)) (-t)]
      ring_nf
    rw [hMpow]
    dsimp [H]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.rpow_add (hxpos i)]
    ring_nf
  calc
    loss ^ (-t) * density ≤ (c ^ (-t) * M ^ (-t)) * density :=
      mul_le_mul_of_nonneg_right hpow_le hdensity_nonneg
    _ ≤ (c ^ (-t) * M ^ (-t)) * (C * H) :=
      mul_le_mul_of_nonneg_left hdensity_le hscale_nonneg
    _ = (c ^ (-t) * C) * (M ^ (-t) * H) := by ring
    _ = (c ^ (-t) * C) *
        ∏ i, (x i) ^ ((h i : ℝ) - 2 * t * (k i : ℝ)) := by
      rw [hmodel]

/-- Pointwise signed-box loss-density domination.  This is the absolute-value
analogue of `loss_rpow_neg_mul_density_le_const_mul_monomialFactor_of_pos`,
used away from the coordinate hyperplanes. -/
theorem loss_rpow_neg_mul_density_le_const_mul_abs_monomialFactor_of_abs_pos
    {ι : Type*} [Fintype ι] {h k : ι → ℕ} {t c C loss density : ℝ}
    {x : ι → ℝ}
    (hc : 0 < c) (ht : 0 ≤ t) (hxabs : ∀ i, 0 < |x i|)
    (hloss : c * ∏ i, (|x i|) ^ (2 * (k i : ℝ)) ≤ loss)
    (hdensity_nonneg : 0 ≤ density)
    (hdensity_le : density ≤ C * ∏ i, (|x i|) ^ (h i : ℝ)) :
    loss ^ (-t) * density ≤
      (c ^ (-t) * C) *
        ∏ i, (|x i|) ^ ((h i : ℝ) - 2 * t * (k i : ℝ)) := by
  let M : ℝ := ∏ i, (|x i|) ^ (2 * (k i : ℝ))
  let H : ℝ := ∏ i, (|x i|) ^ (h i : ℝ)
  have hMpos : 0 < M := by
    dsimp [M]
    exact Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hxabs i) _
  have hcMpos : 0 < c * M := mul_pos hc hMpos
  have hloss_pos : 0 < loss := lt_of_lt_of_le hcMpos hloss
  have hpow_le : loss ^ (-t) ≤ c ^ (-t) * M ^ (-t) := by
    have hle : loss ^ (-t) ≤ (c * M) ^ (-t) :=
      Real.rpow_le_rpow_of_nonpos hcMpos hloss (by linarith)
    have hmul : (c * M) ^ (-t) = c ^ (-t) * M ^ (-t) := by
      rw [Real.mul_rpow hc.le hMpos.le]
    exact hle.trans_eq hmul
  have hscale_nonneg : 0 ≤ c ^ (-t) * M ^ (-t) :=
    mul_nonneg (Real.rpow_nonneg hc.le _) (Real.rpow_nonneg hMpos.le _)
  have hmodel :
      M ^ (-t) * H =
        ∏ i, (|x i|) ^ ((h i : ℝ) - 2 * t * (k i : ℝ)) := by
    have hMpow :
        M ^ (-t) = ∏ i, (|x i|) ^ (-(2 * t * (k i : ℝ))) := by
      dsimp [M]
      rw [← Real.finset_prod_rpow Finset.univ
        (fun i => (|x i|) ^ (2 * (k i : ℝ))) (fun i _ =>
          (Real.rpow_nonneg (hxabs i).le _)) (-t)]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Real.rpow_mul (hxabs i).le (2 * (k i : ℝ)) (-t)]
      ring_nf
    rw [hMpow]
    dsimp [H]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.rpow_add (hxabs i)]
    ring_nf
  calc
    loss ^ (-t) * density ≤ (c ^ (-t) * M ^ (-t)) * density :=
      mul_le_mul_of_nonneg_right hpow_le hdensity_nonneg
    _ ≤ (c ^ (-t) * M ^ (-t)) * (C * H) :=
      mul_le_mul_of_nonneg_left hdensity_le hscale_nonneg
    _ = (c ^ (-t) * C) * (M ^ (-t) * H) := by ring
    _ = (c ^ (-t) * C) *
        ∏ i, (|x i|) ^ ((h i : ℝ) - 2 * t * (k i : ℝ)) := by
      rw [hmodel]

/-- Positive-box residual/density finite-side comparison.  Explicit a.e.
monomial lower control on `loss` and upper control on `density` imply finite
lower integral of `loss^(-t) * density` under Aoyagi's strict inequalities. -/
theorem lintegral_ofReal_loss_rpow_neg_mul_density_positiveBox_lt_top
    {ι : Type*} [Fintype ι] {h k : ι → ℕ} {t : ℝ} {R : ι → ℝ} {c C : ℝ}
    {loss density : (ι → ℝ) → ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (ht : 0 ≤ t) (hR : ∀ i, 0 < R i)
    (hcrit : ∀ i, 2 * t * (k i : ℝ) < (h i : ℝ) + 1)
    (hloss : ∀ᵐ x : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (0 : ℝ) (R i))),
      c * ∏ i, (x i) ^ (2 * (k i : ℝ)) ≤ loss x)
    (hdensity_nonneg : ∀ᵐ x : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (0 : ℝ) (R i))),
      0 ≤ density x)
    (hdensity_le : ∀ᵐ x : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (0 : ℝ) (R i))),
      density x ≤ C * ∏ i, (x i) ^ (h i : ℝ)) :
    (∫⁻ x : ι → ℝ, ENNReal.ofReal ((loss x) ^ (-t) * density x)
      ∂ Measure.pi (fun i : ι => volume.restrict (Set.Ioo (0 : ℝ) (R i)))) < ∞ := by
  let μ : Measure (ι → ℝ) :=
    Measure.pi (fun i : ι => volume.restrict (Set.Ioo (0 : ℝ) (R i)))
  let A : ℝ := c ^ (-t) * C
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (Real.rpow_nonneg hc.le _) hC
  refine lintegral_ofReal_le_const_mul_fintype_monomialFactor_positiveBox_lt_top
    (h := h) (k := k) (t := t) (R := R) (A := A)
    (f := fun x => (loss x) ^ (-t) * density x)
    hA hR hcrit ?_
  have hpos := ae_forall_pos_measure_pi_restrict_Ioo (R := R) (ι := ι)
  filter_upwards [hpos, hloss, hdensity_nonneg, hdensity_le] with x hxpos hxloss hxdens_nonneg
    hxdens_le
  simpa [A] using
    loss_rpow_neg_mul_density_le_const_mul_monomialFactor_of_pos
      (h := h) (k := k) (t := t) (c := c) (C := C)
      (loss := loss x) (density := density x) (x := x)
      hc ht hxpos hxloss hxdens_nonneg hxdens_le

/-- Signed-box residual/density finite-side comparison.  Explicit a.e.
absolute-monomial lower control on `loss` and upper control on `density`
imply finite lower integral of `loss^(-t) * density` under Aoyagi's strict
inequalities. -/
theorem lintegral_ofReal_loss_rpow_neg_mul_density_signedBox_lt_top
    {ι : Type*} [Fintype ι] {h k : ι → ℕ} {t : ℝ} {R : ι → ℝ} {c C : ℝ}
    {loss density : (ι → ℝ) → ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (ht : 0 ≤ t) (hR : ∀ i, 0 < R i)
    (hcrit : ∀ i, 2 * t * (k i : ℝ) < (h i : ℝ) + 1)
    (hloss : ∀ᵐ x : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i))),
      c * ∏ i, (|x i|) ^ (2 * (k i : ℝ)) ≤ loss x)
    (hdensity_nonneg : ∀ᵐ x : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i))),
      0 ≤ density x)
    (hdensity_le : ∀ᵐ x : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i))),
      density x ≤ C * ∏ i, (|x i|) ^ (h i : ℝ)) :
    (∫⁻ x : ι → ℝ, ENNReal.ofReal ((loss x) ^ (-t) * density x)
      ∂ Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))) < ∞ := by
  let μ : Measure (ι → ℝ) :=
    Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))
  let A : ℝ := c ^ (-t) * C
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (Real.rpow_nonneg hc.le _) hC
  refine lintegral_ofReal_le_const_mul_fintype_abs_monomialFactor_signedBox_lt_top
    (h := h) (k := k) (t := t) (R := R) (A := A)
    (f := fun x => (loss x) ^ (-t) * density x)
    hA hR hcrit ?_
  have hpos := ae_forall_abs_pos_measure_pi_restrict_Ioo_neg (R := R) (ι := ι)
  filter_upwards [hpos, hloss, hdensity_nonneg, hdensity_le] with x hxabs hxloss hxdens_nonneg
    hxdens_le
  simpa [A] using
    loss_rpow_neg_mul_density_le_const_mul_abs_monomialFactor_of_abs_pos
      (h := h) (k := k) (t := t) (c := c) (C := C)
      (loss := loss x) (density := density x) (x := x)
      hc ht hxabs hxloss hxdens_nonneg hxdens_le

end Aoyagi
end DLN
end DLNFibre

end
