import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Positive-box monomial chart integrability

This file records the elementary finite-side monomial integrability estimate
needed by Aoyagi-style normal-crossing chart calculations.  It proves
integrability of products of coordinate factors on a positive box under the
strict one-dimensional inequalities `2*t*k_i < h_i + 1`.

It does not construct Aoyagi charts, compare a residual loss to a monomial,
transport a density or prior, handle endpoints or divergent sides, produce a
normal-crossing certificate, or extract pole order/RLCT.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DLNFibre
namespace DLN
namespace Aoyagi

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

end Aoyagi
end DLN
end DLNFibre

end
