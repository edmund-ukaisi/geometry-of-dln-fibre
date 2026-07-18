import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# `DLNFibre.DLN.RLCT.Foundations.S1ScalingBridge` — the homogeneity scaling bridge (route (b))

The single new analytic lemma the transform-only engine's `region_glue` needs on route (b): for a
measurable, nonnegative, degree-`D` homogeneous `F : (Fin N → ℝ) → ℝ`, the singular integral of
`F^{-c'}` over a scaled set `ε • K` differs from that over `K` by the pure power `ε^(N − D·c')`:

    ∫_{ε • K} F^{-c'} = ε^(N − D·c') · ∫_K F^{-c'}.

The homogeneity `F(ε • x) = ε^D · F(x)` is the ONLY DLN-specific input (banked downstream as the
global-scaling homogeneity of the DLN loss, degree `D = 2L`). Everything here is Haar change of
variables (`map_addHaar_smul`) + `rpow` bookkeeping — engine-independent, foundation-grade.

## Structure
- `lintegral_smul_set` — the pure Haar CoV: `∫_{ε•K} h = ε^N · ∫_K (h ∘ (ε • ·))`, any measurable
  `h : (Fin N → ℝ) → ℝ≥0∞`, `ε > 0`. No homogeneity, no `F`.
- `lintegral_rpow_neg_smul_bridge` — the scaling bridge proper, folding in the homogeneity to turn
  the `h ∘ (ε • ·)` into the constant `ε^(−D·c')` times the original integrand.
-/

open MeasureTheory Set
open scoped ENNReal Topology BigOperators Pointwise

namespace DLNFibre.DLN.RLCT

variable {N : ℕ}

/-- **The pure Haar scaling change-of-variables for a `lintegral` over a scaled set.** For `ε > 0`
and measurable `K`, `∫_{ε • K} h ∂volume = ε^N · ∫_K (h ∘ (ε • ·)) ∂volume`. The scaling `ε • ·` is
a measurable equivalence with `Measure.map` law `map (ε•·) volume = (ε^N)⁻¹ • volume`
(`map_addHaar_smul`), and `finrank ℝ (Fin N → ℝ) = N`. -/
theorem lintegral_smul_set (h : (Fin N → ℝ) → ℝ≥0∞) (ε : ℝ) (hε : 0 < ε)
    (K : Set (Fin N → ℝ)) (hK : MeasurableSet K) :
    ∫⁻ y in ε • K, h y = ENNReal.ofReal (ε ^ N) * ∫⁻ x in K, h (ε • x) := by
  have hεne : ε ≠ 0 := ne_of_gt hε
  -- the scaling measurable equivalence `Te x = ε • x`
  set Te : (Fin N → ℝ) ≃ᵐ (Fin N → ℝ) := (Homeomorph.smulOfNeZero ε hεne).toMeasurableEquiv with hTe
  have hTeapp : ∀ x, Te x = ε • x := fun _ => rfl
  -- the image form of the scaled set + its measurability
  have himg : ε • K = ⇑Te '' K := by
    rw [← Set.image_smul]; rfl
  have hmeasImg : MeasurableSet (ε • K) := by
    rw [himg]; exact Te.measurableSet_image.mpr hK
  -- the Haar scaling law: `map Te volume = (ε^N)⁻¹ • volume`
  have hpos : (0 : ℝ) < ε ^ N := pow_pos hε N
  have hmap : Measure.map Te (volume : Measure (Fin N → ℝ))
      = ENNReal.ofReal ((ε ^ N)⁻¹) • (volume : Measure (Fin N → ℝ)) := by
    have h1 := MeasureTheory.Measure.map_addHaar_smul (volume : Measure (Fin N → ℝ)) hεne
    rw [Module.finrank_fin_fun, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (ε ^ N)⁻¹)] at h1
    exact h1
  -- the pointwise indicator transport `K.indicator (h ∘ (ε•·)) x = (ε•K).indicator h (Te x)`
  have hind : ∀ x, K.indicator (fun x => h (ε • x)) x = (ε • K).indicator h (Te x) := by
    intro x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx, hTeapp,
        Set.indicator_of_mem (by rw [himg]; exact ⟨x, hx, rfl⟩ : ε • x ∈ ε • K)]
    · rw [Set.indicator_of_notMem hx, hTeapp,
        Set.indicator_of_notMem (by
          rw [himg]; rintro ⟨y, hy, hxy⟩
          exact hx (by rwa [Te.injective hxy] at hy) : ε • x ∉ ε • K)]
  -- assemble: RHS-inner integral = (ε^N)⁻¹ · LHS
  have hstep : ∫⁻ x in K, h (ε • x)
      = ENNReal.ofReal ((ε ^ N)⁻¹) * ∫⁻ y in ε • K, h y := by
    rw [← lintegral_indicator hK, ← lintegral_indicator hmeasImg]
    calc ∫⁻ x, K.indicator (fun x => h (ε • x)) x
        = ∫⁻ x, (ε • K).indicator h (Te x) := by
          refine lintegral_congr fun x => hind x
      _ = ∫⁻ y, (ε • K).indicator h y ∂(Measure.map Te volume) :=
          (lintegral_map_equiv ((ε • K).indicator h) Te).symm
      _ = ∫⁻ y, (ε • K).indicator h y ∂(ENNReal.ofReal ((ε ^ N)⁻¹) • volume) := by rw [hmap]
      _ = ENNReal.ofReal ((ε ^ N)⁻¹) * ∫⁻ y, (ε • K).indicator h y :=
          lintegral_smul_measure _ _
  -- multiply through by ε^N, cancelling ε^N · (ε^N)⁻¹ = 1
  rw [hstep, ← mul_assoc, ← ENNReal.ofReal_mul hpos.le, mul_inv_cancel₀ (ne_of_gt hpos),
    ENNReal.ofReal_one, one_mul]

/-- **The homogeneity scaling bridge** (the one new analytic lemma, route (b)). For a measurable,
nonnegative, degree-`D` homogeneous `F` on `Fin N → ℝ`,

    ∫_{ε • K} F^{-c'} = ε^(N − D·c') · ∫_K F^{-c'}     (ε > 0, K measurable).

`ε^(N − D·c')` is a finite positive constant, so the box integral is finite iff any positive
rescaling of the box is — the homogeneity-cone finiteness transfer `region_glue` uses. -/
theorem lintegral_rpow_neg_smul_bridge (F : (Fin N → ℝ) → ℝ) (D : ℕ) (c' ε : ℝ)
    (K : Set (Fin N → ℝ)) (hFnn : ∀ x, 0 ≤ F x)
    (hhomog : ∀ (c : ℝ) (w : Fin N → ℝ), F (c • w) = c ^ D * F w)
    (hε : 0 < ε) (hK : MeasurableSet K) :
    ∫⁻ y in ε • K, ENNReal.ofReal (F y ^ (-c'))
      = ENNReal.ofReal (ε ^ ((N : ℝ) - D * c')) * ∫⁻ x in K, ENNReal.ofReal (F x ^ (-c')) := by
  rw [lintegral_smul_set (fun y => ENNReal.ofReal (F y ^ (-c'))) ε hε K hK]
  -- rewrite the pulled-back integrand: `(F (ε•x))^{-c'} = ε^{-D c'} · (F x)^{-c'}`
  have hεD : (0 : ℝ) ≤ ε ^ D := (pow_pos hε D).le
  have hpow : (ε ^ D : ℝ) ^ (-c') = ε ^ (-((D : ℝ) * c')) := by
    rw [← Real.rpow_natCast ε D, ← Real.rpow_mul hε.le]
    congr 1; ring
  have hintegrand : ∀ x, ENNReal.ofReal (F (ε • x) ^ (-c'))
      = ENNReal.ofReal (ε ^ (-((D : ℝ) * c'))) * ENNReal.ofReal (F x ^ (-c')) := by
    intro x
    rw [hhomog ε x, Real.mul_rpow hεD (hFnn x), hpow,
      ENNReal.ofReal_mul (Real.rpow_nonneg hε.le _)]
  -- pull the constant out of the inner integral, then merge the two `ε`-powers
  calc ENNReal.ofReal (ε ^ N) * ∫⁻ x in K, ENNReal.ofReal (F (ε • x) ^ (-c'))
      = ENNReal.ofReal (ε ^ N)
          * ∫⁻ x in K, ENNReal.ofReal (ε ^ (-((D : ℝ) * c'))) * ENNReal.ofReal (F x ^ (-c')) := by
        refine congrArg _ (lintegral_congr fun x => hintegrand x)
    _ = ENNReal.ofReal (ε ^ N) * ENNReal.ofReal (ε ^ (-((D : ℝ) * c')))
          * ∫⁻ x in K, ENNReal.ofReal (F x ^ (-c')) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_assoc]
    _ = ENNReal.ofReal (ε ^ ((N : ℝ) - D * c')) * ∫⁻ x in K, ENNReal.ofReal (F x ^ (-c')) := by
        rw [← ENNReal.ofReal_mul (pow_pos hε N).le, ← Real.rpow_natCast ε N,
          ← Real.rpow_add hε, sub_eq_add_neg]

end DLNFibre.DLN.RLCT
