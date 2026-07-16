import DLNFibre.DLN.RLCT.Validate.RouteMSchurWishartWeight
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

set_option linter.style.longLine false

/-!
# `RouteMSJInteriorShell` — the tight-interior log-integrability (couplerad §w3-deep)

**Thread (aoyagi-full Stage 2), the interior coupled shell-integration.** The interior charge integral
`∫_cell < ⊤` (for the generic cell `a+b ≤ ρ`, `ρ = min(M₂, n_last)`) splits by the smallest singular value
`σ_ρ(S)` of the deep factor `S`. This module owns the `σ_ρ → 0` TIGHT shells; schurB's uniform atom
`chargedWishartWeight_fullDeepRank_lt_top` covers the BULK `{σ_ρ ≥ δ₀}` (and, unified, is optional — the
graded log bound is valid for all `σ_ρ`).

The crux (couplerad §w3-deep): the per-shell charge weight grows only **logarithmically** in `1/σ_ρ`,
`W(S) ≤ C·(1 + log(1/σ_ρ))` (the top `ρ−1` singular directions are order-1; only `σ_ρ ~ ε` is small),
while the `σ_ρ`-measure of the shell `{σ_ρ ~ ε}` is `~ ε^{c−1} dε` with `c = codim{rank S ≤ ρ−1} =
(M₂−ρ+1)(n−ρ+1) ≥ 1`. Hence

    ∫_{σ_ρ < δ₀} W dS ≤ ∫₀^{δ₀} C·(1 + log(1/ε))·ε^{c−1} dε < ∞   (converges since c ≥ 1).

The `s = c−1 ≥ 0 > −1` power is integrable near `0`; the log factor is dominated by an arbitrarily small
power `log(1/ε) ≤ η⁻¹·ε^{−η}` (any `η > 0`), reducing the whole thing to a power integral `∫ ε^{s−η}`
finite for `s−η > −1` (the §w3-deep "option II" Lean route; couplerad's recommended σ^{−κ} domination).
This is the genuinely-new log-machinery; the naive uniform-atom `ε^{−ab}` bound would DIVERGE (`c = ab`
borderline), the graded log bound converges.

## Contents (this milestone — the analytic convergence core)
- `log_one_div_le_rpow_neg` — log-vs-power domination `log(1/x) ≤ η⁻¹·x^{−η}` (network-free, `x, η > 0`).
- `shellLogWeight_integrableOn` — the tight-shell weight `C·(1+log(1/ε))·ε^s` is integrable on `(0,t)`
  (`0 < t ≤ 1`, `−1 < s`, `0 ≤ C`); the analytic convergence core (Bochner form).
- `shellLogWeight_lintegral_lt_top` — the `ℝ≥0∞` form: `∫⁻ ε in Ioc 0 t, ofReal(C·(1+log(1/ε))·ε^s) < ⊤`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace DLNFibre.DLN.RLCT

/-- **Log-vs-power domination.** For `η > 0` and `x > 0`, `log(1/x) ≤ η⁻¹·x^{−η}`. (No `x ≤ 1` needed:
for `x ≥ 1` the LHS is `≤ 0` and the RHS is `> 0`.) Proof: with `y = x⁻¹`, `η·log y = log(y^η) ≤ y^η − 1
≤ y^η` (`Real.log_le_sub_one_of_pos`); divide by `η`, and `y^η = x^{−η}`. This is the §w3-deep step-4
"option II" trick that converts the tight-shell log charge into an arbitrarily small power. -/
theorem log_one_div_le_rpow_neg {η x : ℝ} (hη : 0 < η) (hx : 0 < x) :
    Real.log (1 / x) ≤ η⁻¹ * x ^ (-η) := by
  have hx0 : (0 : ℝ) ≤ x := hx.le
  have hxinv : (0 : ℝ) < x⁻¹ := inv_pos.mpr hx
  rw [one_div]
  -- x^(-η) = (x⁻¹)^η
  have hpow : x ^ (-η) = (x⁻¹) ^ η := by rw [Real.inv_rpow hx0, Real.rpow_neg hx0]
  rw [hpow]
  set y := x⁻¹ with hy
  -- η·log y = log(y^η) ≤ y^η − 1 ≤ y^η
  have hlog : η * Real.log y = Real.log (y ^ η) := (Real.log_rpow hxinv η).symm
  have hstep : Real.log (y ^ η) ≤ y ^ η - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hxinv η)
  have h2 : η * Real.log y ≤ y ^ η := by rw [hlog]; linarith
  -- divide by η > 0
  have h3 := mul_le_mul_of_nonneg_left h2 (le_of_lt (inv_pos.mpr hη))
  rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hη), one_mul] at h3

/-- **The tight-shell log weight is integrable near `0`.** For `0 < t ≤ 1`, `−1 < s`, `0 ≤ C`, the weight
`ε ↦ C·(1 + log(1/ε))·ε^s` is Bochner-integrable on `(0, t)`. This is couplerad's §w3-deep tight-shell
convergence: the graded log charge `C·(1 + log(1/σ_ρ))` against the `ε^{c−1} dε` shell measure (`s = c−1`,
`c ≥ 1` ⟹ `s ≥ 0 > −1`). Route: dominate `log(1/ε) ≤ η⁻¹·ε^{−η}` with `η = (s+1)/2 > 0`, so the weight is
`≤ C·(ε^s + η⁻¹·ε^{s−η})`, a sum of power integrals finite near `0` (`s > −1` and `s − η > −1`). -/
theorem shellLogWeight_integrableOn {t s C : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hs : -1 < s) (hC : 0 ≤ C) :
    IntegrableOn (fun ε => C * (1 + Real.log (1 / ε)) * ε ^ s) (Ioo (0 : ℝ) t) := by
  classical
  set η : ℝ := (s + 1) / 2 with hη
  have hηpos : 0 < η := by rw [hη]; linarith
  have hsη : -1 < s - η := by rw [hη]; linarith
  -- the dominating function `g ε = C·ε^s + (C·η⁻¹)·ε^{s−η}`, integrable near 0
  have h1 : IntegrableOn (fun ε => ε ^ s) (Ioo (0 : ℝ) t) volume :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff ht).mpr hs
  have h2 : IntegrableOn (fun ε => ε ^ (s - η)) (Ioo (0 : ℝ) t) volume :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff ht).mpr hsη
  have hg : IntegrableOn (fun ε => C * ε ^ s + (C * η⁻¹) * ε ^ (s - η)) (Ioo (0 : ℝ) t) volume :=
    (h1.const_mul C).add (h2.const_mul (C * η⁻¹))
  -- measurability of the weight
  have hmeas : AEStronglyMeasurable
      (fun ε => C * (1 + Real.log (1 / ε)) * ε ^ s) (volume.restrict (Ioo (0 : ℝ) t)) := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  -- the pointwise bound on `(0, t)`
  refine Integrable.mono' hg hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with ε hε
  obtain ⟨hε0, hεt⟩ := hε
  have hε1 : ε < 1 := lt_of_lt_of_le hεt ht1
  have hεs : (0 : ℝ) < ε ^ s := Real.rpow_pos_of_pos hε0 s
  have hlogpos : 0 ≤ Real.log (1 / ε) := by
    rw [one_div]
    exact Real.log_nonneg (by rw [le_inv_comm₀ (by norm_num) hε0]; simpa using hε1.le)
  -- the weight is nonneg, so `‖·‖ = ·`
  have hfnn : 0 ≤ C * (1 + Real.log (1 / ε)) * ε ^ s := by positivity
  rw [Real.norm_of_nonneg hfnn]
  -- `(1 + log(1/ε))·ε^s ≤ ε^s + η⁻¹·ε^{s−η}`
  have hdom : Real.log (1 / ε) ≤ η⁻¹ * ε ^ (-η) := log_one_div_le_rpow_neg hηpos hε0
  have hcross : η⁻¹ * ε ^ (-η) * ε ^ s = η⁻¹ * ε ^ (s - η) := by
    rw [mul_assoc, ← Real.rpow_add hε0]; ring_nf
  calc C * (1 + Real.log (1 / ε)) * ε ^ s
      = C * ((1 + Real.log (1 / ε)) * ε ^ s) := by ring
    _ ≤ C * ((1 + η⁻¹ * ε ^ (-η)) * ε ^ s) := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply mul_le_mul_of_nonneg_right _ hεs.le
        linarith
    _ = C * (ε ^ s + η⁻¹ * ε ^ (-η) * ε ^ s) := by ring
    _ = C * (ε ^ s + η⁻¹ * ε ^ (s - η)) := by rw [hcross]
    _ = C * ε ^ s + (C * η⁻¹) * ε ^ (s - η) := by ring

/-- **The tight-shell log weight has finite lower Lebesgue integral (`ℝ≥0∞` form).** The `< ⊤` restatement
of `shellLogWeight_integrableOn` over the half-open shell `Ioc 0 t` (differing from `Ioo 0 t` by the null
set `{t}`), in the shape the coupled per-cell finiteness consumes. -/
theorem shellLogWeight_lintegral_lt_top {t s C : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hs : -1 < s)
    (hC : 0 ≤ C) :
    (∫⁻ ε in Ioc (0 : ℝ) t, ENNReal.ofReal (C * (1 + Real.log (1 / ε)) * ε ^ s)) < ⊤ := by
  classical
  -- move to `Ioo 0 t` (they agree a.e. under `volume`)
  have hae : (Ioo (0 : ℝ) t : Set ℝ) =ᵐ[volume] Ioc (0 : ℝ) t := Ioo_ae_eq_Ioc
  rw [setLIntegral_congr hae.symm]
  have hInt := shellLogWeight_integrableOn ht ht1 hs hC
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) t)]
      (fun ε => C * (1 + Real.log (1 / ε)) * ε ^ s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with ε hε
    obtain ⟨hε0, hεt⟩ := hε
    have hε1 : ε < 1 := lt_of_lt_of_le hεt ht1
    have hlogpos : 0 ≤ Real.log (1 / ε) := by
      rw [one_div]
      exact Real.log_nonneg (by rw [le_inv_comm₀ (by norm_num) hε0]; simpa using hε1.le)
    have hεs : (0 : ℝ) < ε ^ s := Real.rpow_pos_of_pos hε0 s
    positivity
  have := (lintegral_ofReal_ne_top_iff_integrable hInt.aestronglyMeasurable hnn).mpr hInt
  exact lt_top_iff_ne_top.mpr this

end DLNFibre.DLN.RLCT
