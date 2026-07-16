import DLNFibre.DLN.RLCT.Validate.RouteMSchurWishartWeight
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

set_option linter.style.longLine false

/-!
# `RouteMSJInteriorShell` — the interior charge free-box (route C) + the log-integrability atom

**Thread (aoyagi-full Stage 2), the interior coupled shell-integration.** The interior gate is the CHARGE
free-box `∫∫_{(A_cor,S)∈box} det((A_cor·S)(A_cor·S)ᵀ)^{−a/2}` (arch1build's definitional read: the loss
factor is `x`-independent and BOUNDED on the interior generic cell — `E_top`'s `P·P⁻¹` cancels, `E_tr`'s
`Q_inr` is killed by its own projector — so it pulls out and the gate reduces to the charge). For the 3
square dispatch witnesses (`b=1, a=1`, `S` square `n×p`, `ρ = min(n,p)`), the free-box is **POWER-convergent**
by integrating `S` FIRST: `∫_S ‖A_cor·S‖⁻¹ dS ≤ C·‖A_cor‖⁻¹` uniformly, then `∫_{A_cor} ‖A_cor‖⁻¹ dA_cor <
⊤` (`a=1 < n`). There is NO log on the interior — the log was an `A_cor`-first-order artifact (the fixed-`S`
charge weight `W(S) ~ log(1/σ_min(S))`), which the `S`-first order avoids; the genuine log lives at the
EDGE `a+b = ρ+1` (edgeasm).

## Contents
Route C (the interior closure, `b=1,a=1`), power-convergent, `S`-first:
- `chargeFreeBox_b1a1_of_inner` — the assembly: given schurB's inner uniform charge bound `∫_S charge^{−1/2}
  dS ≤ C·frobSq(A_cor)^{−1/2}` (via the banked qbox projection-radial core `projection_rpow_lintegral_
  uniform`), the outer `A_cor`-integral closes by the banked `detGram_lintegral_lt_top` (`r=1`, `a=1<n`).
  Discharges to `chargeFreeBox_b1a1_lt_top` once schurB lands the inner contract. Needs `n≥2 ∧ p≥2`.

The log-integrability atom (re-homed: NOT the interior tool — it is the EDGE tool for `a+b=ρ+1`, and the
last-step tool for the `A_cor`-first lens of the coupled/edge integrals; reusable clean bedrock):
- `log_one_div_le_rpow_neg` — log-vs-power domination `log(1/x) ≤ η⁻¹·x^{−η}` (network-free, `x, η > 0`).
- `shellLogWeight_integrableOn` — the weight `C·(1+log(1/ε))·ε^s` is integrable on `(0,t)` (`0<t≤1`,
  `−1<s`, `0≤C`); the analytic convergence core (Bochner form), via the `σ^{−κ}` domination.
- `shellLogWeight_lintegral_lt_top` — the `ℝ≥0∞` form: `∫⁻ ε in Ioc 0 t, ofReal(C·(1+log(1/ε))·ε^s) < ⊤`.
-/

open MeasureTheory Set Matrix
open scoped ENNReal Matrix

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

/-! ## The interior charge free-box (route C, `b=1,a=1` square witnesses)

The interior closure is the CHARGE free-box `∫∫_{(A_cor,S)∈box} det((A_cor·S)(A_cor·S)ᵀ)^{−a/2}` (arch1build:
the loss factor is x-independent and BOUNDED on the interior generic cell — `E_top`'s `P·P⁻¹` cancels,
`E_tr`'s `Q_inr` is killed by its own projector — so it pulls out, leaving the charge). For the 3 square
dispatch witnesses `b=1, a=1` (`S = Z_deep` square `n×p`, `ρ = min(n,p)`), `chargeGramDet A_cor S =
frobSq(A_cor·S) = ‖A_cor·S‖²`, and the free-box is POWER-convergent by integrating `S` FIRST:
`∫_S ‖A_cor·S‖⁻¹ dS ≤ C·‖A_cor‖⁻¹` uniformly (schurB's inner contract, via the banked qbox projection-
radial core `projection_rpow_lintegral_uniform`), then `∫_{A_cor} ‖A_cor‖⁻¹ dA_cor < ⊤` (banked
`detGram_lintegral_lt_top` at `r=1`). No log, no shell, no CoV — the log was an `A_cor`-first artifact,
`S`-first is pure power. Needs `n≥2 ∧ p≥2` (`= a+b ≤ ρ`). -/

/-- **The interior charge free-box is finite, given the inner uniform bound (`b=1`, general `a < n`).** The
assembly of route C: consume the inner uniform charge bound `hinner` (`∫_S charge^{−a/2} dS ≤
C·frobSq(A_cor)^{−a/2}`, uniform `C`, via the banked projection-radial core — schurB's contract) and close
the outer `A_cor`-integral by the banked `detGram_lintegral_lt_top` (`r=1`, exponent `−a/2` at `a < n`).
The proof carries `a` freely (only `a < n` matters for the outer); the `a=1` square witnesses are the
corollary `chargeFreeBox_b1a1_of_inner` below. -/
theorem chargeFreeBox_b1_of_inner {n p a : ℕ} (hn : a < n) (C : ℝ≥0∞) (hC : C < ⊤)
    (hinner : ∀ Acor : Fin 1 → Fin n → ℝ,
      (∫⁻ S in matBox n p 1, ENNReal.ofReal ((chargeGramDet Acor S) ^ (-(a : ℝ) / 2)))
        ≤ C * ENNReal.ofReal ((frobSq Acor) ^ (-(a : ℝ) / 2))) :
    (∫⁻ Acor in matBox 1 n 1, ∫⁻ S in matBox n p 1,
        ENNReal.ofReal ((chargeGramDet Acor S) ^ (-(a : ℝ) / 2))) < ⊤ := by
  classical
  -- the `1×n` Gram determinant is `frobSq` (inline `det_gramRow`)
  have hgram : ∀ v : Fin 1 → Fin n → ℝ,
      ((Matrix.of v) * (Matrix.of v)ᵀ).det = frobSq v := by
    intro v
    rw [Matrix.det_fin_one]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    rw [frobSq, Fin.sum_univ_one]
    exact Finset.sum_congr rfl (fun j _ => by rw [sq])
  calc (∫⁻ Acor in matBox 1 n 1, ∫⁻ S in matBox n p 1,
          ENNReal.ofReal ((chargeGramDet Acor S) ^ (-(a : ℝ) / 2)))
      ≤ ∫⁻ Acor in matBox 1 n 1, C * ENNReal.ofReal ((frobSq Acor) ^ (-(a : ℝ) / 2)) :=
        lintegral_mono hinner
    _ = C * ∫⁻ Acor in matBox 1 n 1, ENNReal.ofReal ((frobSq Acor) ^ (-(a : ℝ) / 2)) :=
        lintegral_const_mul' _ _ hC.ne
    _ = C * ∫⁻ Acor in matBox 1 n 1,
          ENNReal.ofReal (((Matrix.of Acor) * (Matrix.of Acor)ᵀ).det ^ (-(a : ℝ) / 2)) := by
        congr 1
        refine setLIntegral_congr_fun (matBox_measurableSet 1 n 1) (fun Acor _ => ?_)
        rw [hgram]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top hC ?_
        have hna : (a : ℝ) < (n : ℝ) := by exact_mod_cast hn
        have h := detGram_lintegral_lt_top (r := 1) (n := n) (by omega) (a := (a : ℝ))
          (by push_cast; linarith)
        exact h

/-- **The `a=1` square-witness corollary** (matching schurB's `corankSlab_charge_sint_le` contract exactly):
the interior charge free-box `∫∫_{(A_cor,S)∈box} det((A_cor·S)(A_cor·S)ᵀ)^{−1/2}` is finite given the
`a=1` inner uniform bound, for `n ≥ 2`. Discharges to `chargeFreeBox_b1a1_lt_top` on wiring schurB's inner. -/
theorem chargeFreeBox_b1a1_of_inner {n p : ℕ} (hn : 2 ≤ n) (C : ℝ≥0∞) (hC : C < ⊤)
    (hinner : ∀ Acor : Fin 1 → Fin n → ℝ,
      (∫⁻ S in matBox n p 1, ENNReal.ofReal ((chargeGramDet Acor S) ^ (-(1 : ℝ) / 2)))
        ≤ C * ENNReal.ofReal ((frobSq Acor) ^ (-(1 : ℝ) / 2))) :
    (∫⁻ Acor in matBox 1 n 1, ∫⁻ S in matBox n p 1,
        ENNReal.ofReal ((chargeGramDet Acor S) ^ (-(1 : ℝ) / 2))) < ⊤ := by
  have h := chargeFreeBox_b1_of_inner (n := n) (p := p) (a := 1) (by omega) C hC
    (by simpa using hinner)
  simpa using h

end DLNFibre.DLN.RLCT
