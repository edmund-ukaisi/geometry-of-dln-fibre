import DLNFibre.DLN.RLCT.Validate.RouteMSJRadialPolar
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

set_option linter.style.longLine false

/-!
# `RouteMSJIncidenceChart4Polar` — Brick D piece (ii), chart (4): the `H̃`-fibre polar scaling

**Thread `genm-sj5-brickdcont`.** Chart (4) of the incidence-resolution atlas (`incidence-cert.md` §3b(4)):
the `H̃`-fibre integral over the front block `ℝ^{N}` (`N = u·b`) carries the scale `τ = ‖Y W‖` out as the
monomial `τ^{N − 2q}`:

    ∫_{H̃ ∈ ℝ^N} (‖H̃‖² + τ²)^{−q} dH̃  =  τ^{N − 2q} · ∫_{V ∈ ℝ^N} (‖V‖² + 1)^{−q} dV.

The scale extraction is the load-bearing content (it feeds the outer `τ`-radial exponent bookkeeping,
piece (iv)'s `clsCodim`); the unit integral `K = ∫(‖V‖²+1)^{−q}dV` is finite iff `2q > N`. Proof: the
Haar scaling CoV `map_addHaar_smul` at `r = τ⁻¹` (`H̃ = τ·V`), no polar/sphere needed. Network-free measure
theory; axiom-clean. Chart (4) as an individual CoV is bltj-INDEPENDENT (only the assembly's atlas-coverage
is bltj-gated).
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal

/-- **Chart (4) — the `H̃`-fibre polar scaling (cert §3b(4)).** For `τ > 0` and any real `q`, the front-block
`ℝ^N` integral extracts the scale as `τ^{N−2q}`:
`∫ (‖H̃‖²+τ²)^{−q} dH̃ = τ^{N−2q} · ∫ (‖V‖²+1)^{−q} dV`. Via the Haar scaling `H̃ = τ·V`
(`map_addHaar_smul` at `r = τ⁻¹`), reformulating the integrand as `(‖H‖²+τ²)^{−q} = τ^{−2q}·(‖τ⁻¹•H‖²+1)^{−q}`. -/
theorem chart4_polar_scaling {N : ℕ} {τ : ℝ} (hτ : 0 < τ) (q : ℝ) :
    ∫⁻ H : EuclideanSpace ℝ (Fin N), ENNReal.ofReal ((‖H‖ ^ 2 + τ ^ 2) ^ (-q))
      = ENNReal.ofReal (τ ^ ((N : ℝ) - 2 * q))
          * ∫⁻ V : EuclideanSpace ℝ (Fin N), ENNReal.ofReal ((‖V‖ ^ 2 + 1) ^ (-q)) := by
  set g : EuclideanSpace ℝ (Fin N) → ℝ := fun x => (‖x‖ ^ 2 + 1) ^ (-q) with hg_def
  have hgmeas : Measurable g := by rw [hg_def]; fun_prop
  -- pointwise: (‖H‖²+τ²)^{−q} = τ^{−2q} · g (τ⁻¹ • H)
  have hpt : ∀ H : EuclideanSpace ℝ (Fin N),
      ENNReal.ofReal ((‖H‖ ^ 2 + τ ^ 2) ^ (-q))
        = ENNReal.ofReal (τ ^ (-(2 * q))) * ENNReal.ofReal (g (τ⁻¹ • H)) := by
    intro H
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hnorm : ‖τ⁻¹ • H‖ ^ 2 = τ⁻¹ ^ 2 * ‖H‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]; ring
    have hbase : τ⁻¹ ^ 2 * ‖H‖ ^ 2 + 1 = τ⁻¹ ^ 2 * (‖H‖ ^ 2 + τ ^ 2) := by field_simp
    have hsplit : (τ⁻¹ ^ 2 * (‖H‖ ^ 2 + τ ^ 2)) ^ (-q)
        = (τ⁻¹ ^ 2) ^ (-q) * (‖H‖ ^ 2 + τ ^ 2) ^ (-q) :=
      Real.mul_rpow (by positivity) (by positivity)
    have hpow2 : ((τ ^ 2 : ℝ)) ^ q = τ ^ (2 * q) := by
      rw [← Real.rpow_natCast τ 2, ← Real.rpow_mul hτ.le]; norm_num
    have h1 : (τ⁻¹ ^ 2 : ℝ) ^ (-q) = (τ ^ 2 : ℝ) ^ q := by
      rw [inv_pow, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv]
    have h2 : τ ^ (-(2 * q)) = ((τ ^ 2 : ℝ) ^ q)⁻¹ := by
      rw [Real.rpow_neg hτ.le, hpow2]
    have hconst : τ ^ (-(2 * q)) * (τ⁻¹ ^ 2) ^ (-q) = 1 := by
      rw [h1, h2, inv_mul_cancel₀ (by positivity)]
    rw [hg_def]; simp only [hnorm, hbase, hsplit]
    rw [← mul_assoc, hconst, one_mul]
  -- the scaling CoV: ∫ g(τ⁻¹ • x) = τ^N · ∫ g
  have hscale : ∫⁻ H : EuclideanSpace ℝ (Fin N), ENNReal.ofReal (g (τ⁻¹ • H))
      = ENNReal.ofReal (τ ^ (N : ℝ)) * ∫⁻ V : EuclideanSpace ℝ (Fin N), ENNReal.ofReal (g V) := by
    have hsmul : Measurable (fun x : EuclideanSpace ℝ (Fin N) => τ⁻¹ • x) := by fun_prop
    have hmap := Measure.map_addHaar_smul (volume : Measure (EuclideanSpace ℝ (Fin N)))
      (show (τ⁻¹ : ℝ) ≠ 0 by positivity)
    rw [← lintegral_map hgmeas.ennreal_ofReal hsmul, hmap, lintegral_smul_measure]
    congr 1
    rw [finrank_euclideanSpace_fin,
      show |((τ⁻¹ ^ N : ℝ))⁻¹| = τ ^ (N : ℝ) by
        rw [inv_pow, inv_inv, abs_of_pos (by positivity), Real.rpow_natCast]]
  calc ∫⁻ H : EuclideanSpace ℝ (Fin N), ENNReal.ofReal ((‖H‖ ^ 2 + τ ^ 2) ^ (-q))
      = ∫⁻ H : EuclideanSpace ℝ (Fin N),
          ENNReal.ofReal (τ ^ (-(2 * q))) * ENNReal.ofReal (g (τ⁻¹ • H)) := by simp_rw [hpt]
    _ = ENNReal.ofReal (τ ^ (-(2 * q)))
          * ∫⁻ H : EuclideanSpace ℝ (Fin N), ENNReal.ofReal (g (τ⁻¹ • H)) :=
        lintegral_const_mul _ ((hgmeas.comp (by fun_prop)).ennreal_ofReal)
    _ = ENNReal.ofReal (τ ^ (-(2 * q)))
          * (ENNReal.ofReal (τ ^ (N : ℝ)) * ∫⁻ V, ENNReal.ofReal (g V)) := by rw [hscale]
    _ = ENNReal.ofReal (τ ^ ((N : ℝ) - 2 * q)) * ∫⁻ V, ENNReal.ofReal (g V) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hτ,
          show -(2 * q) + (N : ℝ) = (N : ℝ) - 2 * q from by ring]

/-- **Chart (4) unit-integral finiteness (sufficiency).** The unit integral `K = ∫(‖V‖²+1)^{−q} dV` over
`ℝ^N` is finite when `2q > N`. Direct reuse of Mathlib's `integrable_rpow_neg_one_add_norm_sq`
(`finrank < r ⟹ (1+‖x‖²)^{−r/2}` integrable, at `r = 2q`). `N/2` is the exact fibre threshold; the necessity
`K < ⊤ ⟹ 2q > N` is not formalised here (so this is a `_lt_top` sufficiency, not an `iff`). -/
theorem chart4_unit_lintegral_lt_top {N : ℕ} {q : ℝ} (hq : (N : ℝ) < 2 * q) :
    ∫⁻ V : EuclideanSpace ℝ (Fin N), ENNReal.ofReal ((‖V‖ ^ 2 + 1) ^ (-q)) < ⊤ := by
  have hint : Integrable
      (fun V : EuclideanSpace ℝ (Fin N) => ((1 : ℝ) + ‖V‖ ^ 2) ^ (-(2 * q) / 2)) volume :=
    integrable_rpow_neg_one_add_norm_sq (by rw [finrank_euclideanSpace_fin]; exact hq)
  have heq : (fun V : EuclideanSpace ℝ (Fin N) => ((1 : ℝ) + ‖V‖ ^ 2) ^ (-(2 * q) / 2))
      = (fun V => (‖V‖ ^ 2 + 1) ^ (-q)) := by
    funext V; rw [add_comm]; congr 1; ring
  rw [heq] at hint
  have hfin := hint.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm,
    lintegral_enorm_of_nonneg (fun V => Real.rpow_nonneg (by positivity) _)] at hfin
  exact hfin

/-- **Chart (4) — the `H̃`-fibre is finite (assembly-ready).** For `τ > 0` and `2q > N`, the front-block
integral is finite: `∫(‖H̃‖²+τ²)^{−q} dH̃ = τ^{N−2q}·K < ⊤`. Combines `chart4_polar_scaling` (the scale)
with `chart4_unit_lintegral_lt_top` (`K < ⊤`). -/
theorem chart4_Htilde_fibre_lt_top {N : ℕ} {τ : ℝ} (hτ : 0 < τ) {q : ℝ} (hq : (N : ℝ) < 2 * q) :
    ∫⁻ H : EuclideanSpace ℝ (Fin N), ENNReal.ofReal ((‖H‖ ^ 2 + τ ^ 2) ^ (-q)) < ⊤ := by
  rw [chart4_polar_scaling hτ q]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (chart4_unit_lintegral_lt_top hq)

end DLNFibre.DLN.RLCT
