import DLNFibre.DLN.RLCT.Validate.Case222Cover

/-!
# `RouteMSmearedAxisPeel` — the M-agnostic weighted divergence from a quadratic rate (contract field B)

The reusable core of the boundary-SMEARED contract's `hSdiv` (the weighted source-divergence), abstracted
over an axis box + a quadratic rate (Codex `headline-path-answer` §3): the `z`-axis carries the
divergence, the rest factor is a positive constant-in-`z` integral.

On a product source `Ioo 0 δ ×ˢ T` (the binding axis `z ∈ (0,δ)`, the rest in a positive-measure box `T`),
with the rate `F = z²·U` (`U` measurable, `0 < U` on the rest box, `z`-independent — the `Λ₀` having
cancelled), the weighted integrand `|z|^h · |F|^{−c'}` rewrites to `|z|^{h−2c'} · U^{−c'}`. Tonelli peels
`z`: the `z`-factor `∫_{(0,δ)} |z|^{h−2c'} = ⊤` (the banked 1-D atom `abs_rpow_lintegral_Ioo_eq_top`, valid
for `h − 2c' ≤ −1`, i.e. `c' ≥ ½(h+1)` — at `h = minAdm−1` this is `c' ≥ ½·minAdm`), the rest-factor
`∫_T U^{−c'} > 0` (positive `U` on a positive-measure box). `⊤ · (positive) = ⊤`.

This is the M-agnostic, opaque-width-free divergence engine the L=2 (and ∀M) smeared headline consumes,
with the source box, the rate, and the `U`-positivity supplied per family. Reuses the banked 1-D `rpow`
atom (axiom-clean — the `Skeleton` sorries in its import chain are in other declarations, not this atom).
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

/-- **The weighted divergence from a quadratic rate (axis-box form).** On `Ioo 0 δ ×ˢ T` with the rate
`F (z,y) = z²·Uy y`, `Uy` measurable + positive on `T`, and `h − 2c' ≤ −1`, the weighted integral
`∫ |z|^h · |F|^{−c'} = ⊤`. The `z`-axis peel (Tonelli) + the 1-D `rpow` atom + the positive rest factor.
The rate is `z`-independent in `U` (the `Λ₀` cancels), so the rest factor pulls out of the `z`-integral. -/
theorem axisPeel_diverges_of_quadratic_rate
    {E : Type*} [MeasurableSpace E] {volE : Measure E} [SFinite volE]
    (δ h c' : ℝ) (T : Set E)
    (F : ℝ × E → ℝ) (Uy : E → ℝ)
    (hδ : 0 < δ)
    (hTmeas : MeasurableSet T) (hTpos : 0 < volE T)
    (hUmeas : Measurable Uy)
    (hexp : h - 2 * c' ≤ -1)
    (hRate : ∀ z ∈ Set.Ioo (0:ℝ) δ, ∀ y ∈ T, F (z, y) = z ^ 2 * Uy y)
    (hUpos : ∀ y ∈ T, 0 < Uy y) :
    ∫⁻ u in (Set.Ioo (0:ℝ) δ) ×ˢ T,
        ENNReal.ofReal (|u.1| ^ h * |F u| ^ (-c')) ∂(volume.prod volE) = ⊤ := by
  -- the rest factor `g y := U(y)^{−c'}`, measurable and positive on `T`
  set g : E → ℝ≥0∞ := fun y => ENNReal.ofReal (Uy y ^ (-c')) with hg
  have hgmeas : Measurable g := by rw [hg]; fun_prop
  -- the integrand on the box equals `ofReal(|z|^{h−2c'}) * g y`
  have hbox : Set.EqOn (fun u : ℝ × E => ENNReal.ofReal (|u.1| ^ h * |F u| ^ (-c')))
      (fun u : ℝ × E => ENNReal.ofReal (|u.1| ^ (h - 2 * c')) * g u.2)
      ((Set.Ioo (0:ℝ) δ) ×ˢ T) := by
    rintro ⟨z, y⟩ ⟨hz, hy⟩
    have hzabs : (0:ℝ) < |z| := abs_pos.mpr (ne_of_gt hz.1)
    have hUp : (0:ℝ) < Uy y := hUpos y hy
    simp only
    rw [hRate z hz y hy]
    have habs : |z ^ 2 * Uy y| = |z| ^ 2 * Uy y := by
      rw [abs_mul, abs_of_nonneg (le_of_lt hUp), abs_pow]
    rw [habs, Real.mul_rpow (by positivity) (le_of_lt hUp),
      ← Real.rpow_natCast |z| 2, ← Real.rpow_mul (abs_nonneg _), hg,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg z) _)]
    congr 1
    -- `|z|^h * (|z|^{−(2c')} * Uy^{−c'}) = |z|^{h−2c'} * Uy^{−c'}`
    rw [show ((2:ℕ):ℝ) * -c' = -(2 * c') by push_cast; ring,
      ← mul_assoc, ← Real.rpow_add hzabs, show h + -(2 * c') = h - 2 * c' by ring]
  rw [setLIntegral_congr_fun (measurableSet_Ioo.prod hTmeas) hbox]
  -- Tonelli: peel the `z`-axis
  rw [setLIntegral_prod _ (by
    refine Measurable.aemeasurable ?_
    have h1 : Measurable (fun u : ℝ × E => ENNReal.ofReal (|u.1| ^ (h - 2 * c'))) := by fun_prop
    exact h1.mul (hgmeas.comp measurable_snd))]
  -- inner integral: pull the `z`-factor constant out of the `T`-integral
  have hinner : ∀ z, (∫⁻ y in T, ENNReal.ofReal (|z| ^ (h - 2 * c')) * g y ∂volE)
      = ENNReal.ofReal (|z| ^ (h - 2 * c')) * ∫⁻ y in T, g y ∂volE :=
    fun z => lintegral_const_mul _ hgmeas
  simp only [hinner]
  -- outer integral: pull the rest-factor constant out of the `z`-integral
  rw [lintegral_mul_const _ (by fun_prop : Measurable (fun z : ℝ => ENNReal.ofReal (|z| ^ (h - 2 * c'))))]
  -- `z`-factor `= ⊤` (the 1-D atom), rest factor `> 0`
  rw [abs_rpow_lintegral_Ioo_eq_top _ δ hδ hexp]
  refine ENNReal.top_mul (ne_of_gt ?_)
  -- `∫_T U^{−c'} > 0`: positive on the positive-measure box `T`
  rw [setLIntegral_pos_iff hgmeas]
  refine lt_of_lt_of_le hTpos (measure_mono ?_)
  intro y hy
  refine ⟨?_, hy⟩
  rw [Function.mem_support, hg, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact Real.rpow_pos_of_pos (hUpos y hy) _

end DLNFibre.DLN.RLCT
