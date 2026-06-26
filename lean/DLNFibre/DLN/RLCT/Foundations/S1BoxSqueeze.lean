import DLNFibre.DLN.RLCT.Foundations.Rlct
import DLNFibre.DLN.RLCT.Foundations.S1WeightedProductMin

/-!
# `DLNFibre.DLN.RLCT.Foundations.S1BoxSqueeze` — box-level squeeze integrability transfer (R1 lift, piece 1)

The foundational piece of the GE-leg squeeze+reindex lift (glue (a), g156-adjudicated): a two-sided
squeeze `c₁·Φ ≤ F ≤ c₂·Φ` (`Φ, F ≥ 0`, `c₁ > 0`) over a set `V` transfers box-integrability of the
threshold density `|·|^{−c'}` between `F` and `Φ`. The box-level (not germ) analog of
`rlctAtOn_squeeze`: where `rlctAtOn_squeeze` (GeneralR1Recursion) lifts the squeeze to the point RLCT,
this lifts it to a FIXED set `V` (the chart's full ratio box) — which the per-node cover needs
(`chart_pullback`'s `hKint` is over a fixed box, not a germ).

Used in the lift: the post-blow-up core is squeezed `c₁·Φ ≤ core ≤ c₂·Φ` over the ratio box with
`Φ = ∑Erow² + ‖S·Bred‖²` (the box-uniform `schur_node_squeeze`, `T = ‖v‖` bounded on the box; constants
`c₁ = (2(1+T²))⁻¹ > 0`, `c₂ = 2+2T²`). This lemma transfers `IntegrableOn (|Φ|^{−c'}) V ⟹ IntegrableOn
(|core|^{−c'}) V`, reducing the core's box-integrability to `Φ`'s (= Erow smooth block + child).

Axiom-free target (only `propext`/`Classical.choice`/`Quot.sound`).
-/

open MeasureTheory Set
open scoped ENNReal
namespace DLNFibre.DLN.RLCT

variable {E : Type*} [MeasureSpace E] [TopologicalSpace E] [OpensMeasurableSpace E]

/-- **Box-level squeeze integrability transfer.** On a measurable set `V`, if `0 ≤ Φ`, `c₁·Φ ≤ F ≤
c₂·Φ` (`c₁ > 0`), and `F` is measurable, then `|Φ|^{−c'}` integrable on `V` (`c' ≥ 0`) gives `|F|^{−c'}`
integrable on `V`. The integrand domination `|F|^{−c'} ≤ |c₁·Φ|^{−c'}` (smaller base ⟹ larger negative
power; `abs_rpow_neg_mono` with `F = 0 → Φ = 0` from `c₁·Φ ≤ F` and `F ≤ c₂·Φ`), and the `c₁`-unit is
stripped (`|c₁·Φ|^{−c'} = c₁^{−c'}·|Φ|^{−c'}`). The box analog of `rlctAtOn_squeeze`'s mono leg. -/
theorem box_integrableOn_of_squeeze (F Φ : E → ℝ) (V : Set E) (hVmeas : MeasurableSet V)
    (hFmeas : Measurable F) (hΦmeas : Measurable Φ) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁)
    (hsq : ∀ w ∈ V, 0 ≤ Φ w ∧ c₁ * Φ w ≤ F w ∧ F w ≤ c₂ * Φ w)
    (c' : ℝ) (hc' : 0 ≤ c') (hΦint : IntegrableOn (fun w => |Φ w| ^ (-c')) V volume) :
    IntegrableOn (fun w => |F w| ^ (-c')) V volume := by
  -- dominate `|F|^{−c'} ≤ c₁^{−c'}·|Φ|^{−c'}` on `V`, then `Integrable.mono`.
  have hFnn : ∀ w, 0 ≤ |F w| ^ (-c') := fun w => Real.rpow_nonneg (abs_nonneg _) _
  -- the dominating function `c₁^{−c'}·|Φ|^{−c'}` is integrable on `V`
  have hdom_int : IntegrableOn (fun w => (c₁ ^ (-c')) * |Φ w| ^ (-c')) V volume :=
    hΦint.const_mul _
  refine Integrable.mono hdom_int
    (((continuous_abs.measurable.comp hFmeas).pow_const _).aestronglyMeasurable) ?_
  -- pointwise: `‖|F|^{−c'}‖ ≤ ‖c₁^{−c'}·|Φ|^{−c'}‖` a.e. on `V`
  refine (ae_restrict_iff' hVmeas).mpr (ae_of_all _ (fun w hw => ?_))
  obtain ⟨hΦw, hlo, hhi⟩ := hsq w hw
  have hF0 : 0 ≤ F w := le_trans (mul_nonneg hc₁.le hΦw) hlo
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (hFnn w),
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hc₁.le _) (Real.rpow_nonneg (abs_nonneg _) _))]
  -- `|F|^{−c'} ≤ |c₁·Φ|^{−c'} = c₁^{−c'}·|Φ|^{−c'}` (domination + unit strip)
  have hmono : |F w| ^ (-c') ≤ |c₁ * Φ w| ^ (-c') := by
    apply abs_rpow_neg_mono (F w) (c₁ * Φ w) c' hc'
    · rw [abs_of_nonneg hF0, abs_of_nonneg (mul_nonneg hc₁.le hΦw)]; exact hlo
    · intro hcΦ0
      have hΦ0 : Φ w = 0 := by
        rcases mul_eq_zero.1 hcΦ0 with h | h
        · exact absurd h (ne_of_gt hc₁)
        · exact h
      have : F w = 0 := le_antisymm (by rw [hΦ0, mul_zero] at hhi; exact hhi) hF0
      exact this
  calc |F w| ^ (-c') ≤ |c₁ * Φ w| ^ (-c') := hmono
    _ = c₁ ^ (-c') * |Φ w| ^ (-c') := by
        rw [abs_mul, abs_of_pos hc₁, Real.mul_rpow hc₁.le (abs_nonneg _)]

end DLNFibre.DLN.RLCT
