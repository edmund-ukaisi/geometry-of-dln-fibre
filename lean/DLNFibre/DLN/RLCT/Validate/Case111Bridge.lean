import DLNFibre.DLN.RLCT.Skeleton
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# `DLNFibre.DLN.RLCT.Validate.Case111Bridge` — `monomialThreshold (1,1,1) = 1/2`, axiom-free

The probe deliverable: the weighted-monomial threshold for the `(1,1,1)` resolution data
(`k = (1,1)`, `h = (0,0)`, `d = 2`) is `1/2` — proven **directly from Mathlib**, without the
`monomial_rlct` citation. This shows the threshold-half of `monomial_rlct` is **not** an irreducible
external fact for normal-crossing data: it is Fubini (`Integrable.mul_prod` /
`Integrable.prod_right_ae` + the product-measure equivalence `measurePreserving_finTwoArrow`) plus
the single-variable rpow integrability iff (`intervalIntegral.integrableOn_Ioo_rpow_iff`), per axis.

The analytic heart is `intervalIntegral.integrableOn_Ioo_rpow_iff : IntegrableOn (·^s) (Ioo 0 t) ↔
-1 < s` (for `s = -2c`: integrable ⟺ `c < 1/2`), lifted to the 2-D box. The admissible-exponent set
is then `{c' : NNReal | c' < 1/2}`, whose `sSup` in `ℝ≥0∞` is `1/2`.

See `Case111.lean` for the cited (`monomial_rlct`) version `case111_monomialThreshold` and the
`rlctAt`-headline. The general threshold-half (`d` axes, arbitrary `k,h`) follows the same recipe
(`Fin d` pi↔iterated-prod, per-axis ratio binding the min); the obstruction is Lean labour, not
mathematics — see the thread feasibility note.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set Real Filter
open scoped ENNReal

/-! ## The box-integrability iff (the analytic spine) -/

/-- The two-variable monomial `x^{−2c}·y^{−2c}` is integrable on `[0,1]²` (a `prod` measure) **iff**
`c < 1/2`. Forward: `Integrable.mul_prod` from the per-axis integrability. Reverse: a.e.-slice
integrability (`Integrable.prod_right_ae`) at a positive `y`, factoring out the nonzero constant,
reduces to the single-axis iff. The genuine analytic content, all from Mathlib. -/
theorem prodBox_rpow_integrableOn_iff (c : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 ^ (-2 * c) * p.2 ^ (-2 * c))
        (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) (volume.prod volume) ↔ c < 1 / 2 := by
  constructor
  · intro h
    rw [IntegrableOn, ← Measure.prod_restrict] at h
    have hae := h.prod_right_ae
    haveI : (ae (volume.restrict (Icc (0 : ℝ) 1))).NeBot := by
      rw [ae_restrict_neBot]; simp [Real.volume_Icc]
    have haey : ∀ᵐ y ∂(volume.restrict (Icc (0 : ℝ) 1)), 0 < y := by
      rw [ae_iff, Measure.restrict_apply' measurableSet_Icc]
      apply measure_mono_null
        (h := show {y | ¬ 0 < y} ∩ Icc (0 : ℝ) 1 ⊆ {(0 : ℝ)} from ?_)
      · simp
      · intro x hx
        simp only [mem_inter_iff, mem_setOf_eq, not_lt, mem_Icc] at hx
        simp only [mem_singleton_iff]; exact le_antisymm hx.1 hx.2.1
    obtain ⟨y, hyint, hypos⟩ := (hae.and haey).exists
    have hyne : y ^ (-2 * c) ≠ 0 := by positivity
    have key : IntegrableOn (fun x : ℝ => x ^ (-2 * c)) (Icc (0 : ℝ) 1) volume := by
      have hcm := hyint.const_mul (y ^ (-2 * c))⁻¹
      rw [IntegrableOn]
      refine hcm.congr (Filter.Eventually.of_forall (fun x => ?_))
      simp only; field_simp
    rw [integrableOn_Icc_iff_integrableOn_Ioo,
      intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num)] at key
    linarith
  · intro hc
    have hsv : IntegrableOn (fun x : ℝ => x ^ (-2 * c)) (Icc (0 : ℝ) 1) volume := by
      rw [integrableOn_Icc_iff_integrableOn_Ioo,
        intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num)]
      linarith
    rw [IntegrableOn, ← Measure.prod_restrict]
    exact MeasureTheory.Integrable.mul_prod hsv hsv

/-- The `(1,1,1)` weighted-monomial integrand is integrable on the unit box `[0,1]²` **iff**
`c < 1/2`. Lifts `prodBox_rpow_integrableOn_iff` along the measure-preserving equiv
`finTwoArrow : (Fin 2 → ℝ) ≃ ℝ²` (`measurePreserving_finTwoArrow`), with the box `[0,1]²` and the
`|uⱼ|`-monomial collapsing to the rpow product (on the box `|uⱼ| = uⱼ`). -/
theorem unitBox_monomialIntegrand_integrableOn_iff (c : ℝ) :
    IntegrableOn (monomialIntegrand 2 (![1, 1] : Fin 2 → ℕ) (![0, 0] : Fin 2 → ℕ) c)
        (unitBox 2) volume ↔ c < 1 / 2 := by
  have hmp := measurePreserving_finTwoArrow (volume : Measure ℝ)
  have hemb : MeasurableEmbedding (MeasurableEquiv.finTwoArrow (α := ℝ)) :=
    (MeasurableEquiv.finTwoArrow).measurableEmbedding
  rw [← prodBox_rpow_integrableOn_iff c, ← hmp.integrableOn_comp_preimage hemb]
  have hset : MeasurableEquiv.finTwoArrow (α := ℝ) ⁻¹' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
      = unitBox 2 := by
    ext u
    simp only [mem_preimage, MeasurableEquiv.finTwoArrow, mem_prod, unitBox, Set.mem_pi, mem_univ,
      forall_true_left]
    constructor
    · rintro ⟨h0, h1⟩ i; fin_cases i <;> simpa
    · intro h; exact ⟨h 0, h 1⟩
  rw [hset]
  apply integrableOn_congr_fun _
    (MeasurableSet.pi Set.countable_univ (fun i _ => measurableSet_Icc))
  intro u hu
  simp only [unitBox, Set.mem_pi, mem_univ, forall_true_left, mem_Icc] at hu
  have h0 : |u 0| = u 0 := abs_of_nonneg (hu 0).1
  have h1 : |u 1| = u 1 := abs_of_nonneg (hu 1).1
  have hmono : monomialIntegrand 2 (![1, 1] : Fin 2 → ℕ) (![0, 0] : Fin 2 → ℕ) c u
      = |u 0| ^ (-2 * c) * |u 1| ^ (-2 * c) := by
    unfold monomialIntegrand
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show (2 * (1 : ℕ)) = 2 from rfl, pow_zero, pow_zero, one_mul,
      Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_natCast (|u 0|) 2, ← Real.rpow_natCast (|u 1|) 2,
      ← Real.rpow_mul (abs_nonneg _), ← Real.rpow_mul (abs_nonneg _)]
    norm_num
  rw [hmono, h0, h1]
  simp [Function.comp, MeasurableEquiv.finTwoArrow]

/-! ## The threshold value, axiom-free -/

/-- **The probe payoff.** `monomialThreshold 2 (1,1) (0,0) = 1/2`, proven without `monomial_rlct`.
The admissible-exponent set is exactly the coerced `{c' : NNReal | c' < 1/2}` (by
`unitBox_monomialIntegrand_integrableOn_iff`), whose `sSup` in `ℝ≥0∞` is `1/2`. So the
threshold-half of the S2 citation is, for this normal-crossing datum, a Mathlib theorem. -/
theorem monomialThreshold_case111 :
    monomialThreshold 2 (![1, 1] : Fin 2 → ℕ) (![0, 0] : Fin 2 → ℕ) = (1 / 2 : ℝ≥0∞) := by
  unfold monomialThreshold
  have hset : { c : ℝ≥0∞ | ∃ c' : NNReal, c = (c' : ℝ≥0∞) ∧
        IntegrableOn (monomialIntegrand 2 (![1, 1]) (![0, 0]) (c' : ℝ)) (unitBox 2) volume }
      = { c : ℝ≥0∞ | ∃ c' : NNReal, c = (c' : ℝ≥0∞) ∧ (c' : ℝ) < 1 / 2 } := by
    ext c; constructor
    · rintro ⟨c', rfl, hc⟩; exact ⟨c', rfl, (unitBox_monomialIntegrand_integrableOn_iff _).1 hc⟩
    · rintro ⟨c', rfl, hc⟩; exact ⟨c', rfl, (unitBox_monomialIntegrand_integrableOn_iff _).2 hc⟩
  rw [hset]
  apply le_antisymm
  · apply sSup_le; rintro c ⟨c', rfl, hc⟩
    rw [show (1 / 2 : ℝ≥0∞) = ((1 / 2 : NNReal) : ℝ≥0∞) by simp]
    rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe]; push_cast; linarith
  · apply le_of_forall_lt_imp_le_of_dense
    intro q hq
    have hqfin : q ≠ ⊤ := by intro h; rw [h] at hq; simp at hq
    apply le_sSup
    refine ⟨q.toNNReal, (ENNReal.coe_toNNReal hqfin).symm, ?_⟩
    have hqt : q.toReal < (1 / 2 : ℝ) := by
      have := (ENNReal.toReal_lt_toReal hqfin (by simp : (1 / 2 : ℝ≥0∞) ≠ ⊤)).2 hq
      simpa using this
    exact hqt

/-! ## Reusable infra for the `rlctAt`-bridge (baby S1.1; thread 13)

Two self-contained, sorry-free pieces toward `case111_rlct_eq_monomialThreshold` (`rlctAt = θ` for
the `(1,1,1)` monomial). They are **reusable S1.1 infra**, not `(1,1,1)`-throwaway. The third piece
(the measure-preserving `Params (1,1,1) ≃ᵐ (Fin 2 → ℝ)`) is **blocked** by a `Params`-as-`def` type
obstruction documented in thread 13 — so the bridge `sorry` in `Case111.lean` stands. -/

/-- **One-sided `rpow` integrability via `|·|`** (the bridge's piece 2, half): `|x|^s` is integrable
on `Ioo 0 ε` **iff** `-1 < s` (on the positive half `|x| = x`, so this is the single-axis rpow iff).
The two-sided version on `[-ε, ε]` (the `𝓝 0`-shaped chart the `rlctAt` side needs, crossing `0`)
glues this right half with the reflected negative half — a short addendum once a `volume`
neg-invariance lemma is in scope (see thread 13). -/
theorem abs_rpow_integrableOn_Ioo_iff (s ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun x : ℝ => |x| ^ s) (Ioo (0 : ℝ) ε) volume ↔ -1 < s := by
  have hposEq : EqOn (fun x : ℝ => |x| ^ s) (fun x : ℝ => x ^ s) (Ioo (0 : ℝ) ε) :=
    fun x hx => by simp only; rw [abs_of_pos hx.1]
  rw [integrableOn_congr_fun hposEq measurableSet_Ioo,
    intervalIntegral.integrableOn_Ioo_rpow_iff hε]

/-- **Per-layer measure-preserving entry equiv** (toward the bridge's piece 1): the unique scalar
entry of a `1×1` real matrix, `(Fin 1 → Fin 1 → ℝ) ≃ᵐ ℝ`, is volume-preserving (twice-`funUnique`).
The remaining step — assembling these per-layer maps into a measure-preserving
`Params (1,1,1) ≃ᵐ (Fin 2 → ℝ)` — is BLOCKED: `Params H`'s fiber
`Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ` does not reduce to `Fin 1 → Fin 1 → ℝ` *uniformly*
in symbolic `s` (only per concrete `s` via `fin_cases`), and `Matrix`-as-`def` blocks the
`MeasurableSpace`/Pi-fiber instances `volume_preserving_pi` needs. See thread 13. -/
theorem measurePreserving_matrixEntry₁₁ :
    MeasurePreserving
      ((MeasurableEquiv.funUnique (Fin 1) (Fin 1 → ℝ)).trans (MeasurableEquiv.funUnique (Fin 1) ℝ))
      (volume : Measure (Fin 1 → Fin 1 → ℝ)) volume :=
  (volume_preserving_funUnique (Fin 1) ℝ).comp (volume_preserving_funUnique (Fin 1) (Fin 1 → ℝ))

end DLNFibre.DLN.RLCT
