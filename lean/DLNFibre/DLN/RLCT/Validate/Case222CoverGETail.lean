import DLNFibre.DLN.RLCT.Validate.Case222CoverGE
import DLNFibre.DLN.RLCT.Foundations.S1Fubini

/-!
# `DLNFibre.DLN.RLCT.Validate.Case222CoverGETail` — the `p = 0` A-pivot summand finiteness

The `≥`-direction keystone `aPivotSummand_lt_top` needs each of the four step-1 A-pivot summands of
`∫⁻_{openBox} |myF222|^{−c'}` finite (for `c' < 3/2`). This file discharges the `p = 0` summand,
reducing it to a single inner lemma `resolved_residual_lt_top` (the resolved-form finiteness).

## The reduction (cube domination + Tonelli pivot-peel + Lemma-2 transport)

`p = 0` summand `= ∫⁻_{chartDom \ {x₀=0}} |det φ₁| · (openBox.indicator |myF222|^{−c'})∘φ₁`.

1. **Cube domination** (`p0_summand_le_cube`, gated): `≤ ∫⁻_{cube8 = [−1,1]^8} p0integrand`.
2. **Drop the `openBox` cutoff** (it only shrinks): `≤ ∫⁻_{cube8} ofReal(|x₀|³ · |myF222(step1A x)|^{−c'})`.
3. **Factor** (`p0_integrand_factor`, a.e. off the null `{x₀=0}`, `myF222_step1A'` + `rpow` algebra):
   the integrand is the product `ofReal(|x₀|^{3−2c'}) · ofReal(|step1Residual(tail x)|^{−c'})`.
4. **Tonelli pivot-peel** (`cube8_tonelli_peel`, the measure-preserving `finPeel 7` split into
   `ℝ × (Fin 7 → ℝ)`): the cube integral is `(∫_{[−1,1]} |x₀|^{3−2c'}) · (∫_{box7} |step1Residual|^{−c'})`.
   The pivot factor is finite (`x0_lintegral_lt_top`, `3−2c' > −1 ⟺ c' < 2`, and `c' < 3/2 < 2`).
5. **Lemma-2 transport** (`tail_residual_lt_top`): `step1Residual = resolvedForm ∘ lemma2Fwd`, and
   `lemma2Fwd` is measure-preserving (`measurePreserving_lemma2`), so the tail integral transports to
   `∫⁻_{lemma2Fwd '' box7} |resolvedForm|^{−c'}`, dominated by `∫⁻_{bigbox7 = [−2,2]^7} |resolvedForm|^{−c'}`
   (`lemma2Fwd_box7_subset`).

So the `p = 0` summand finiteness reduces to `resolved_residual_lt_top` (the resolved-form finiteness
over the bounded box, the inner step-2/step-3 recursion — the one remaining `sorry`). The other three
A-pivots are structurally identical by the A-block coordinate symmetry of `myF222`.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators
namespace DLNFibre.DLN.RLCT

/-- The symmetric box `[−1,1]^7` — the bounded tail domain after the `finPeel 7` pivot-peel. -/
noncomputable def box7 : Set (Fin 7 → ℝ) := Set.univ.pi (fun _ => Set.Icc (-1 : ℝ) 1)

theorem cube8_eq_finPeel_preimage :
    cube8 = (finPeel 7) ⁻¹' (Set.Icc (-1 : ℝ) 1 ×ˢ box7) := by
  ext x
  simp only [cube8, box7, finPeel7_apply, Set.mem_preimage, Set.mem_prod, Set.mem_pi,
    Set.mem_univ, true_implies, Set.mem_Icc]
  constructor
  · intro h; exact ⟨h 0, fun i => by have := h i.succ; simpa [Fin.tail] using this⟩
  · rintro ⟨h0, htail⟩ i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · exact h0
    · have := htail j; simpa [Fin.tail] using this

/-- **Tonelli pivot-peel on `cube8`.** A product integrand `f(x₀)·g(tail x)` over the cube splits as
`(∫_{[−1,1]} f) · (∫_{box7} g)` — `cube8 = (finPeel 7)⁻¹' ([−1,1] ×ˢ box7)` (`cube8_eq_finPeel_preimage`),
the measure-preserving `finPeel 7` transports the cube integral to the product measure, then
`lintegral_prod_mul`. The pivot `x₀` separates from the resolved tail. -/
theorem cube8_tonelli_peel (f : ℝ → ℝ≥0∞) (g : (Fin 7 → ℝ) → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ x in cube8, f (x 0) * g (Fin.tail x)
      = (∫⁻ x0 in Set.Icc (-1:ℝ) 1, f x0) * (∫⁻ v in box7, g v) := by
  have hmp : MeasurePreserving (finPeel 7) := finPeel_mp 7
  have hemb : MeasurableEmbedding (finPeel 7) := (finPeel 7).measurableEmbedding
  have hstep : ∫⁻ x in cube8, f (x 0) * g (Fin.tail x)
      = ∫⁻ p in (Set.Icc (-1:ℝ) 1 ×ˢ box7), f p.1 * g p.2 := by
    rw [show (fun x : Fin 8 → ℝ => f (x 0) * g (Fin.tail x))
          = (fun p : ℝ × (Fin 7 → ℝ) => f p.1 * g p.2) ∘ (finPeel 7) from by
        funext x; simp only [Function.comp_apply, finPeel7_apply],
      cube8_eq_finPeel_preimage]
    exact hmp.setLIntegral_comp_preimage_emb hemb (fun p : ℝ × (Fin 7 → ℝ) => f p.1 * g p.2)
      (Set.Icc (-1:ℝ) 1 ×ˢ box7)
  rw [hstep, show (volume : Measure (ℝ × (Fin 7 → ℝ))) = (volume : Measure ℝ).prod volume from
        Measure.volume_eq_prod _ _, ← Measure.prod_restrict, lintegral_prod_mul hf.aemeasurable
        hg.aemeasurable]

/-- **The pivot factor is finite.** `∫⁻_{[−1,1]} |x₀|^{3−2c'} < ⊤` for `c' < 2`: integrable iff
`3−2c' > −1 ⟺ c' < 2` (`abs_rpow_integrableOn_Icc_symm_iff`), then `< ⊤` via the nonneg
`hasFiniteIntegral_iff_ofReal` bridge. The `x₀`-monomial after the step-1 blow-up (`|det| = |x₀|³`
against the loss base `|x₀|^{2c'}`). -/
theorem x0_lintegral_lt_top (c' : NNReal) (hc' : (c':ℝ) < 2) :
    ∫⁻ x0 in Set.Icc (-1:ℝ) 1, ENNReal.ofReal (|x0| ^ (3 - 2*(c':ℝ))) < ⊤ := by
  have hint : IntegrableOn (fun x0 : ℝ => |x0| ^ (3 - 2*(c':ℝ))) (Set.Icc (-1:ℝ) 1) volume := by
    rw [abs_rpow_integrableOn_Icc_symm_iff (3 - 2*(c':ℝ)) 1 (by norm_num)]; linarith
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc (-1:ℝ) 1)] (fun x0 : ℝ => |x0| ^ (3 - 2*(c':ℝ))) :=
    ae_of_all _ (fun x => Real.rpow_nonneg (abs_nonneg _) _)
  have hmeas : AEStronglyMeasurable (fun x0 : ℝ => |x0| ^ (3 - 2*(c':ℝ)))
      (volume.restrict (Set.Icc (-1:ℝ) 1)) :=
    (by fun_prop : Measurable (fun x0 : ℝ => |x0| ^ (3 - 2*(c':ℝ)))).aestronglyMeasurable
  rw [IntegrableOn, Integrable, hasFiniteIntegral_iff_ofReal hnn] at hint
  convert hint.2 using 1


/-- **`p = 0` integrand factorization** (off the null `{x₀ = 0}`, where `rpow_add` needs base `≠ 0`).
`ofReal(|x₀|³ · |myF222(step1A x)|^{−c'}) = ofReal(|x₀|^{3−2c'}) · ofReal(|step1Residual(tail x)|^{−c'})`
via `myF222_step1A'` (`myF222(step1A x) = x₀²·step1Residual(tail x)`) + `rpow` algebra. The product
form `cube8_tonelli_peel` consumes. -/
theorem p0_integrand_factor (c' : NNReal) (x : Fin 8 → ℝ) (hx0 : x 0 ≠ 0) :
    ENNReal.ofReal (|x 0| ^ 3 * |myF222 (step1A x)| ^ (-(c':ℝ)))
      = ENNReal.ofReal (|x 0| ^ (3 - 2*(c':ℝ)))
          * ENNReal.ofReal (|step1Residual (Fin.tail x)| ^ (-(c':ℝ))) := by
  have hx0a : (0:ℝ) < |x 0| := abs_pos.2 hx0
  rw [myF222_step1A', abs_mul, abs_pow, Real.mul_rpow (by positivity) (abs_nonneg _),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [show (|x 0| ^ 3 : ℝ) = |x 0| ^ (3:ℝ) from by rw [← Real.rpow_natCast (|x 0|) 3]; norm_num,
    show (|x 0| ^ 2 : ℝ) = |x 0| ^ (2:ℝ) from by rw [← Real.rpow_natCast (|x 0|) 2]; norm_num,
    ← Real.rpow_mul (abs_nonneg _), ← mul_assoc,
    ← Real.rpow_add hx0a]
  ring_nf

/-- The enlarged box `[−2,2]^7` containing `lemma2Fwd '' box7` (each `lemma2Fwd` entry is bounded by
`2` on `[−1,1]^7`); the bounded resolved-coordinate domain for the inner recursion. -/
noncomputable def bigbox7 : Set (Fin 7 → ℝ) := Set.univ.pi (fun _ => Set.Icc (-2 : ℝ) 2)

/-- `lemma2Fwd` maps `box7` into `bigbox7` (each output entry `|·| ≤ 2` on `[−1,1]^7`: the entries are
single coords or coord-plus-product-of-two, each in `[−2,2]`). -/
theorem lemma2Fwd_box7_subset : lemma2Fwd '' box7 ⊆ bigbox7 := by
  rintro w ⟨v, hv, rfl⟩
  simp only [box7, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc] at hv
  -- products of two entries lie in [-1,1]
  have hprod : ∀ a b : Fin 7, |v a * v b| ≤ 1 := fun a b => by
    rw [abs_mul]
    exact mul_le_one₀ (abs_le.2 ⟨(hv a).1, (hv a).2⟩) (abs_nonneg _) (abs_le.2 ⟨(hv b).1, (hv b).2⟩)
  have hp05 := abs_le.1 (hprod 0 5); have hp06 := abs_le.1 (hprod 0 6)
  have hp01 := abs_le.1 (hprod 0 1)
  -- the seven explicit entry bounds (literal indices, dodging the `fin_cases` `Fin.mk` friction)
  have e0 : -2 ≤ lemma2Fwd v 0 ∧ lemma2Fwd v 0 ≤ 2 := by
    simp only [lemma2Fwd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, Fin.isValue]; exact ⟨by linarith [(hv 0).1], by linarith [(hv 0).2]⟩
  have e1 : -2 ≤ lemma2Fwd v 1 ∧ lemma2Fwd v 1 ≤ 2 := by
    simp only [lemma2Fwd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, Fin.isValue]
    exact ⟨by linarith [(hv 3).1, hp05.1], by linarith [(hv 3).2, hp05.2]⟩
  have e2 : -2 ≤ lemma2Fwd v 2 ∧ lemma2Fwd v 2 ≤ 2 := by
    simp only [lemma2Fwd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, Fin.isValue]
    exact ⟨by linarith [(hv 4).1, hp06.1], by linarith [(hv 4).2, hp06.2]⟩
  have e3 : -2 ≤ lemma2Fwd v 3 ∧ lemma2Fwd v 3 ≤ 2 := by
    simp only [lemma2Fwd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, Fin.isValue]
    exact ⟨by linarith [(hv 2).1, hp01.2], by linarith [(hv 2).2, hp01.1]⟩
  have e4 : -2 ≤ lemma2Fwd v 4 ∧ lemma2Fwd v 4 ≤ 2 := by
    simp only [lemma2Fwd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, Fin.isValue]; exact ⟨by linarith [(hv 1).1], by linarith [(hv 1).2]⟩
  have e5 : -2 ≤ lemma2Fwd v 5 ∧ lemma2Fwd v 5 ≤ 2 := by
    simp only [lemma2Fwd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, Fin.isValue]; exact ⟨by linarith [(hv 5).1], by linarith [(hv 5).2]⟩
  have e6 : -2 ≤ lemma2Fwd v 6 ∧ lemma2Fwd v 6 ≤ 2 := by
    simp only [lemma2Fwd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, Fin.isValue]; exact ⟨by linarith [(hv 6).1], by linarith [(hv 6).2]⟩
  intro i _
  simp only [bigbox7, Set.mem_Icc]
  fin_cases i
  · exact e0
  · exact e1
  · exact e2
  · exact e3
  · exact e4
  · exact e5
  · exact e6

/-- **The resolved-form finiteness over the bounded box** (the inner step-2/step-3 recursion). For
`c' < 3/2`, `∫⁻_{bigbox7} |resolvedForm w|^{−c'} < ⊤`. The remaining `sorry`: the `recStep {1,2,3}`
blow-up of `resolvedForm` (E/F0/δ cells) + per-cell Tonelli pivot-peel (each unit/block `≥ 1`). -/
theorem resolved_residual_lt_top (c' : NNReal) (hc' : (c':ℝ) < 3/2) :
    ∫⁻ w in bigbox7, ENNReal.ofReal (|resolvedForm w| ^ (-(c':ℝ))) < ⊤ := by
  sorry

theorem tail_residual_lt_top (c' : NNReal) (hc' : (c':ℝ) < 3/2) :
    ∫⁻ v in box7, ENNReal.ofReal (|step1Residual v| ^ (-(c':ℝ))) < ⊤ := by
  -- step1Residual = resolvedForm ∘ lemma2Fwd
  have hpt : ∀ v, ENNReal.ofReal (|step1Residual v| ^ (-(c':ℝ)))
      = (fun w => ENNReal.ofReal (|resolvedForm w| ^ (-(c':ℝ)))) (lemma2Fwd v) := by
    intro v; rw [step1Residual_eq_resolvedForm]
  simp_rw [hpt]
  have hmp : MeasurePreserving lemma2Fwd (volume : Measure (Fin 7 → ℝ)) volume :=
    measurePreserving_lemma2
  have hemb : MeasurableEmbedding lemma2Fwd := by
    have : lemma2Fwd = ⇑lemma2Hom := rfl
    rw [this]; exact lemma2Hom.measurableEmbedding
  rw [hmp.setLIntegral_comp_emb hemb (fun w => ENNReal.ofReal (|resolvedForm w| ^ (-(c':ℝ)))) box7]
  refine lt_of_le_of_lt (lintegral_mono_set lemma2Fwd_box7_subset) ?_
  exact resolved_residual_lt_top c' hc'

/-- **The `p = 0` A-pivot summand is finite** (below `3/2`), modulo `resolved_residual_lt_top`. Assembles
the chain: cube domination → drop the `openBox` cutoff → factor a.e. → Tonelli pivot-peel →
`x₀`-factor finite × tail finite (`tail_residual_lt_top`, which reduces to the resolved form). -/
theorem p0_summand_via_tail (c' : NNReal) (hc' : (c':ℝ) < 3/2) :
    ∫⁻ x in chartDomOn Aact 0 \ pivotZeroOn 0, p0integrand c' x < ⊤ := by
  -- step A: ≤ cube8 integral (gated)
  refine lt_of_le_of_lt (p0_summand_le_cube c') ?_
  -- step B: drop the openBox indicator, get |x0|^3 form (probe 1)
  refine lt_of_le_of_lt
    (show ∫⁻ x in cube8, p0integrand c' x
        ≤ ∫⁻ x in cube8, ENNReal.ofReal (|x 0| ^ 3 * |myF222 (step1A x)| ^ (-(c':ℝ))) from ?_) ?_
  · apply lintegral_mono; intro x
    simp only [p0integrand]
    rw [show (Aact : Finset (Fin 8)) = ({0,1,2,3} : Finset (Fin 8)) from rfl, step1A_det, abs_pow,
      show (pivotBlowupOn ({0,1,2,3} : Finset (Fin 8)) 0 x) = step1A x from
        (step1A_eq_pivotBlowupOn x).symm]
    by_cases h : step1A x ∈ openBox
    · rw [Set.indicator_of_mem h, ← ENNReal.ofReal_mul (by positivity)]
    · rw [Set.indicator_of_notMem h, mul_zero]; exact zero_le _
  -- step C: factor a.e. (off x0=0 null) into the product form, then Tonelli
  rw [show (∫⁻ x in cube8, ENNReal.ofReal (|x 0| ^ 3 * |myF222 (step1A x)| ^ (-(c':ℝ))))
        = ∫⁻ x in cube8, ENNReal.ofReal (|x 0| ^ (3 - 2*(c':ℝ)))
            * ENNReal.ofReal (|step1Residual (Fin.tail x)| ^ (-(c':ℝ))) from ?_]
  · have hsrmeas : Measurable (fun v : Fin 7 → ℝ => step1Residual v) := by
      unfold step1Residual; fun_prop
    rw [cube8_tonelli_peel (fun x0 => ENNReal.ofReal (|x0| ^ (3 - 2*(c':ℝ))))
        (fun v => ENNReal.ofReal (|step1Residual v| ^ (-(c':ℝ))))
        (ENNReal.measurable_ofReal.comp (by fun_prop))
        (ENNReal.measurable_ofReal.comp (by fun_prop))]
    exact ENNReal.mul_lt_top (x0_lintegral_lt_top c' (by linarith)) (tail_residual_lt_top c' hc')
  · -- a.e. congr off the null {x0 = 0}
    refine setLIntegral_congr_fun_ae cube8_meas ?_
    have hae : ∀ᵐ x ∂(volume : Measure (Fin 8 → ℝ)), x 0 ≠ 0 := by
      rw [ae_iff]; simpa using coordZero_null 0
    filter_upwards [hae] with x hx0 _
    exact p0_integrand_factor c' x hx0

end DLNFibre.DLN.RLCT
