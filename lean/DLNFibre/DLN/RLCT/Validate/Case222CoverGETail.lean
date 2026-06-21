import DLNFibre.DLN.RLCT.Validate.Case222CoverGE
import DLNFibre.DLN.RLCT.Foundations.S1Fubini
import DLNFibre.DLN.RLCT.Foundations.S1SmoothBlock

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

open MeasureTheory Set Metric
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

/-- The symmetric box `[−T,T]^m` (the bounded chart domain at half-width `T`). -/
noncomputable def boxT (m : ℕ) (T : ℝ) : Set (Fin m → ℝ) := Set.univ.pi (fun _ => Set.Icc (-T) T)

/-- **1-D `rpow` lintegral finiteness.** `∫⁻_{[−T,T]} |x|^a < ⊤` for `a > −1`: `|x|^a` is integrable
on the symmetric interval (`abs_rpow_integrableOn_Icc_symm_iff`), and the `< ⊤` form follows from the
nonneg `hasFiniteIntegral_iff_ofReal` bridge. The per-axis convergent atom of the box pivot-peel. -/
theorem abs_rpow_lintegral_Icc_lt_top (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : -1 < a) :
    ∫⁻ x in Set.Icc (-T) T, ENNReal.ofReal (|x| ^ a) < ⊤ := by
  have hint : IntegrableOn (fun x : ℝ => |x| ^ a) (Set.Icc (-T) T) volume := by
    rw [abs_rpow_integrableOn_Icc_symm_iff a T hT]; exact ha
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc (-T) T)] (fun x : ℝ => |x| ^ a) :=
    ae_of_all _ (fun x => Real.rpow_nonneg (abs_nonneg _) _)
  rw [IntegrableOn, Integrable, hasFiniteIntegral_iff_ofReal hnn] at hint
  convert hint.2 using 1

/-- **Single-coordinate monomial over a box is finite.** `∫⁻_{[−T,T]^{n+1}} |x p|^a < ⊤` for
`a > −1`: peel coordinate `p` via the measure-preserving `piFinSuccAbove p` into `ℝ × (Fin n → ℝ)`,
Tonelli-separate (`lintegral_prod_mul`) into the convergent pivot factor (`abs_rpow_lintegral_Icc_lt_top`)
times the constant `1` over the compact box (`IsCompact.measure_lt_top`). The reusable terminal of the
resolved-form per-cell pivot-peel: a leaf's integrand is bounded by such a single-coord monomial. -/
theorem boxT_coord_rpow_lt_top {n : ℕ} (T : ℝ) (hT : 0 < T) (p : Fin (n+1)) (a : ℝ) (ha : -1 < a) :
    ∫⁻ x in boxT (n+1) T, ENNReal.ofReal (|x p| ^ a) < ⊤ := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) p with he
  have hmp : MeasurePreserving e (volume : Measure (Fin (n+1) → ℝ)) volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) p
  have hemb : MeasurableEmbedding e := e.measurableEmbedding
  have heapp : ∀ x : Fin (n+1) → ℝ, e x = (x p, fun j => x (p.succAbove j)) := fun x => rfl
  have hpre : boxT (n+1) T = e ⁻¹' (Set.Icc (-T) T ×ˢ boxT n T) := by
    ext x
    simp only [boxT, Set.mem_preimage, heapp, Set.mem_prod, Set.mem_pi, Set.mem_univ,
      true_implies, Set.mem_Icc]
    constructor
    · intro h; exact ⟨h p, fun j => h (p.succAbove j)⟩
    · rintro ⟨hp, hrest⟩ i
      rcases Fin.eq_self_or_eq_succAbove p i with rfl | ⟨j, rfl⟩
      · exact hp
      · exact hrest j
  rw [hpre]
  rw [show (fun x : Fin (n+1) → ℝ => ENNReal.ofReal (|x p| ^ a))
        = (fun x : Fin (n+1) → ℝ =>
            (fun q : ℝ × (Fin n → ℝ) =>
              (fun x0 : ℝ => ENNReal.ofReal (|x0| ^ a)) q.1 * (fun _ : Fin n → ℝ => (1:ℝ≥0∞)) q.2)
              (e x))
        from by funext x; rw [heapp]; simp]
  rw [hmp.setLIntegral_comp_preimage_emb hemb
    (fun q : ℝ × (Fin n → ℝ) =>
      (fun x0 : ℝ => ENNReal.ofReal (|x0| ^ a)) q.1 * (fun _ : Fin n → ℝ => (1:ℝ≥0∞)) q.2)
    (Set.Icc (-T) T ×ˢ boxT n T)]
  rw [show (volume : Measure (ℝ × (Fin n → ℝ))) = (volume : Measure ℝ).prod volume from
        Measure.volume_eq_prod _ _, ← Measure.prod_restrict,
    lintegral_prod_mul (f := fun x0 : ℝ => ENNReal.ofReal (|x0| ^ a))
      (g := fun _ : Fin n → ℝ => (1:ℝ≥0∞))
      (ENNReal.measurable_ofReal.comp (by fun_prop)).aemeasurable measurable_const.aemeasurable]
  refine ENNReal.mul_lt_top (abs_rpow_lintegral_Icc_lt_top T hT a ha) ?_
  rw [lintegral_const, one_mul, Measure.restrict_apply_univ]
  exact (isCompact_univ_pi (fun _ => isCompact_Icc)).measure_lt_top

/-! ## The resolved-form recursion (`recStep {1,2,3}` → E/F0/δ cells)

`∫⁻_{bigbox7} |resolvedForm|^{−c'}` splits (via `recStep {1,2,3} 1`) into the three step-2 pivot cells.
The E (`q=1`) and F0 (`q=2`) cells are UNIT leaves (`resolvedForm (φ₂q z) = z_q²·U`, `U ≥ 1`): support
containment (`step2E_support_box` / `pivotF0_support_box`: the `bigbox7` cutoff bounds `z` into a box)
+ the pointwise bound to the single-coord monomial `|z_q|^{2−2c'}` (`U^{−c'} ≤ 1`) + the box terminal
`boxT_coord_rpow_lt_top` (`2−2c' > −1 ⟺ c' < 3/2`). The δ (`q=3`) cell is the BLOCK branch
(`resolvedForm (φ₂₃ z) = z3²·block`, `block` vanishing) — it needs step-3 (`block_residual_lt_top`). -/

theorem step2E_support_box (z : Fin 7 → ℝ) (hcd : z ∈ chartDomOn ({1,2,3} : Finset (Fin 7)) 1)
    (hb : step2E z ∈ bigbox7) : z ∈ boxT 7 2 := by
  simp only [bigbox7, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc] at hb
  have h2 : |z 2| ≤ 1 := hcd 2 (by decide) (by decide)
  have h3 : |z 3| ≤ 1 := hcd 3 (by decide) (by decide)
  have b0 : -2 ≤ z 0 ∧ z 0 ≤ 2 := by have := hb 0; simpa [step2E] using this
  have b1 : -2 ≤ z 1 ∧ z 1 ≤ 2 := by have := hb 1; simpa [step2E] using this
  have b2 : -2 ≤ z 2 ∧ z 2 ≤ 2 := ⟨by linarith [abs_le.1 h2], by linarith [abs_le.1 h2]⟩
  have b3 : -2 ≤ z 3 ∧ z 3 ≤ 2 := ⟨by linarith [abs_le.1 h3], by linarith [abs_le.1 h3]⟩
  have b4 : -2 ≤ z 4 ∧ z 4 ≤ 2 := by have := hb 4; simpa [step2E] using this
  have b5 : -2 ≤ z 5 ∧ z 5 ≤ 2 := by have := hb 5; simpa [step2E] using this
  have b6 : -2 ≤ z 6 ∧ z 6 ≤ 2 := by have := hb 6; simpa [step2E] using this
  intro i _
  simp only [boxT, Set.mem_Icc] at *
  fin_cases i
  · exact b0
  · exact b1
  · exact b2
  · exact b3
  · exact b4
  · exact b5
  · exact b6

-- pointwise: the E-cell integrand at z (using step2E = pivotBlowupOn {1,2,3} 1) factors and bounds.
theorem Ecell_integrand_bound (c' : NNReal) (z : Fin 7 → ℝ)
    (hz : z ∈ chartDomOn ({1,2,3} : Finset (Fin 7)) 1 \ pivotZeroOn 1) :
    ENNReal.ofReal |(pivotBlowupOnDeriv ({1,2,3} : Finset (Fin 7)) 1 z).det|
        * bigbox7.indicator (fun w => ENNReal.ofReal (|resolvedForm w| ^ (-(c':ℝ))))
            (pivotBlowupOn ({1,2,3} : Finset (Fin 7)) 1 z)
      ≤ (boxT 7 2).indicator (fun z => ENNReal.ofReal (|z 1| ^ (2 - 2*(c':ℝ)))) z := by
  rw [show pivotBlowupOn ({1,2,3} : Finset (Fin 7)) 1 z = step2E z from (step2E_eq_pivotBlowupOn z).symm,
      step2E_det]
  by_cases hb : step2E z ∈ bigbox7
  · rw [Set.indicator_of_mem hb]
    rw [Set.indicator_of_mem (step2E_support_box z hz.1 hb)]
    -- |z1²| · |resolvedForm(step2E z)|^{-c'} ≤ |z1|^{2-2c'}
    rw [resolvedForm_step2E]
    have hz1 : z 1 ≠ 0 := hz.2
    have hUge : (1:ℝ) ≤ 1 + (z 2)^2 + (z 4 + z 3 * z 5)^2 + (z 4 * z 2 + z 3 * z 6)^2 :=
      step2E_unit_ge_one z
    -- ofReal(|z1²|) * ofReal(|z1²·U|^{-c'}) ≤ ofReal(|z1|^{2-2c'})
    rw [← ENNReal.ofReal_mul (abs_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    set U := 1 + (z 2)^2 + (z 4 + z 3 * z 5)^2 + (z 4 * z 2 + z 3 * z 6)^2 with hUdef
    have hUpos : 0 < U := lt_of_lt_of_le one_pos hUge
    have hz1a : (0:ℝ) < |z 1| := abs_pos.2 hz1
    -- the clean real bound: |z1²| · |z1²·U|^{-c'} = |z1|^{2-2c'} · U^{-c'}
    have key : |z 1 ^ 2| * |z 1 ^ 2 * U| ^ (-(c':ℝ)) = |z 1| ^ (2 - 2*(c':ℝ)) * U ^ (-(c':ℝ)) := by
      rw [show |z 1 ^ 2 * U| = |z 1| ^ 2 * U from by rw [abs_mul, abs_pow, abs_of_pos hUpos],
          show |z 1 ^ 2| = |z 1| ^ 2 from by rw [abs_pow],
          Real.mul_rpow (by positivity) hUpos.le]
      have h2 : (|z 1| ^ 2 : ℝ) = |z 1| ^ (2:ℝ) := by rw [← Real.rpow_natCast (|z 1|) 2]; norm_num
      rw [h2, ← Real.rpow_mul (abs_nonneg _), ← mul_assoc, ← Real.rpow_add hz1a]
      congr 2 <;> push_cast <;> ring
    rw [key]
    calc |z 1| ^ (2 - 2*(c':ℝ)) * U ^ (-(c':ℝ))
        ≤ |z 1| ^ (2 - 2*(c':ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_one_of_one_le_of_nonpos hUge (neg_nonpos.2 (by positivity)))
            (Real.rpow_nonneg (abs_nonneg _) _)
      _ = |z 1| ^ (2 - 2*(c':ℝ)) := mul_one _
  · rw [Set.indicator_of_notMem hb, mul_zero]; exact zero_le _

theorem Ecell_lt_top (c' : NNReal) (hc' : (c':ℝ) < 3/2) :
    ∫⁻ z in chartDomOn ({1,2,3} : Finset (Fin 7)) 1 \ pivotZeroOn 1,
        ENNReal.ofReal |(pivotBlowupOnDeriv ({1,2,3} : Finset (Fin 7)) 1 z).det|
          * bigbox7.indicator (fun w => ENNReal.ofReal (|resolvedForm w| ^ (-(c':ℝ))))
              (pivotBlowupOn ({1,2,3} : Finset (Fin 7)) 1 z) < ⊤ := by
  have hmono : ∫⁻ z in chartDomOn ({1,2,3} : Finset (Fin 7)) 1 \ pivotZeroOn 1,
        ENNReal.ofReal |(pivotBlowupOnDeriv ({1,2,3} : Finset (Fin 7)) 1 z).det|
          * bigbox7.indicator (fun w => ENNReal.ofReal (|resolvedForm w| ^ (-(c':ℝ))))
              (pivotBlowupOn ({1,2,3} : Finset (Fin 7)) 1 z)
      ≤ ∫⁻ z in boxT 7 2, ENNReal.ofReal (|z 1| ^ (2 - 2*(c':ℝ))) := by
    rw [← lintegral_indicator (chartDomOn_diff_measurableSet _ _),
        ← lintegral_indicator (by exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc) :
          MeasurableSet (boxT 7 2))]
    apply lintegral_mono
    intro z
    by_cases hz : z ∈ chartDomOn ({1,2,3} : Finset (Fin 7)) 1 \ pivotZeroOn 1
    · rw [Set.indicator_of_mem hz]
      exact Ecell_integrand_bound c' z hz
    · rw [Set.indicator_of_notMem hz]; exact zero_le _
  exact lt_of_le_of_lt hmono (boxT_coord_rpow_lt_top 2 (by norm_num) 1 (2 - 2*(c':ℝ)) (by linarith))

-- ===== F0-cell (q=2), mirror of E (resolvedForm_pivotF0 / pivotF0_unit_ge_one) =====
theorem pivotBlowupF0_apply (z : Fin 7 → ℝ) :
    pivotBlowupOn ({1,2,3} : Finset (Fin 7)) 2 z = ![z 0, z 2 * z 1, z 2, z 2 * z 3, z 4, z 5, z 6] := by
  funext i; fin_cases i <;> simp [pivotBlowupOn, Matrix.cons_val]

theorem pivotF0_support_box (z : Fin 7 → ℝ) (hcd : z ∈ chartDomOn ({1,2,3} : Finset (Fin 7)) 2)
    (hb : pivotBlowupOn ({1,2,3} : Finset (Fin 7)) 2 z ∈ bigbox7) : z ∈ boxT 7 2 := by
  rw [pivotBlowupF0_apply] at hb
  simp only [bigbox7, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc] at hb
  have h1 : |z 1| ≤ 1 := hcd 1 (by decide) (by decide)
  have h3 : |z 3| ≤ 1 := hcd 3 (by decide) (by decide)
  have b0 : -2 ≤ z 0 ∧ z 0 ≤ 2 := by have := hb 0; simpa using this
  have b2 : -2 ≤ z 2 ∧ z 2 ≤ 2 := by have := hb 2; simpa using this
  have b1 : -2 ≤ z 1 ∧ z 1 ≤ 2 := ⟨by linarith [abs_le.1 h1], by linarith [abs_le.1 h1]⟩
  have b3 : -2 ≤ z 3 ∧ z 3 ≤ 2 := ⟨by linarith [abs_le.1 h3], by linarith [abs_le.1 h3]⟩
  have b4 : -2 ≤ z 4 ∧ z 4 ≤ 2 := by have := hb 4; simpa using this
  have b5 : -2 ≤ z 5 ∧ z 5 ≤ 2 := by have := hb 5; simpa using this
  have b6 : -2 ≤ z 6 ∧ z 6 ≤ 2 := by have := hb 6; simpa using this
  intro i _; simp only [boxT, Set.mem_Icc] at *
  fin_cases i
  · exact b0
  · exact b1
  · exact b2
  · exact b3
  · exact b4
  · exact b5
  · exact b6

theorem F0cell_integrand_bound (c' : NNReal) (z : Fin 7 → ℝ)
    (hz : z ∈ chartDomOn ({1,2,3} : Finset (Fin 7)) 2 \ pivotZeroOn 2) :
    ENNReal.ofReal |(pivotBlowupOnDeriv ({1,2,3} : Finset (Fin 7)) 2 z).det|
        * bigbox7.indicator (fun w => ENNReal.ofReal (|resolvedForm w| ^ (-(c':ℝ))))
            (pivotBlowupOn ({1,2,3} : Finset (Fin 7)) 2 z)
      ≤ (boxT 7 2).indicator (fun z => ENNReal.ofReal (|z 2| ^ (2 - 2*(c':ℝ)))) z := by
  rw [show (pivotBlowupOnDeriv ({1,2,3} : Finset (Fin 7)) 2 z).det = (z 2)^2 from by
        rw [pivotBlowupOnDeriv_det _ _ (by decide)];
        norm_num [show ({1,2,3} : Finset (Fin 7)).card = 3 from by decide]]
  by_cases hb : pivotBlowupOn ({1,2,3} : Finset (Fin 7)) 2 z ∈ bigbox7
  · rw [Set.indicator_of_mem hb, Set.indicator_of_mem (pivotF0_support_box z hz.1 hb),
      resolvedForm_pivotF0]
    have hz2 : z 2 ≠ 0 := hz.2
    have hUge := pivotF0_unit_ge_one z
    rw [← ENNReal.ofReal_mul (abs_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    set U := 1 + (z 1)^2 + (z 4 * z 1 + z 3 * z 5)^2 + (z 4 + z 3 * z 6)^2 with hUdef
    have hUpos : 0 < U := lt_of_lt_of_le one_pos hUge
    have hz2a : (0:ℝ) < |z 2| := abs_pos.2 hz2
    have key : |z 2 ^ 2| * |z 2 ^ 2 * U| ^ (-(c':ℝ)) = |z 2| ^ (2 - 2*(c':ℝ)) * U ^ (-(c':ℝ)) := by
      rw [show |z 2 ^ 2 * U| = |z 2| ^ 2 * U from by rw [abs_mul, abs_pow, abs_of_pos hUpos],
          show |z 2 ^ 2| = |z 2| ^ 2 from by rw [abs_pow],
          Real.mul_rpow (by positivity) hUpos.le]
      have h2 : (|z 2| ^ 2 : ℝ) = |z 2| ^ (2:ℝ) := by rw [← Real.rpow_natCast (|z 2|) 2]; norm_num
      rw [h2, ← Real.rpow_mul (abs_nonneg _), ← mul_assoc, ← Real.rpow_add hz2a]
      congr 2 <;> push_cast <;> ring
    rw [key]
    calc |z 2| ^ (2 - 2*(c':ℝ)) * U ^ (-(c':ℝ))
        ≤ |z 2| ^ (2 - 2*(c':ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_one_of_one_le_of_nonpos hUge (neg_nonpos.2 (by positivity)))
            (Real.rpow_nonneg (abs_nonneg _) _)
      _ = |z 2| ^ (2 - 2*(c':ℝ)) := mul_one _
  · rw [Set.indicator_of_notMem hb, mul_zero]; exact zero_le _

theorem F0cell_lt_top (c' : NNReal) (hc' : (c':ℝ) < 3/2) :
    ∫⁻ z in chartDomOn ({1,2,3} : Finset (Fin 7)) 2 \ pivotZeroOn 2,
        ENNReal.ofReal |(pivotBlowupOnDeriv ({1,2,3} : Finset (Fin 7)) 2 z).det|
          * bigbox7.indicator (fun w => ENNReal.ofReal (|resolvedForm w| ^ (-(c':ℝ))))
              (pivotBlowupOn ({1,2,3} : Finset (Fin 7)) 2 z) < ⊤ := by
  have hmono : ∫⁻ z in chartDomOn ({1,2,3} : Finset (Fin 7)) 2 \ pivotZeroOn 2,
        ENNReal.ofReal |(pivotBlowupOnDeriv ({1,2,3} : Finset (Fin 7)) 2 z).det|
          * bigbox7.indicator (fun w => ENNReal.ofReal (|resolvedForm w| ^ (-(c':ℝ))))
              (pivotBlowupOn ({1,2,3} : Finset (Fin 7)) 2 z)
      ≤ ∫⁻ z in boxT 7 2, ENNReal.ofReal (|z 2| ^ (2 - 2*(c':ℝ))) := by
    rw [← lintegral_indicator (chartDomOn_diff_measurableSet _ _),
        ← lintegral_indicator (by exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc) :
          MeasurableSet (boxT 7 2))]
    apply lintegral_mono; intro z
    by_cases hz : z ∈ chartDomOn ({1,2,3} : Finset (Fin 7)) 2 \ pivotZeroOn 2
    · rw [Set.indicator_of_mem hz]; exact F0cell_integrand_bound c' z hz
    · rw [Set.indicator_of_notMem hz]; exact zero_le _
  exact lt_of_le_of_lt hmono (boxT_coord_rpow_lt_top 2 (by norm_num) 2 (2 - 2*(c':ℝ)) (by linarith))

-- ===== δ-cell (q=3): block branch — needs step-3 (block vanishes, not ≥1). =====
/-! ## The δ-block smooth-4D finiteness (the EuclideanSpace radial terminal)

The δ-cell block `z1²+z2²+(z4z1+z5)²+(z4z2+z6)²` is, after the det-1 shear `(z5,z6) ↦ (z4z1+z5, z4z2+z6)`,
a clean 4-D sum of squares `Σ⁴ zᵢ²` — a SMOOTH block (RLCT `4/2 = 2 > 3/2`), NOT a step-3 case. The
4-D `Σ²` box integral is finite below `2` via the measure-preserving bridge `(Fin 4 → ℝ) ≃ᵐ
EuclideanSpace ℝ (Fin 4)` (`PiLp.volume_preserving_toLp`) + the radial integrability
`radial_ball_iff` (`‖y‖^{−2c'}` on a ball, `−4 < −2c' ⟺ c' < 2`) + box-⊆-ball domination. -/

-- On EuclideanSpace ℝ (Fin 4): ‖y‖^{-2c'} integrable on any ball for c'<2.
theorem euclid4_ball_integrable (R : ℝ) (hR : 0 < R) (c' : NNReal) (hc' : (c':ℝ) < 2) :
    IntegrableOn (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ (-(2*(c':ℝ)))) (ball 0 R) volume := by
  have := radial_ball_iff 3 R (-(2*(c':ℝ))) hR
  rw [show (3:ℕ)+1 = 4 from rfl] at this
  rw [this]; push_cast; linarith

-- integrand identity: (Σ x_i²)^{-c'} = ‖toLp x‖^{-2c'} (norm_eq), for x : Fin 4 → ℝ.
theorem sumSq4_eq_norm (c' : NNReal) (x : Fin 4 → ℝ) :
    ((∑ i, (x i)^2) ^ (-(c':ℝ))) = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 4))‖ ^ (-(2*(c':ℝ))) := by
  have hnorm : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 4))‖ ^ 2 = ∑ i, (x i)^2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    apply Finset.sum_congr rfl; intro i _
    rw [Real.norm_eq_abs, sq_abs]
  rw [← hnorm, ← Real.rpow_natCast ‖_‖ 2, ← Real.rpow_mul (norm_nonneg _)]
  ring_nf

-- 4-D core finiteness over the box, via transport to EuclideanSpace + ball domination.
theorem sumSq4_box_lt_top (T : ℝ) (hT : 0 < T) (c' : NNReal) (hc' : (c':ℝ) < 2) :
    ∫⁻ x in boxT 4 T, ENNReal.ofReal ((∑ i, (x i)^2) ^ (-(c':ℝ))) < ⊤ := by
  -- IntegrableOn on the box (Fin 4 → ℝ), then lintegral < ⊤.
  have hmp : MeasurePreserving (WithLp.toLp 2 : (Fin 4 → ℝ) → EuclideanSpace ℝ (Fin 4)) :=
    PiLp.volume_preserving_toLp (Fin 4)
  have hemb : MeasurableEmbedding (WithLp.toLp 2 : (Fin 4 → ℝ) → EuclideanSpace ℝ (Fin 4)) :=
    (MeasurableEquiv.toLp 2 (Fin 4 → ℝ)).measurableEmbedding
  set R := 2*T + 1 with hRdef
  have hRpos : 0 < R := by positivity
  -- the box maps into ball 0 R
  have hsub : (WithLp.toLp 2 : (Fin 4 → ℝ) → EuclideanSpace ℝ (Fin 4)) '' boxT 4 T ⊆ ball 0 R := by
    rintro y ⟨x, hx, rfl⟩
    simp only [boxT, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc] at hx
    rw [mem_ball_zero_iff, EuclideanSpace.norm_eq]
    have hb : ∀ i, (x i)^2 ≤ T^2 := fun i => by
      rcases hx i with ⟨h1, h2⟩; nlinarith
    calc Real.sqrt (∑ i, ‖x i‖^2) ≤ Real.sqrt (∑ i : Fin 4, T^2) := by
            apply Real.sqrt_le_sqrt; apply Finset.sum_le_sum; intro i _
            rw [Real.norm_eq_abs, sq_abs]; exact hb i
      _ = Real.sqrt (4 * T^2) := by
            congr 1; rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; norm_num
      _ < R := by
            rw [hRdef, show (4:ℝ)*T^2 = (2*T)^2 from by ring, Real.sqrt_sq (by positivity)]
            linarith
  -- IntegrableOn (Σ x_i²)^{-c'} on box via transport
  have hint : IntegrableOn (fun x : Fin 4 → ℝ => (∑ i, (x i)^2) ^ (-(c':ℝ))) (boxT 4 T) volume := by
    have hball := euclid4_ball_integrable R hRpos c' hc'
    have hballbox : IntegrableOn (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ (-(2*(c':ℝ))))
        (WithLp.toLp 2 '' boxT 4 T) volume := hball.mono_set hsub
    rw [hmp.integrableOn_image hemb] at hballbox
    refine hballbox.congr_fun ?_ (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))
    intro x _; exact (sumSq4_eq_norm c' x).symm
  -- IntegrableOn → lintegral < ⊤
  have hnn : 0 ≤ᵐ[volume.restrict (boxT 4 T)] (fun x : Fin 4 → ℝ => (∑ i, (x i)^2) ^ (-(c':ℝ))) :=
    ae_of_all _ (fun x => Real.rpow_nonneg (by positivity) _)
  rw [IntegrableOn, Integrable, hasFiniteIntegral_iff_ofReal hnn] at hint
  convert hint.2 using 1

/-! ## The δ-block shear (block → Σ⁴ squares, measure-preserving)

`block z = z1²+z2²+(z4z1+z5)²+(z4z2+z6)²` equals, under the det-1 measure-preserving shear `shearΦ`
(`z5 ↦ z5+z4z1`, `z6 ↦ z6+z4z2`; the off-diagonal `z4`-coupling shifted into the squared slots), the
clean 4-D sum of squares `Σ_{i∈{1,2,5,6}} (shearΦ z)ᵢ²`. Two `measurePreserving_shearAt` (bridged to
the explicit `Function.update` form via the `succAbove`-index `decide`), composed. The block residual
then transports to the smooth-4D `sumSq4_box_lt_top` terminal (RLCT 2 > 3/2). -/

-- single shear m.p. helper (proven above)
theorem shear5_mp : MeasurePreserving
    (fun z : Fin 7 → ℝ => Function.update z 5 (z 5 + z 4 * z 1))
    (volume : Measure (Fin 7 → ℝ)) volume := by
  have h := measurePreserving_shearAt (n := 6) 5 (fun w : Fin 6 → ℝ => w 4 * w 1) (by fun_prop)
  have hidx4 : ((5:Fin 7).succAbove 4) = 4 := by decide
  have hidx1 : ((5:Fin 7).succAbove 1) = 1 := by decide
  have heq : (fun z : Fin 7 → ℝ => Function.update z 5
          (z 5 + (fun w : Fin 6 → ℝ => w 4 * w 1) (fun k => z ((5:Fin 7).succAbove k))))
        = (fun z : Fin 7 → ℝ => Function.update z 5 (z 5 + z 4 * z 1)) := by
    funext z; simp only [hidx4, hidx1]
  rw [← heq]; exact h

-- shear 6 (add z4·z2 to z6)
theorem shear6_mp : MeasurePreserving
    (fun z : Fin 7 → ℝ => Function.update z 6 (z 6 + z 4 * z 2))
    (volume : Measure (Fin 7 → ℝ)) volume := by
  have h := measurePreserving_shearAt (n := 6) 6 (fun w : Fin 6 → ℝ => w 4 * w 2) (by fun_prop)
  have hidx4 : ((6:Fin 7).succAbove 4) = 4 := by decide
  have hidx2 : ((6:Fin 7).succAbove 2) = 2 := by decide
  have heq : (fun z : Fin 7 → ℝ => Function.update z 6
          (z 6 + (fun w : Fin 6 → ℝ => w 4 * w 2) (fun k => z ((6:Fin 7).succAbove k))))
        = (fun z : Fin 7 → ℝ => Function.update z 6 (z 6 + z 4 * z 2)) := by
    funext z; simp only [hidx4, hidx2]
  rw [← heq]; exact h

-- composed shear Φ = shear6 ∘ shear5 (order: shear5 first since shear6 doesn't touch z5)
noncomputable def shearΦ (z : Fin 7 → ℝ) : Fin 7 → ℝ :=
  Function.update (Function.update z 5 (z 5 + z 4 * z 1)) 6 (z 6 + z 4 * z 2)

theorem shearΦ_mp : MeasurePreserving shearΦ (volume : Measure (Fin 7 → ℝ)) volume := by
  have hcomp := shear6_mp.comp shear5_mp
  have heq : (fun z : Fin 7 → ℝ => Function.update z 6 (z 6 + z 4 * z 2)) ∘
      (fun z : Fin 7 → ℝ => Function.update z 5 (z 5 + z 4 * z 1)) = shearΦ := by
    funext z
    unfold shearΦ
    simp only [Function.comp_apply]
    -- shear6 of (shear5 z): value at 6 reads coords 4,2 of (shear5 z), which are unchanged (≠5)
    rw [Function.update_of_ne (show (4:Fin 7) ≠ 5 by decide),
        Function.update_of_ne (show (2:Fin 7) ≠ 5 by decide),
        Function.update_of_ne (show (6:Fin 7) ≠ 5 by decide)]
  rw [← heq]; exact hcomp

-- block identity: block(z) = (Σ over {1,2,5,6} of (shearΦ z)_i²)
theorem block_eq_shear (z : Fin 7 → ℝ) :
    (z 1)^2 + (z 2)^2 + (z 4 * z 1 + z 5)^2 + (z 4 * z 2 + z 6)^2
      = ((shearΦ z) 1)^2 + ((shearΦ z) 2)^2 + ((shearΦ z) 5)^2 + ((shearΦ z) 6)^2 := by
  unfold shearΦ
  -- slot1: ≠6,≠5 ; slot2: ≠6,≠5 ; slot5: ≠6, =5 ; slot6: =6
  rw [show ((Function.update (Function.update z 5 (z 5 + z 4 * z 1)) 6 (z 6 + z 4 * z 2)) 1)
        = z 1 from by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)],
      show ((Function.update (Function.update z 5 (z 5 + z 4 * z 1)) 6 (z 6 + z 4 * z 2)) 2)
        = z 2 from by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)],
      show ((Function.update (Function.update z 5 (z 5 + z 4 * z 1)) 6 (z 6 + z 4 * z 2)) 5)
        = z 5 + z 4 * z 1 from by rw [Function.update_of_ne (by decide), Function.update_self],
      show ((Function.update (Function.update z 5 (z 5 + z 4 * z 1)) 6 (z 6 + z 4 * z 2)) 6)
        = z 6 + z 4 * z 2 from by rw [Function.update_self]]
  ring

/-- **Spectator-peel for a box integral.** An integrand that depends only on the non-`p` coordinates
factors out the `p`-axis: `∫⁻_{[−T,T]^{n+1}} h(drop-p x) = (∫⁻_{[−T,T]^n} h) · vol[−T,T]`
(measure-preserving `piFinSuccAbove p` + `lintegral_prod_mul` with the constant-`1` `p`-factor). Reduces
the δ-block `Σ⁴`-integral over `Fin 7` to `Fin 4` by peeling the three spectator coordinates. -/
theorem boxT_peel_spectator {n : ℕ} (T : ℝ) (hT : 0 < T) (p : Fin (n+1))
    (h : (Fin n → ℝ) → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ x in boxT (n+1) T, h (fun k => x (p.succAbove k))
      = (∫⁻ y in boxT n T, h y) * (volume (Set.Icc (-T) T)) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) p with he
  have hmp : MeasurePreserving e (volume : Measure (Fin (n+1) → ℝ)) volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) p
  have hemb : MeasurableEmbedding e := e.measurableEmbedding
  have heapp : ∀ x : Fin (n+1) → ℝ, e x = (x p, fun k => x (p.succAbove k)) := fun x => rfl
  have hpre : boxT (n+1) T = e ⁻¹' (Set.Icc (-T) T ×ˢ boxT n T) := by
    ext x
    simp only [boxT, Set.mem_preimage, heapp, Set.mem_prod, Set.mem_pi, Set.mem_univ,
      true_implies, Set.mem_Icc]
    constructor
    · intro hx; exact ⟨hx p, fun k => hx (p.succAbove k)⟩
    · rintro ⟨hp, hrest⟩ i
      rcases Fin.eq_self_or_eq_succAbove p i with rfl | ⟨j, rfl⟩
      · exact hp
      · exact hrest j
  rw [hpre]
  rw [show (fun x : Fin (n+1) → ℝ => h (fun k => x (p.succAbove k)))
        = (fun x : Fin (n+1) → ℝ => (fun q : ℝ × (Fin n → ℝ) => (fun _ : ℝ => (1:ℝ≥0∞)) q.1 * h q.2) (e x))
        from by funext x; rw [heapp]; simp]
  rw [hmp.setLIntegral_comp_preimage_emb hemb
    (fun q : ℝ × (Fin n → ℝ) => (fun _ : ℝ => (1:ℝ≥0∞)) q.1 * h q.2) (Set.Icc (-T) T ×ˢ boxT n T)]
  rw [show (volume : Measure (ℝ × (Fin n → ℝ))) = (volume : Measure ℝ).prod volume from
        Measure.volume_eq_prod _ _, ← Measure.prod_restrict,
    lintegral_prod_mul (f := fun _ : ℝ => (1:ℝ≥0∞)) (g := h) measurable_const.aemeasurable hh.aemeasurable]
  rw [lintegral_const, one_mul, Measure.restrict_apply_univ, mul_comm]

/-! ## The δ-block shear transport (measurable-equiv + image-box domination)

`shearΦ` is a measurable equivalence (`shearΦEquiv`, explicit polynomial inverse `shearΦinv`), hence a
`MeasurableEmbedding` (`shearΦ_emb`) — the transport vehicle for the block integral. Its image of the
witness box `[−2,2]^7` sits in the enlarged box `[−6,6]^7` (`shearΦ_box_subset`: the `z4·z1`/`z4·z2`
shifts grow each coord by at most `4`), so the transported `Σ⁴` integral is dominated by the
`[−6,6]^7` box. -/

/-- The explicit inverse of `shearΦ` (subtract the two shears back). -/
noncomputable def shearΦinv (w : Fin 7 → ℝ) : Fin 7 → ℝ :=
  Function.update (Function.update w 5 (w 5 - w 4 * w 1)) 6 (w 6 - w 4 * w 2)

theorem shearΦinv_shearΦ (z : Fin 7 → ℝ) : shearΦinv (shearΦ z) = z := by
  funext i; unfold shearΦinv shearΦ
  fin_cases i <;>
    simp only [Function.update_self, Function.update_of_ne, ne_eq, Fin.reduceEq,
      not_false_eq_true] <;> ring_nf <;> try rfl

theorem shearΦ_shearΦinv (w : Fin 7 → ℝ) : shearΦ (shearΦinv w) = w := by
  funext i; unfold shearΦinv shearΦ
  fin_cases i <;>
    simp only [Function.update_self, Function.update_of_ne, ne_eq, Fin.reduceEq,
      not_false_eq_true] <;> ring_nf <;> try rfl

theorem measurable_shearΦ : Measurable shearΦ := by unfold shearΦ; fun_prop

theorem measurable_shearΦinv : Measurable shearΦinv := by unfold shearΦinv; fun_prop

noncomputable def shearΦEquiv : (Fin 7 → ℝ) ≃ᵐ (Fin 7 → ℝ) where
  toFun := shearΦ
  invFun := shearΦinv
  left_inv := shearΦinv_shearΦ
  right_inv := shearΦ_shearΦinv
  measurable_toFun := measurable_shearΦ
  measurable_invFun := measurable_shearΦinv

theorem shearΦ_emb : MeasurableEmbedding shearΦ :=
  shearΦEquiv.measurableEmbedding

/-- **`shearΦ` image of `[−2,2]^7` sits in `[−6,6]^7`.** -/
theorem shearΦ_box_subset : shearΦ '' boxT 7 2 ⊆ boxT 7 6 := by
  rintro w ⟨z, hz, rfl⟩
  simp only [boxT, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc] at hz
  -- product bounds |z4·z1| ≤ 4, |z4·z2| ≤ 4
  have hp41 : |z 4 * z 1| ≤ 4 := by
    rw [abs_mul]; have := abs_le.2 ⟨(hz 4).1, (hz 4).2⟩; have := abs_le.2 ⟨(hz 1).1, (hz 1).2⟩
    nlinarith [abs_nonneg (z 4), abs_nonneg (z 1), abs_le.2 (⟨(hz 4).1,(hz 4).2⟩ : -2 ≤ z 4 ∧ z 4 ≤ 2),
      abs_le.2 (⟨(hz 1).1,(hz 1).2⟩ : -2 ≤ z 1 ∧ z 1 ≤ 2)]
  have hp42 : |z 4 * z 2| ≤ 4 := by
    rw [abs_mul]
    nlinarith [abs_nonneg (z 4), abs_nonneg (z 2), abs_le.2 (⟨(hz 4).1,(hz 4).2⟩ : -2 ≤ z 4 ∧ z 4 ≤ 2),
      abs_le.2 (⟨(hz 2).1,(hz 2).2⟩ : -2 ≤ z 2 ∧ z 2 ≤ 2)]
  -- the 7 explicit shearΦ entry bounds
  have b0 : -6 ≤ shearΦ z 0 ∧ shearΦ z 0 ≤ 6 := by
    unfold shearΦ; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    constructor <;> linarith [(hz 0).1, (hz 0).2]
  have b1 : -6 ≤ shearΦ z 1 ∧ shearΦ z 1 ≤ 6 := by
    unfold shearΦ; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    constructor <;> linarith [(hz 1).1, (hz 1).2]
  have b2 : -6 ≤ shearΦ z 2 ∧ shearΦ z 2 ≤ 6 := by
    unfold shearΦ; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    constructor <;> linarith [(hz 2).1, (hz 2).2]
  have b3 : -6 ≤ shearΦ z 3 ∧ shearΦ z 3 ≤ 6 := by
    unfold shearΦ; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    constructor <;> linarith [(hz 3).1, (hz 3).2]
  have b4 : -6 ≤ shearΦ z 4 ∧ shearΦ z 4 ≤ 6 := by
    unfold shearΦ; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    constructor <;> linarith [(hz 4).1, (hz 4).2]
  have b5 : -6 ≤ shearΦ z 5 ∧ shearΦ z 5 ≤ 6 := by
    unfold shearΦ; rw [Function.update_of_ne (by decide), Function.update_self]
    constructor <;> [linarith [(hz 5).1, abs_le.1 hp41]; linarith [(hz 5).2, abs_le.1 hp41]]
  have b6 : -6 ≤ shearΦ z 6 ∧ shearΦ z 6 ≤ 6 := by
    unfold shearΦ; rw [Function.update_self]
    constructor <;> [linarith [(hz 6).1, abs_le.1 hp42]; linarith [(hz 6).2, abs_le.1 hp42]]
  intro i _
  simp only [boxT, Set.mem_Icc]
  fin_cases i
  · exact b0
  · exact b1
  · exact b2
  · exact b3
  · exact b4
  · exact b5
  · exact b6

/-! ## The δ-block spectator-separation chain (Σ⁴-on-{1,2,5,6} → sumSq4 via 3 peels)

After the shear, the δ-block integral is `∫_{[−6,6]⁷} (Σ_{i∈{1,2,5,6}} wᵢ²)^{−c'}`. The three spectator
coordinates (`0, 3, 4`) peel off one at a time (`boxT_peel_spectator`, each contributing a finite
`vol[−6,6]` factor), the integrand reindexing through the successive `succAbove` maps (`g7 → h6 → h5
→ h4`, the `decide`-checked index relabelings), landing on the Fin-4 `Σ`-over-all terminal
`sumSq4_box_lt_top`. -/

-- Σ4 over {0,1,2,3} of Fin 4 (matches sumSq4_box_lt_top's ∑ i, (x i)^2).
-- Build the chain: g7 (Σ over {1,2,5,6} Fin7) → peel 3 spectators → Fin4 Σ-all.
-- Use boxT_peel_spectator 3×. Track integrand via explicit h functions + decide on succAbove.

-- After peeling coord 0 (Fin7→Fin6): {1,2,5,6}→{0,1,4,5}. h6 v = (v0²+v1²+v4²+v5²)^{-c'}.
-- After peeling coord 3 of Fin6 (=old 4, a spectator) (Fin6→Fin5): need 3.succAbove:Fin5→Fin6.
--   3.succAbove sends {0,1,2}→{0,1,2}, {3,4}→{4,5}. So {0,1,4,5}→preimages: 0→0,1→1,4→3,5→4.
--   h5 v = (v0²+v1²+v3²+v4²)^{-c'}.
-- After peeling coord 2 of Fin5 (=old 3, spectator) (Fin5→Fin4): 2.succAbove:Fin4→Fin5 sends {0,1}→{0,1},{2,3}→{3,4}.
--   {0,1,3,4}→preimages: 0→0,1→1,3→2,4→3. h4 v = (v0²+v1²+v2²+v3²)^{-c'} = Σ over all Fin4. ✓

noncomputable def g7 (c' : ℝ) (w : Fin 7 → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (((w 1)^2 + (w 2)^2 + (w 5)^2 + (w 6)^2) ^ (-c'))
noncomputable def h6 (c' : ℝ) (v : Fin 6 → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (((v 0)^2 + (v 1)^2 + (v 4)^2 + (v 5)^2) ^ (-c'))
noncomputable def h5 (c' : ℝ) (v : Fin 5 → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (((v 0)^2 + (v 1)^2 + (v 3)^2 + (v 4)^2) ^ (-c'))
noncomputable def h4 (c' : ℝ) (v : Fin 4 → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (((v 0)^2 + (v 1)^2 + (v 2)^2 + (v 3)^2) ^ (-c'))

theorem g7_peel0 (c' : ℝ) (w : Fin 7 → ℝ) : g7 c' w = h6 c' (fun k => w ((0:Fin 7).succAbove k)) := by
  unfold g7 h6
  simp only [show ((0:Fin 7).succAbove 0 : Fin 7) = 1 from by decide,
      show ((0:Fin 7).succAbove 1 : Fin 7) = 2 from by decide,
      show ((0:Fin 7).succAbove 4 : Fin 7) = 5 from by decide,
      show ((0:Fin 7).succAbove 5 : Fin 7) = 6 from by decide]

theorem h6_peel3 (c' : ℝ) (v : Fin 6 → ℝ) : h6 c' v = h5 c' (fun k => v ((3:Fin 6).succAbove k)) := by
  unfold h6 h5
  simp only [show ((3:Fin 6).succAbove 0 : Fin 6) = 0 from by decide,
      show ((3:Fin 6).succAbove 1 : Fin 6) = 1 from by decide,
      show ((3:Fin 6).succAbove 3 : Fin 6) = 4 from by decide,
      show ((3:Fin 6).succAbove 4 : Fin 6) = 5 from by decide]

theorem h5_peel2 (c' : ℝ) (v : Fin 5 → ℝ) : h5 c' v = h4 c' (fun k => v ((2:Fin 5).succAbove k)) := by
  unfold h5 h4
  simp only [show ((2:Fin 5).succAbove 0 : Fin 5) = 0 from by decide,
      show ((2:Fin 5).succAbove 1 : Fin 5) = 1 from by decide,
      show ((2:Fin 5).succAbove 2 : Fin 5) = 3 from by decide,
      show ((2:Fin 5).succAbove 3 : Fin 5) = 4 from by decide]

-- h4 over boxT 4 6 IS sumSq4_box_lt_top.
theorem h4_box_lt_top (c' : NNReal) (hc' : (c':ℝ) < 2) :
    ∫⁻ v in boxT 4 (6:ℝ), h4 (c':ℝ) v < ⊤ := by
  have := sumSq4_box_lt_top 6 (by norm_num) c' hc'
  refine lt_of_le_of_lt (le_of_eq ?_) this
  apply setLIntegral_congr_fun (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))
  intro v _
  unfold h4
  congr 2
  rw [Fin.sum_univ_four]

-- measurability of the h's
theorem h6_meas (c' : ℝ) : Measurable (h6 c') := by unfold h6; fun_prop
theorem h5_meas (c' : ℝ) : Measurable (h5 c') := by unfold h5; fun_prop
theorem h4_meas (c' : ℝ) : Measurable (h4 c') := by unfold h4; fun_prop

-- chain: ∫ g7 = (∫ h6)·v = (∫ h5)·v·v = (∫ h4)·v³, each v=vol[-6,6]<⊤.
theorem sumSq4_subset_box_lt_top (c' : NNReal) (hc' : (c':ℝ) < 2) :
    ∫⁻ w in boxT 7 (6:ℝ), g7 (c':ℝ) w < ⊤ := by
  have hvol : volume (Set.Icc (-6:ℝ) 6) < ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  -- peel 0: ∫ g7 = ∫ h6(drop0) = (∫_{boxT 6} h6)·vol
  have hstep0 : ∫⁻ w in boxT 7 (6:ℝ), g7 (c':ℝ) w
      = (∫⁻ v in boxT 6 (6:ℝ), h6 (c':ℝ) v) * volume (Set.Icc (-6:ℝ) 6) := by
    rw [show (fun w => g7 (c':ℝ) w) = (fun w : Fin 7 → ℝ => h6 (c':ℝ) (fun k => w ((0:Fin 7).succAbove k)))
          from funext (fun w => g7_peel0 (c':ℝ) w)]
    exact boxT_peel_spectator (n:=6) 6 (by norm_num) 0 (h6 (c':ℝ)) (h6_meas _)
  have hstep1 : ∫⁻ v in boxT 6 (6:ℝ), h6 (c':ℝ) v
      = (∫⁻ v in boxT 5 (6:ℝ), h5 (c':ℝ) v) * volume (Set.Icc (-6:ℝ) 6) := by
    rw [show (fun v => h6 (c':ℝ) v) = (fun v : Fin 6 → ℝ => h5 (c':ℝ) (fun k => v ((3:Fin 6).succAbove k)))
          from funext (fun v => h6_peel3 (c':ℝ) v)]
    exact boxT_peel_spectator (n:=5) 6 (by norm_num) 3 (h5 (c':ℝ)) (h5_meas _)
  have hstep2 : ∫⁻ v in boxT 5 (6:ℝ), h5 (c':ℝ) v
      = (∫⁻ v in boxT 4 (6:ℝ), h4 (c':ℝ) v) * volume (Set.Icc (-6:ℝ) 6) := by
    rw [show (fun v => h5 (c':ℝ) v) = (fun v : Fin 5 → ℝ => h4 (c':ℝ) (fun k => v ((2:Fin 5).succAbove k)))
          from funext (fun v => h5_peel2 (c':ℝ) v)]
    exact boxT_peel_spectator (n:=4) 6 (by norm_num) 2 (h4 (c':ℝ)) (h4_meas _)
  rw [hstep0, hstep1, hstep2]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top (h4_box_lt_top c' hc') hvol) hvol) hvol

/-- **General box pivot-peel.** `∫_{[−T,T]^{n+1}} f(x p)·g(drop-p x) = (∫_{[−T,T]} f)·(∫_{[−T,T]^n} g)` — the arbitrary-slot, nonconstant-tail Tonelli separation (generalises `cube8_tonelli_peel`). -/
-- general pivot-peel: f at coord p × g of the rest, separates (generalizes cube8_tonelli_peel).
theorem boxT_pivot_peel {n : ℕ} (T : ℝ) (p : Fin (n+1)) (f : ℝ → ℝ≥0∞) (g : (Fin n → ℝ) → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ x in boxT (n+1) T, f (x p) * g (fun k => x (p.succAbove k))
      = (∫⁻ t in Set.Icc (-T) T, f t) * (∫⁻ y in boxT n T, g y) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) p with he
  have hmp : MeasurePreserving e (volume : Measure (Fin (n+1) → ℝ)) volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) p
  have hemb : MeasurableEmbedding e := e.measurableEmbedding
  have heapp : ∀ x : Fin (n+1) → ℝ, e x = (x p, fun k => x (p.succAbove k)) := fun x => rfl
  have hpre : boxT (n+1) T = e ⁻¹' (Set.Icc (-T) T ×ˢ boxT n T) := by
    ext x
    simp only [boxT, Set.mem_preimage, heapp, Set.mem_prod, Set.mem_pi, Set.mem_univ,
      true_implies, Set.mem_Icc]
    constructor
    · intro hx; exact ⟨hx p, fun k => hx (p.succAbove k)⟩
    · rintro ⟨hpp, hrest⟩ i
      rcases Fin.eq_self_or_eq_succAbove p i with rfl | ⟨j, rfl⟩
      · exact hpp
      · exact hrest j
  rw [hpre]
  rw [show (fun x : Fin (n+1) → ℝ => f (x p) * g (fun k => x (p.succAbove k)))
        = (fun x : Fin (n+1) → ℝ => (fun q : ℝ × (Fin n → ℝ) => f q.1 * g q.2) (e x))
        from by funext x; rw [heapp]]
  rw [hmp.setLIntegral_comp_preimage_emb hemb (fun q : ℝ × (Fin n → ℝ) => f q.1 * g q.2)
    (Set.Icc (-T) T ×ˢ boxT n T)]
  rw [show (volume : Measure (ℝ × (Fin n → ℝ))) = (volume : Measure ℝ).prod volume from
        Measure.volume_eq_prod _ _, ← Measure.prod_restrict,
    lintegral_prod_mul hf.aemeasurable hg.aemeasurable]

/-- The step-3 block residual finiteness over a bounded box (the 4th-level recursion: blow up
`block = z1²+z2²+(z4z1+z5)²+(z4z2+z6)²` along its vertex, `blockForm_step3` + `step3_unit_ge_one`
+ `block_leaf_integrable`). The δ-cell's inner integral. -/
theorem block_residual_lt_top (c' : NNReal) (hc' : (c':ℝ) < 3/2) :
    ∫⁻ z in boxT 7 (2:ℝ),
        ENNReal.ofReal (|(z 1)^2 + (z 2)^2 + (z 4 * z 1 + z 5)^2 + (z 4 * z 2 + z 6)^2| ^ (-(c':ℝ))) < ⊤ := by
  have hstep : ∀ z, ENNReal.ofReal (|(z 1)^2 + (z 2)^2 + (z 4 * z 1 + z 5)^2 + (z 4 * z 2 + z 6)^2| ^ (-(c':ℝ)))
      = g7 (c':ℝ) (shearΦ z) := by
    intro z
    unfold g7
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (z 1)^2 + (z 2)^2 + (z 4 * z 1 + z 5)^2 + (z 4 * z 2 + z 6)^2),
        block_eq_shear]
  simp_rw [hstep]
  rw [shearΦ_mp.setLIntegral_comp_emb shearΦ_emb (g7 (c':ℝ)) (boxT 7 2)]
  refine lt_of_le_of_lt (lintegral_mono_set shearΦ_box_subset) ?_
  exact sumSq4_subset_box_lt_top c' (by linarith)

/-! ## The δ-cell finiteness (block branch via z3-peel onto the Fin-6 block)

The δ-cell residual `z3²·blockδ` (`resolvedForm_pivotDelta`, `blockδ = z1²+z2²+(z4z1+z5)²+(z4z2+z6)²`,
independent of `z3`). Support-contain to `[−2,2]⁷`, bound the integrand by `|z3|^{2−2c'}·blockδ^{−c'}`,
then `boxT_pivot_peel` separates the `z3`-monomial (finite, `2−2c' > −1 ⟺ c' < 3/2`) from the Fin-6
block `blockδ6` — whose finiteness comes from `block_residual_lt_top` itself by peeling `z3` as a
spectator (`boxT_peel_spectator`), no second shear chain needed. -/

/-- The δ-block as an `ℝ≥0∞`-integrand (`Σ⁴`-form, independent of `z3`). -/
noncomputable def blockδ (c' : ℝ) (z : Fin 7 → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (((z 1)^2 + (z 2)^2 + (z 4 * z 1 + z 5)^2 + (z 4 * z 2 + z 6)^2) ^ (-c'))

/-- The δ-block read on `Fin 6` (after dropping the `z3` pivot via `3.succAbove`). -/
noncomputable def blockδ6 (c' : ℝ) (v : Fin 6 → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (((v 1)^2 + (v 2)^2 + (v 3 * v 1 + v 4)^2 + (v 3 * v 2 + v 5)^2) ^ (-c'))

/-- `blockδ z = blockδ6 (drop-3 z)` (`3.succAbove` sends `{1,2,3,4,5} ↦ {1,2,4,5,6}`). -/
theorem blockδ_peel3 (c' : ℝ) (z : Fin 7 → ℝ) :
    blockδ c' z = blockδ6 c' (fun k => z ((3:Fin 7).succAbove k)) := by
  unfold blockδ blockδ6
  simp only [show ((3:Fin 7).succAbove 1 : Fin 7) = 1 from by decide,
      show ((3:Fin 7).succAbove 2 : Fin 7) = 2 from by decide,
      show ((3:Fin 7).succAbove 3 : Fin 7) = 4 from by decide,
      show ((3:Fin 7).succAbove 4 : Fin 7) = 5 from by decide,
      show ((3:Fin 7).succAbove 5 : Fin 7) = 6 from by decide]

theorem blockδ6_meas (c' : ℝ) : Measurable (blockδ6 c') := by unfold blockδ6; fun_prop

/-- **The Fin-6 δ-block is finite below `3/2`.** Derived from `block_residual_lt_top` (`= ∫ blockδ`
over `[−2,2]⁷`) by peeling `z3` as a spectator (`boxT_peel_spectator`): the Fin-7 block integral
factors as `(∫ blockδ6)·vol[−2,2]`, and `vol[−2,2] ≠ 0` forces `∫ blockδ6 < ⊤`. -/
theorem blockδ6_box_lt_top (c' : NNReal) (hc' : (c':ℝ) < 3/2) :
    ∫⁻ v in boxT 6 (2:ℝ), blockδ6 (c':ℝ) v < ⊤ := by
  have hbr := block_residual_lt_top c' hc'
  have heq : (∫⁻ z in boxT 7 (2:ℝ), ENNReal.ofReal (|(z 1)^2 + (z 2)^2 + (z 4 * z 1 + z 5)^2 + (z 4 * z 2 + z 6)^2| ^ (-(c':ℝ))))
      = ∫⁻ z in boxT 7 (2:ℝ), blockδ (c':ℝ) z := by
    apply setLIntegral_congr_fun (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))
    intro z _; unfold blockδ; simp only
    rw [abs_of_nonneg (by positivity)]
  rw [heq] at hbr
  rw [show (fun z => blockδ (c':ℝ) z) = (fun z : Fin 7 → ℝ => blockδ6 (c':ℝ) (fun k => z ((3:Fin 7).succAbove k)))
        from funext (fun z => blockδ_peel3 (c':ℝ) z),
      boxT_peel_spectator (n:=6) 2 (by norm_num) 3 (blockδ6 (c':ℝ)) (blockδ6_meas _)] at hbr
  have hvol0 : volume (Set.Icc (-2:ℝ) 2) ≠ 0 := by
    rw [Real.volume_Icc]; rw [show (2:ℝ) - (-2) = 4 from by norm_num]
    exact (ENNReal.ofReal_pos.2 (by norm_num)).ne'
  by_contra h
  rw [not_lt, top_le_iff] at h
  rw [h, ENNReal.top_mul hvol0] at hbr
  exact (lt_irrefl _ hbr).elim

/-- **δ-cell support containment.** On `chartDomOn {1,2,3} 3`, the `bigbox7` cutoff forces `z ∈ [−2,2]⁷`. -/
theorem pivotδ_support_box (z : Fin 7 → ℝ) (hcd : z ∈ chartDomOn ({1,2,3} : Finset (Fin 7)) 3)
    (hb : pivotBlowupOn ({1,2,3} : Finset (Fin 7)) 3 z ∈ bigbox7) : z ∈ boxT 7 2 := by
  rw [show pivotBlowupOn ({1,2,3} : Finset (Fin 7)) 3 z = ![z 0, z 3 * z 1, z 3 * z 2, z 3, z 4, z 5, z 6]
        from by funext i; fin_cases i <;> simp [pivotBlowupOn, Matrix.cons_val]] at hb
  simp only [bigbox7, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc] at hb
  have h1 : |z 1| ≤ 1 := hcd 1 (by decide) (by decide)
  have h2 : |z 2| ≤ 1 := hcd 2 (by decide) (by decide)
  have b0 : -2 ≤ z 0 ∧ z 0 ≤ 2 := by have := hb 0; simpa using this
  have b3 : -2 ≤ z 3 ∧ z 3 ≤ 2 := by have := hb 3; simpa using this
  have b1 : -2 ≤ z 1 ∧ z 1 ≤ 2 := ⟨by linarith [abs_le.1 h1], by linarith [abs_le.1 h1]⟩
  have b2 : -2 ≤ z 2 ∧ z 2 ≤ 2 := ⟨by linarith [abs_le.1 h2], by linarith [abs_le.1 h2]⟩
  have b4 : -2 ≤ z 4 ∧ z 4 ≤ 2 := by have := hb 4; simpa using this
  have b5 : -2 ≤ z 5 ∧ z 5 ≤ 2 := by have := hb 5; simpa using this
  have b6 : -2 ≤ z 6 ∧ z 6 ≤ 2 := by have := hb 6; simpa using this
  intro i _; simp only [boxT, Set.mem_Icc]
  fin_cases i
  · exact b0
  · exact b1
  · exact b2
  · exact b3
  · exact b4
  · exact b5
  · exact b6

/-- **δ-cell integrand bound** (off `{z3=0}`): the cell integrand `≤` the single pivot-monomial times
`blockδ`, on the box. `|det| = z3²`, `resolvedForm_pivotDelta` gives `z3²·blockδ`, and the `rpow`
algebra factors `|z3²|·|z3²·B|^{−c'} = |z3|^{2−2c'}·B^{−c'}`. -/
theorem deltaCell_integrand_bound (c' : NNReal) (z : Fin 7 → ℝ)
    (hz : z ∈ chartDomOn ({1,2,3} : Finset (Fin 7)) 3 \ pivotZeroOn 3) :
    ENNReal.ofReal |(pivotBlowupOnDeriv ({1,2,3} : Finset (Fin 7)) 3 z).det|
        * bigbox7.indicator (fun w => ENNReal.ofReal (|resolvedForm w| ^ (-(c':ℝ))))
            (pivotBlowupOn ({1,2,3} : Finset (Fin 7)) 3 z)
      ≤ (boxT 7 2).indicator
          (fun z => ENNReal.ofReal (|z 3| ^ (2 - 2*(c':ℝ))) * blockδ (c':ℝ) z) z := by
  rw [show (pivotBlowupOnDeriv ({1,2,3} : Finset (Fin 7)) 3 z).det = (z 3)^2 from by
        rw [pivotBlowupOnDeriv_det _ _ (by decide)];
        norm_num [show ({1,2,3} : Finset (Fin 7)).card = 3 from by decide]]
  by_cases hb : pivotBlowupOn ({1,2,3} : Finset (Fin 7)) 3 z ∈ bigbox7
  · rw [Set.indicator_of_mem hb, Set.indicator_of_mem (pivotδ_support_box z hz.1 hb),
      resolvedForm_pivotDelta]
    have hz3 : z 3 ≠ 0 := hz.2
    have hz3a : (0:ℝ) < |z 3| := abs_pos.2 hz3
    unfold blockδ
    set B := (z 1)^2 + (z 2)^2 + (z 4 * z 1 + z 5)^2 + (z 4 * z 2 + z 6)^2 with hBdef
    have hbpos : (0:ℝ) ≤ B := by rw [hBdef]; positivity
    rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _)]
    apply le_of_eq
    congr 1
    have key : |z 3 ^ 2| * |z 3 ^ 2 * B| ^ (-(c':ℝ)) = |z 3| ^ (2 - 2*(c':ℝ)) * B ^ (-(c':ℝ)) := by
      rw [show |z 3 ^ 2 * B| = |z 3| ^ 2 * B from by rw [abs_mul, abs_pow, abs_of_nonneg hbpos],
          show |z 3 ^ 2| = |z 3| ^ 2 from by rw [abs_pow],
          Real.mul_rpow (by positivity) hbpos]
      have h2e : (|z 3| ^ 2 : ℝ) = |z 3| ^ (2:ℝ) := by rw [← Real.rpow_natCast (|z 3|) 2]; norm_num
      rw [h2e, ← Real.rpow_mul (abs_nonneg _), ← mul_assoc, ← Real.rpow_add hz3a]
      congr 2 <;> push_cast <;> ring
    exact key
  · rw [Set.indicator_of_notMem hb, mul_zero]; exact zero_le _


theorem deltaCell_lt_top (c' : NNReal) (hc' : (c':ℝ) < 3/2) :
    ∫⁻ z in chartDomOn ({1,2,3} : Finset (Fin 7)) 3 \ pivotZeroOn 3,
        ENNReal.ofReal |(pivotBlowupOnDeriv ({1,2,3} : Finset (Fin 7)) 3 z).det|
          * bigbox7.indicator (fun w => ENNReal.ofReal (|resolvedForm w| ^ (-(c':ℝ))))
              (pivotBlowupOn ({1,2,3} : Finset (Fin 7)) 3 z) < ⊤ := by
  have hbm : MeasurableSet (boxT 7 (2:ℝ)) := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have hbound : ∫⁻ z in chartDomOn ({1,2,3} : Finset (Fin 7)) 3 \ pivotZeroOn 3,
        ENNReal.ofReal |(pivotBlowupOnDeriv ({1,2,3} : Finset (Fin 7)) 3 z).det|
          * bigbox7.indicator (fun w => ENNReal.ofReal (|resolvedForm w| ^ (-(c':ℝ))))
              (pivotBlowupOn ({1,2,3} : Finset (Fin 7)) 3 z)
      ≤ ∫⁻ z in boxT 7 (2:ℝ), ENNReal.ofReal (|z 3| ^ (2 - 2*(c':ℝ))) * blockδ (c':ℝ) z := by
    rw [← lintegral_indicator (chartDomOn_diff_measurableSet ({1,2,3} : Finset (Fin 7)) 3)
          (fun z => ENNReal.ofReal |(pivotBlowupOnDeriv ({1,2,3} : Finset (Fin 7)) 3 z).det|
            * bigbox7.indicator (fun w => ENNReal.ofReal (|resolvedForm w| ^ (-(c':ℝ))))
                (pivotBlowupOn ({1,2,3} : Finset (Fin 7)) 3 z)),
        ← lintegral_indicator hbm
          (fun z => ENNReal.ofReal (|z 3| ^ (2 - 2*(c':ℝ))) * blockδ (c':ℝ) z)]
    apply lintegral_mono; intro z
    by_cases hz : z ∈ chartDomOn ({1,2,3} : Finset (Fin 7)) 3 \ pivotZeroOn 3
    · rw [Set.indicator_of_mem hz]; exact deltaCell_integrand_bound c' z hz
    · rw [Set.indicator_of_notMem hz]; exact zero_le _
  refine lt_of_le_of_lt hbound ?_
  rw [show (fun z : Fin 7 → ℝ => ENNReal.ofReal (|z 3| ^ (2 - 2*(c':ℝ))) * blockδ (c':ℝ) z)
        = (fun z : Fin 7 → ℝ => (fun t => ENNReal.ofReal (|t| ^ (2 - 2*(c':ℝ)))) (z 3)
            * blockδ6 (c':ℝ) (fun k => z ((3:Fin 7).succAbove k)))
        from by funext z; simp only; rw [blockδ_peel3]]
  rw [boxT_pivot_peel (n := 6) 2 3 (fun t => ENNReal.ofReal (|t| ^ (2 - 2*(c':ℝ)))) (blockδ6 (c':ℝ))
    (ENNReal.measurable_ofReal.comp (by fun_prop)) (blockδ6_meas _)]
  exact ENNReal.mul_lt_top (abs_rpow_lintegral_Icc_lt_top 2 (by norm_num) (2 - 2*(c':ℝ)) (by linarith))
    (blockδ6_box_lt_top c' hc')

-- ===== assemble resolved_residual via recStep {1,2,3} 1 =====
theorem resolved_residual_lt_top (c' : NNReal) (hc' : (c':ℝ) < 3/2) :
    ∫⁻ w in bigbox7, ENNReal.ofReal (|resolvedForm w| ^ (-(c':ℝ))) < ⊤ := by
  rw [recStep ({1,2,3} : Finset (Fin 7)) 1 (by decide) bigbox7
    (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))
    (fun w => ENNReal.ofReal (|resolvedForm w| ^ (-(c':ℝ))))]
  refine ENNReal.sum_lt_top.2 (fun q hq => ?_)
  fin_cases hq
  · exact Ecell_lt_top c' hc'
  · exact F0cell_lt_top c' hc'
  · exact deltaCell_lt_top c' hc'

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

/-! ## The `≥`-headline (restated downstream, consuming `p0_summand_via_tail`)

`aPivotSummand_lt_top` lives upstream in `Case222CoverGE` (where `p0_summand_via_tail` is not yet in
scope), so the `≥`-headline is restated here. The four step-1 A-pivot summands: `p = 0` is
`p0_summand_via_tail` (the full p=0 chain, now proven); `p ∈ {1,2,3}` are `aPivotSummand_p123_lt_top`
(the A-block coordinate-symmetric variants — the one remaining gap). -/

/-! ## The three non-`a00` A-pivots by coordinate-conjugation symmetry

`myF222 = ‖A·B‖²` is invariant under the coordinate permutations realising the A-block row/column
swaps (`σ1,σ2,σ3` below; `myF222 ∘ σ = myF222` by `ring`). Each such `σ` (with `σ p = 0` and
`σ : Aact ≃ Aact`) CONJUGATES the `p`-pivot blow-up to the `0`-pivot one
(`pivotBlowup_conj`), transports the chart domain / pivot-zero locus / `openBox` cutoff
(`chartDom_preimage_conj`, `pivotZero_preimage_conj`, `openBox_conj`), and preserves the Jacobian
(`det_conj`). So the `p`-summand equals the proven `p = 0` summand (`p0_summand_via_tail`) under the
measure-preserving `x ↦ x∘σ` (`measurePreserving_perm8`). The chart-conjugation soundness was
independently red-teamed (Codex `xhigh`, `threads/codex-chart-conj/`): the blow-up identity holds at
every coordinate slot (pivot / active / spectator), and the spectator B-swaps commute with the
A-block blow-up. -/

-- Fin 8 coordinate permutation is measure-preserving (mirror of measurePreserving_perm for Fin 7).
theorem measurePreserving_perm8 (σ : Fin 8 ≃ Fin 8) :
    MeasurePreserving (fun x : Fin 8 → ℝ => x ∘ σ) (volume : Measure (Fin 8 → ℝ)) volume := by
  have h := volume_measurePreserving_piCongrLeft (fun _ : Fin 8 => ℝ) σ.symm
  convert h using 1
  funext x; funext a
  rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  simp [Function.comp]

-- the three involutive permutations.
noncomputable def σ1 : Fin 8 ≃ Fin 8 := Equiv.ofBijective ![1,0,3,2,6,7,4,5] (by decide)
noncomputable def σ2 : Fin 8 ≃ Fin 8 := Equiv.ofBijective ![2,3,0,1,4,5,6,7] (by decide)
noncomputable def σ3 : Fin 8 ≃ Fin 8 := Equiv.ofBijective ![3,2,1,0,6,7,4,5] (by decide)

-- myF222 ∘ σp = myF222 (ring/decide-safe; verified numerically). σ1 example.
theorem myF222_σ1 (x : Fin 8 → ℝ) : myF222 (x ∘ σ1) = myF222 x := by
  unfold myF222 σ1
  simp only [Function.comp, Equiv.ofBijective_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val, Fin.isValue]
  ring


theorem myF222_σ2 (x : Fin 8 → ℝ) : myF222 (x ∘ σ2) = myF222 x := by
  unfold myF222 σ2
  simp only [Function.comp, Equiv.ofBijective_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val, Fin.isValue]
  ring

theorem myF222_σ3 (x : Fin 8 → ℝ) : myF222 (x ∘ σ3) = myF222 x := by
  unfold myF222 σ3
  simp only [Function.comp, Equiv.ofBijective_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val, Fin.isValue]
  ring

-- UNIFORM conjugation reduction: given σ with the right structure, S(p) = S(0).
-- Hypotheses (Codex-verified): σ p = 0; σ maps Aact→Aact; σ maps Aactᶜ→Aactᶜ; myF222∘σ=myF222.
-- blow-up conjugation: pivotBlowupOn Aact p (x∘σ) = (pivotBlowupOn Aact 0 x)∘σ.
theorem pivotBlowup_conj (σ : Fin 8 ≃ Fin 8) (p : Fin 8) (hσp : σ p = 0)
    (hAact : ∀ i, σ i ∈ Aact ↔ i ∈ Aact) (x : Fin 8 → ℝ) :
    pivotBlowupOn Aact p (x ∘ σ) = (pivotBlowupOn Aact 0 x) ∘ σ := by
  funext i
  unfold pivotBlowupOn
  simp only [Function.comp]
  by_cases hip : i = p
  · subst hip
    rw [if_pos rfl, hσp, if_pos rfl]
  · rw [if_neg hip]
    have hσi0 : σ i ≠ 0 := by rw [← hσp]; exact fun h => hip (σ.injective h)
    rw [if_neg hσi0]
    by_cases hia : i ∈ Aact
    · rw [if_pos hia, if_pos ((hAact i).2 hia), hσp]
    · rw [if_neg hia, if_neg (fun h => hia ((hAact i).1 h))]

-- chartDom preimage under σ: (·∘σ)⁻¹'(chartDomOn Aact p) = chartDomOn Aact 0, given σ-structure.
theorem chartDom_preimage_conj (σ : Fin 8 ≃ Fin 8) (p : Fin 8) (hσp : σ p = 0)
    (hAact : ∀ i, σ i ∈ Aact ↔ i ∈ Aact) :
    (fun x : Fin 8 → ℝ => x ∘ σ) ⁻¹' (chartDomOn Aact p) = chartDomOn Aact 0 := by
  ext x
  simp only [Set.mem_preimage, chartDomOn, Set.mem_setOf_eq, Function.comp]
  constructor
  · intro h j hj hj0
    have hsj : σ (σ.symm j) = j := σ.apply_symm_apply j
    have hmem : σ.symm j ∈ Aact := (hAact (σ.symm j)).1 (by rw [hsj]; exact hj)
    have hne : σ.symm j ≠ p := by intro he; rw [he, hσp] at hsj; exact hj0 hsj.symm
    have := h (σ.symm j) hmem hne
    rwa [hsj] at this
  · intro h j hj hjp
    have hmem : σ j ∈ Aact := (hAact j).2 hj
    have hne : σ j ≠ 0 := by rw [← hσp]; exact fun he => hjp (σ.injective he)
    exact h (σ j) hmem hne

theorem pivotZero_preimage_conj (σ : Fin 8 ≃ Fin 8) (p : Fin 8) (hσp : σ p = 0) :
    (fun x : Fin 8 → ℝ => x ∘ σ) ⁻¹' (pivotZeroOn p) = pivotZeroOn 0 := by
  ext x
  simp only [Set.mem_preimage, pivotZeroOn, Set.mem_setOf_eq, Function.comp, hσp]

theorem openBox_conj (σ : Fin 8 ≃ Fin 8) (y : Fin 8 → ℝ) :
    y ∘ σ ∈ openBox ↔ y ∈ openBox := by
  simp only [openBox, Set.mem_pi, Set.mem_univ, true_implies, Function.comp]
  exact ⟨fun h i => by have := h (σ.symm i); rwa [σ.apply_symm_apply] at this, fun h i => h (σ i)⟩

-- det conjugation: |det(pivotBlowupOnDeriv Aact p (y∘σ))| = |det(pivotBlowupOnDeriv Aact 0 y)|, when σ p = 0.
theorem det_conj (σ : Fin 8 ≃ Fin 8) (p : Fin 8) (hσp : σ p = 0) (hp : p ∈ Aact) (y : Fin 8 → ℝ) :
    |(pivotBlowupOnDeriv Aact p (y ∘ σ)).det| = |(pivotBlowupOnDeriv Aact 0 y).det| := by
  rw [pivotBlowupOnDeriv_det Aact p hp, pivotBlowupOnDeriv_det Aact 0 (by decide)]
  simp only [Function.comp, hσp]

-- THE UNIFORM CONJUGATION REDUCTION: S(p) = S(0), hence < ⊤ via p0_summand_via_tail.
theorem aPivotSummand_conj (c' : NNReal) (hc' : (c':ℝ) < 3/2) (σ : Fin 8 ≃ Fin 8) (p : Fin 8)
    (hp : p ∈ Aact) (hσp : σ p = 0) (hAact : ∀ i, σ i ∈ Aact ↔ i ∈ Aact)
    (hmyF : ∀ x, myF222 (x ∘ σ) = myF222 x) :
    ∫⁻ x in chartDomOn Aact p \ pivotZeroOn p,
        ENNReal.ofReal |(pivotBlowupOnDeriv Aact p x).det|
          * openBox.indicator (fun w => ENNReal.ofReal (|myF222 w| ^ (-(c':ℝ))))
              (pivotBlowupOn Aact p x) < ⊤ := by
  -- (·∘σ) as a measurable equiv (precomposition by the permutation σ).
  let eσ : (Fin 8 → ℝ) ≃ᵐ (Fin 8 → ℝ) :=
    { toFun := fun x => x ∘ σ, invFun := fun x => x ∘ σ.symm,
      left_inv := fun x => by funext i; simp [Function.comp],
      right_inv := fun x => by funext i; simp [Function.comp],
      measurable_toFun := by dsimp; fun_prop, measurable_invFun := by dsimp; fun_prop }
  have hmp : MeasurePreserving eσ volume volume := by
    have := measurePreserving_perm8 σ
    exact this
  have hemb : MeasurableEmbedding eσ := eσ.measurableEmbedding
  set Ip := fun x : Fin 8 → ℝ => ENNReal.ofReal |(pivotBlowupOnDeriv Aact p x).det|
          * openBox.indicator (fun w => ENNReal.ofReal (|myF222 w| ^ (-(c':ℝ))))
              (pivotBlowupOn Aact p x) with hIpdef
  have hDpre : eσ ⁻¹' (chartDomOn Aact p \ pivotZeroOn p)
      = chartDomOn Aact 0 \ pivotZeroOn 0 := by
    show (fun x : Fin 8 → ℝ => x ∘ σ) ⁻¹' (chartDomOn Aact p \ pivotZeroOn p) = _
    rw [Set.preimage_diff, chartDom_preimage_conj σ p hσp hAact, pivotZero_preimage_conj σ p hσp]
  rw [← hmp.setLIntegral_comp_preimage_emb hemb Ip (chartDomOn Aact p \ pivotZeroOn p), hDpre]
  -- now ∫_{D(0)} Ip(eσ y); show Ip(eσ y) = p0integrand c' y, then = p0_summand_via_tail
  refine (setLIntegral_congr_fun (chartDomOn_diff_measurableSet Aact 0)
    (fun y _ => ?_)).trans_lt (p0_summand_via_tail c' hc')
  show Ip (y ∘ σ) = p0integrand c' y
  have hcongr : ∀ y, Ip (y ∘ σ) = p0integrand c' y := by
    intro y
    rw [hIpdef]
    simp only
    rw [det_conj σ p hσp hp y, pivotBlowup_conj σ p hσp hAact y]
    unfold p0integrand
    congr 1
    -- openBox.indicator (|myF222|^{-c'}) ((pivotBlowupOn Aact 0 y)∘σ) = openBox.indicator (...) (pivotBlowupOn Aact 0 y)
    by_cases hmem : (pivotBlowupOn Aact 0 y) ∘ σ ∈ openBox
    · have hmem0 : pivotBlowupOn Aact 0 y ∈ openBox := (openBox_conj σ _).1 hmem
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem0, hmyF]
    · have hmem0 : pivotBlowupOn Aact 0 y ∉ openBox := fun h => hmem ((openBox_conj σ _).2 h)
      rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem0]
  exact hcongr y

-- σ structural facts (decide-checkable for the concrete permutations).
theorem σ1_p : σ1 1 = 0 := by decide
theorem σ2_p : σ2 2 = 0 := by decide
theorem σ3_p : σ3 3 = 0 := by decide
theorem σ1_Aact : ∀ i, σ1 i ∈ Aact ↔ i ∈ Aact := by decide
theorem σ2_Aact : ∀ i, σ2 i ∈ Aact ↔ i ∈ Aact := by decide
theorem σ3_Aact : ∀ i, σ3 i ∈ Aact ↔ i ∈ Aact := by decide

-- the 3-pivot summand finiteness, by conjugation (closing aPivotSummand_p123_lt_top).
theorem aPivotSummand_p123_done (c' : NNReal) (hc' : (c':ℝ) < 3/2) (p : Fin 8)
    (hp : p ∈ ({1,2,3} : Finset (Fin 8))) :
    ∫⁻ x in chartDomOn Aact p \ pivotZeroOn p,
        ENNReal.ofReal |(pivotBlowupOnDeriv Aact p x).det|
          * openBox.indicator (fun y => ENNReal.ofReal (|myF222 y| ^ (-(c':ℝ))))
              (pivotBlowupOn Aact p x) < ⊤ := by
  have hpA : p ∈ Aact := by
    rcases Finset.mem_insert.1 hp with rfl | hp'; · decide
    rcases Finset.mem_insert.1 hp' with rfl | hp''; · decide
    rw [Finset.mem_singleton.1 hp'']; decide
  fin_cases hp
  · exact aPivotSummand_conj c' hc' σ1 1 (by decide) σ1_p σ1_Aact myF222_σ1
  · exact aPivotSummand_conj c' hc' σ2 2 (by decide) σ2_p σ2_Aact myF222_σ2
  · exact aPivotSummand_conj c' hc' σ3 3 (by decide) σ3_p σ3_Aact myF222_σ3

/-- **The three non-`a00` A-pivot summands are finite** (the A-block-symmetric variants of the `p = 0`
chain `p0_summand_via_tail`). The last open piece of the `(2,2,2)` `≥`-direction. -/
theorem aPivotSummand_p123_lt_top (c' : NNReal) (hc' : (c':ℝ) < 3/2) (p : Fin 8)
    (hp : p ∈ ({1,2,3} : Finset (Fin 8))) :
    ∫⁻ x in chartDomOn Aact p \ pivotZeroOn p,
        ENNReal.ofReal |(pivotBlowupOnDeriv Aact p x).det|
          * openBox.indicator (fun y => ENNReal.ofReal (|myF222 y| ^ (-(c':ℝ))))
              (pivotBlowupOn Aact p x) < ⊤ :=
  aPivotSummand_p123_done c' hc' p hp

/-- **The `(2,2,2)` `≥`-direction threshold finiteness** (downstream restatement). For every `c' < 3/2`,
`∫⁻_{openBox} |myF222|^{−c'} < ⊤`: the step-1 `recStep` splits into the four A-pivot summands, `p = 0`
by `p0_summand_via_tail`, `p ∈ {1,2,3}` by `aPivotSummand_p123_lt_top`; `ENNReal.sum_lt_top` closes. -/
theorem myF222_threshold_lt_top' (c' : NNReal) (hc' : (c':ℝ) < 3/2) :
    ∫⁻ x in openBox, ENNReal.ofReal (|myF222 x| ^ (-(c':ℝ))) < ⊤ := by
  rw [recStep Aact 0 (by decide) openBox isOpen_openBox.measurableSet
    (fun y => ENNReal.ofReal (|myF222 y| ^ (-(c':ℝ))))]
  refine ENNReal.sum_lt_top.2 (fun p hp => ?_)
  rcases Finset.mem_insert.1 hp with rfl | hp'
  · exact p0_summand_via_tail c' hc'
  · exact aPivotSummand_p123_lt_top c' hc' p hp'

/-- **The `(2,2,2)` `≥`-direction headline** (downstream restatement). `rlctAtOn myF222 0 ≥ 3/2` via
`rlctAtOn_ge_of_integral_lt` on `openBox ∋ 0` (`myF222_threshold_lt_top'`). -/
theorem rlctAtOn_myF222_ge' : (3 : ℝ≥0∞) / 2 ≤ rlctAtOn myF222 0 := by
  apply rlctAtOn_ge_of_integral_lt myF222 ?_ openBox isOpen_openBox mem_openBox_zero (3 / 2)
  · intro c' hc'
    have h32 : (3 : ℝ≥0∞) / 2 = ENNReal.ofReal (3 / 2) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
    have hc'r : (c' : ℝ) < 3 / 2 := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num)).1
      (by rw [← h32, ENNReal.ofReal_coe_nnreal]; exact hc')
    exact myF222_threshold_lt_top' c' hc'r
  · unfold myF222; fun_prop

/-- **The `(2,2,2)` resolution value (`#80`): `rlctAtOn myF222 0 = 3/2`.** `le_antisymm` of the gated
`≤`-half (`rlctAtOn_myF222_le`, `Case222Resolution` @dd40c45) and the `≥`-half proven here
(`rlctAtOn_myF222_ge'`). Every leaf threshold is `3/2` (`Case222Value`), so this is the `⨅`-value. The
`≥`-half is axiom-clean (`[propext, Classical.choice, Quot.sound]`); the `≤`-half carries the single
permitted S2 citation (`monomial_rlct`, via the box-divergence atom). -/
theorem rlctAtOn_myF222_eq : rlctAtOn myF222 0 = 3 / 2 :=
  le_antisymm rlctAtOn_myF222_le rlctAtOn_myF222_ge'

end DLNFibre.DLN.RLCT
