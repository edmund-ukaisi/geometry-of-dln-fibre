import DLNFibre.DLN.RLCT.Validate.RouteMSJIncidenceAssembly
import DLNFibre.DLN.RLCT.Validate.RouteMSJCorankSurvival
import DLNFibre.DLN.RLCT.Validate.DeepestCoreNonvanishing

set_option linter.style.longLine false

/-!
# `RouteMSJPivotEnergyPos` — the pivot-energy a.e.-positivity input `hEtopae`

**Thread `genm-arch1build` (aoyagi-full Stage 2), the ARCH-1 mint-path.** `shellSpine_le_frontCharge`
(`RouteMSJIncidenceAssembly`) threads a second a.e. hypothesis alongside `hGae`: the pivot energy
`E_top = frobSq (P · Q̃ₚ)` is `> 0` a.e. in the front block `x`, a.e. in `p`. This module discharges it.

Mechanism (arch1probe §Q-B; recon brick D): on `outerDom` (`IsUnit P`), `pivotEnergy_stack_eq` puts the
pivot energy in POLYNOMIAL form `frobSq (P·Q_p + B₁₂·Q_b) = frobSq ([P|B₁₂]·hsQ)`. It vanishes only where a
nonzero linear form in `(P, B₁₂)` does — a null set — as long as `Q_p ≠ 0`. And `Q_p = prod (redChain u M) z`
(the pivot rows of `hsQ`) is `≠ 0` a.e. `z` (the `DeepestCoreNonvanishing` `corePoly` nonvanishing). So
`E_top > 0` a.e.

Core abstract lemma `frobSq_stack_pos_ae`: for `Q_p ≠ 0`, a.e. `(P, B₁₂, C)` has `frobSq (P·Q_p+B₁₂·Q_b) > 0`
(pick a nonzero `Q_p` entry ⟹ a nonzero linear form in `P`'s row 0 ⟹ `ae_matrix_eval_ne_zero`; Fubini in
`(P, B₁₂, C)` via `quasiMeasurePreserving_fst`/`_snd` + `measurePreserving_swap` + `ae_prod_iff_ae_ae`).
Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory MvPolynomial
open scoped ENNReal BigOperators

variable {L : ℕ}

/-! ## The abstract core: `frobSq (P·Qp + B·Qb)` is positive a.e. when `Qp ≠ 0` -/

/-- **A single-block-varying a.e. positivity.** For a fixed `B` and a nonzero-entry column `k₀` of `Qp`,
a.e. `P` has `(P·Qp + B·Qb)` nonzero at `(0, k₀)` — the entry is a nonzero linear form in `P`'s row `0`
(coefficient `Qp l₀ k₀ ≠ 0`), discharged by `ae_matrix_eval_ne_zero`. -/
theorem stackEntry_ne_zero_ae {u b n : ℕ} (hu : 1 ≤ u)
    (Qp : Matrix (Fin u) (Fin n) ℝ) (Qb : Matrix (Fin b) (Fin n) ℝ)
    (l₀ : Fin u) (k₀ : Fin n) (hlk : Qp l₀ k₀ ≠ 0) (B : Matrix (Fin u) (Fin b) ℝ) :
    ∀ᵐ P : Fin u → Fin u → ℝ,
      (Matrix.of P * Qp + Matrix.of B * Qb) ⟨0, hu⟩ k₀ ≠ 0 := by
  classical
  set c := (Matrix.of B * Qb) ⟨0, hu⟩ k₀ with hc
  set Poly : MvPolynomial (Fin u × Fin u) ℝ :=
    (∑ l, MvPolynomial.C (Qp l k₀) * MvPolynomial.X (⟨0, hu⟩, l)) + MvPolynomial.C c with hPoly
  -- the monomial `X (⟨0,hu⟩, l₀)` has coefficient `Qp l₀ k₀ ≠ 0`, so `Poly ≠ 0`
  have hcoeff : MvPolynomial.coeff (Finsupp.single (⟨0, hu⟩, l₀) 1) Poly = Qp l₀ k₀ := by
    rw [hPoly, MvPolynomial.coeff_add]
    have hC : MvPolynomial.coeff (Finsupp.single ((⟨0, hu⟩ : Fin u), l₀) 1) (MvPolynomial.C c) = 0 := by
      rw [MvPolynomial.coeff_C, if_neg]
      exact fun h => by simpa using (Finsupp.single_eq_zero.mp h.symm)
    rw [hC, add_zero, MvPolynomial.coeff_sum]
    rw [Finset.sum_eq_single l₀]
    · rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X', if_pos rfl, mul_one]
    · intro l _ hl
      rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X', if_neg, mul_zero]
      exact fun h => hl (by simpa using (Prod.ext_iff.mp (Finsupp.single_left_injective one_ne_zero h)).2)
    · intro h; exact absurd (Finset.mem_univ _) h
  have hPolyne : Poly ≠ 0 := by
    intro h; rw [h, MvPolynomial.coeff_zero] at hcoeff; exact hlk hcoeff.symm
  -- the eval encoding
  have henc : ∀ P : Fin u → Fin u → ℝ,
      MvPolynomial.eval (fun ij : Fin u × Fin u => P ij.1 ij.2) Poly
        = (Matrix.of P * Qp + Matrix.of B * Qb) ⟨0, hu⟩ k₀ := by
    intro P
    have hL : MvPolynomial.eval (fun ij : Fin u × Fin u => P ij.1 ij.2) Poly
        = (∑ l, P ⟨0, hu⟩ l * Qp l k₀) + c := by
      rw [hPoly, map_add, map_sum, MvPolynomial.eval_C]
      congr 1
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
      ring
    have hR : (Matrix.of P * Qp + Matrix.of B * Qb) ⟨0, hu⟩ k₀
        = (∑ l, P ⟨0, hu⟩ l * Qp l k₀) + c := by
      rw [Matrix.add_apply, Matrix.mul_apply, ← hc]
      simp only [Matrix.of_apply]
    rw [hL, hR]
  filter_upwards [ae_matrix_eval_ne_zero Poly hPolyne] with P hP
  rw [← henc]; exact hP

/-- **The stack pivot energy is positive a.e.** For `Qp ≠ 0` (and `u ≥ 1`), a.e. front block
`x = (P, B₁₂, C)` has `frobSq (P·Qp + B₁₂·Qb) > 0`. Fubini in `(P, B₁₂, C)` reduces to the single-block
a.e. `stackEntry_ne_zero_ae`; the frobenius square dominates one squared entry. -/
theorem frobSq_stack_pos_ae {u a b n : ℕ} (hu : 1 ≤ u)
    (Qp : Matrix (Fin u) (Fin n) ℝ) (Qb : Matrix (Fin b) (Fin n) ℝ) (hQp : Qp ≠ 0) :
    ∀ᵐ x ∂(volume : Measure (SJOuter u a b)),
      0 < frobSq (Matrix.of x.1.1 * Qp + Matrix.of x.1.2 * Qb) := by
  classical
  obtain ⟨l₀, k₀, hlk⟩ : ∃ l k, Qp l k ≠ 0 := by
    by_contra h; push_neg at h; exact hQp (by ext l k; simp [h l k])
  -- the entry function and its measurability
  set E : (Fin u → Fin u → ℝ) × (Fin u → Fin b → ℝ) → ℝ :=
    fun w => (Matrix.of w.1 * Qp + Matrix.of w.2 * Qb) ⟨0, hu⟩ k₀ with hE
  have hEmeas : Measurable E := by
    rw [hE]
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply]
    refine Measurable.add (Finset.measurable_sum _ (fun l _ => ?_))
      (Finset.measurable_sum _ (fun l _ => ?_))
    · exact (((measurable_pi_apply l).comp ((measurable_pi_apply _).comp measurable_fst)).mul
        measurable_const)
    · exact (((measurable_pi_apply l).comp ((measurable_pi_apply _).comp measurable_snd)).mul
        measurable_const)
  -- a.e. over `(B, P)` (then swap to `(P, B)`), via `stackEntry_ne_zero_ae` per `B`
  have hBP : ∀ᵐ w ∂((volume : Measure (Fin u → Fin b → ℝ)).prod
      (volume : Measure (Fin u → Fin u → ℝ))), E (w.2, w.1) ≠ 0 := by
    rw [Measure.ae_prod_iff_ae_ae (by
      have : {w : (Fin u → Fin b → ℝ) × (Fin u → Fin u → ℝ) | E (w.2, w.1) ≠ 0}
          = (fun w => E (w.2, w.1)) ⁻¹' {(0 : ℝ)}ᶜ := rfl
      rw [this]
      exact (hEmeas.comp (measurable_snd.prodMk measurable_fst))
        (measurableSet_singleton _).compl)]
    filter_upwards with B
    filter_upwards [stackEntry_ne_zero_ae hu Qp Qb l₀ k₀ hlk B] with P hP
    exact hP
  -- swap to `(P, B)`
  have hPB : ∀ᵐ w ∂((volume : Measure (Fin u → Fin u → ℝ)).prod
      (volume : Measure (Fin u → Fin b → ℝ))), E w ≠ 0 := by
    filter_upwards [(Measure.measurePreserving_swap).quasiMeasurePreserving.ae hBP] with w hw
    simpa using hw
  -- lift to `SJOuter` (drop `C` via `fst`)
  have hSJ : ∀ᵐ x ∂(volume : Measure (SJOuter u a b)), E x.1 ≠ 0 := by
    have hfst : Measure.QuasiMeasurePreserving (Prod.fst : SJOuter u a b → _)
        (volume : Measure (SJOuter u a b))
        (volume : Measure ((Fin u → Fin u → ℝ) × (Fin u → Fin b → ℝ))) := by
      rw [Measure.volume_eq_prod]
      exact Measure.quasiMeasurePreserving_fst
    exact hfst.ae hPB
  -- the entry squared bounds the frobenius square below
  filter_upwards [hSJ] with x hx
  have hpos : 0 < (E x.1) ^ 2 := by positivity
  refine lt_of_lt_of_le hpos ?_
  calc (E x.1) ^ 2
      = ((Matrix.of x.1.1 * Qp + Matrix.of x.1.2 * Qb) ⟨0, hu⟩ k₀) ^ 2 := by rw [hE]
    _ ≤ ∑ k, ((Matrix.of x.1.1 * Qp + Matrix.of x.1.2 * Qb) ⟨0, hu⟩ k) ^ 2 :=
        Finset.single_le_sum (f := fun k => ((Matrix.of x.1.1 * Qp + Matrix.of x.1.2 * Qb) ⟨0, hu⟩ k) ^ 2)
          (fun k _ => sq_nonneg _) (Finset.mem_univ k₀)
    _ ≤ frobSq (Matrix.of x.1.1 * Qp + Matrix.of x.1.2 * Qb) :=
        Finset.single_le_sum (f := fun i => ∑ k, ((Matrix.of x.1.1 * Qp + Matrix.of x.1.2 * Qb) i k) ^ 2)
          (fun i _ => Finset.sum_nonneg (fun k _ => sq_nonneg _)) (Finset.mem_univ (⟨0, hu⟩ : Fin u))

/-! ## The `hEtopae` input for `shellSpine_le_frontCharge` -/

/-- **The pivot energy is positive a.e. — the `hEtopae` input.** For a good binding cut (`u = t+j`,
`1 ≤ t`, all widths `≥ 1`), a.e. reduced param / corank pair `p` and a.e. front block `x` on `outerDom`,
the pivot energy `E_top = frobSq (P · Q̃ₚ) > 0`. `Q_p = prod (redChain u M) z` (the pivot rows of `hsQ`)
is `≠ 0` a.e. `z` (the `corePoly` nonvanishing), so `frobSq_stack_pos_ae` applies to the polynomial form
`frobSq (P·Q_p + B₁₂·Q_b)`, which equals `E_top` on `outerDom` (`pivotEnergy_stack_eq`, `IsUnit P`). This
is exactly the second a.e. hypothesis `shellSpine_le_frontCharge` threads. -/
theorem deepFactor_hEtopae (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ)
    (ht1 : 1 ≤ t) (hnd : ∀ i, 1 ≤ M i) :
    ∀ᵐ p ∂(volume.restrict
        (paramsBoxM (redChain (t + j) M) 1 ×ˢ matBox (M 1 - (t + j)) (M 2) 1)),
      ∀ᵐ x ∂(volume.restrict (outerDom (t + j) (M 0 - (t + j)) (M 1 - (t + j)) 1)),
        0 < frobSq (Matrix.of x.1.1
          * ((hsQ M (t + j) (deeperFlagZdeep M (t + j)) p.1 p.2).submatrix Sum.inl id
            + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2
                * (hsQ M (t + j) (deeperFlagZdeep M (t + j)) p.1 p.2).submatrix Sum.inr id)) := by
  classical
  set u := t + j with hu_def
  have hu : 1 ≤ u := le_trans ht1 (Nat.le_add_right t j)
  have hposW : ∀ s, 1 ≤ redChain u M s := by
    intro s
    refine Fin.cases ?_ (fun i => ?_) s
    · rw [redChain_zero]; exact hu
    · rw [redChain_succ]; exact hnd _
  -- `prod (redChain u M) z ≠ 0` a.e. `z` (corePoly nonvanishing)
  obtain ⟨Aw, hAw⟩ := dlnLoss_deepest_core_ne_zero_witness (redChain u M) hposW
  have hP_ne : corePoly (redChain u M) ≠ 0 := by
    intro hP0; apply hAw
    have he := eval_corePoly (redChain u M) (paramsEquivFlat (redChain u M) Aw)
    rw [hP0, map_zero] at he
    rw [show (paramsEquivFlat (redChain u M)).symm (paramsEquivFlat (redChain u M) Aw) = Aw
        from by simp] at he
    exact he.symm
  have haeP : ∀ᵐ z ∂(volume : Measure (Params (redChain u M))),
      prod (redChain u M) z ≠ 0 := by
    have hpull := (measurePreserving_paramsEquivFlat (redChain u M)).quasiMeasurePreserving.ae
      (MvPolynomial.ae_eval_ne_zero (corePoly (redChain u M)) hP_ne)
    filter_upwards [hpull] with z hz
    rw [eval_corePoly,
      show (paramsEquivFlat (redChain u M)).symm (paramsEquivFlat (redChain u M) z) = z
        from by simp] at hz
    intro hprod0
    apply hz
    have hdf : dlnLoss (redChain u M) 0 z = frobSq (prod (redChain u M) z) := by
      simp only [dlnLoss, frobSq, Matrix.sub_apply, Matrix.zero_apply, sub_zero]
    rw [hdf, hprod0]; simp [frobSq]
  -- lift to a.e. `p` over the box (`A_cor`-free, via `fst`)
  have hprod_ae : ∀ᵐ p ∂(volume.restrict
      (paramsBoxM (redChain u M) 1 ×ˢ matBox (M 1 - u) (M 2) 1)),
      prod (redChain u M) p.1 ≠ 0 := by
    have hfst : Measure.QuasiMeasurePreserving
        (Prod.fst : Params (redChain u M) × (Fin (M 1 - u) → Fin (M 2) → ℝ) → _)
        (volume.restrict (paramsBoxM (redChain u M) 1 ×ˢ matBox (M 1 - u) (M 2) 1))
        (volume.restrict (paramsBoxM (redChain u M) 1)) := by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
      exact Measure.quasiMeasurePreserving_fst
    exact hfst.ae (ae_restrict_of_ae haeP)
  filter_upwards [hprod_ae] with p hp
  -- `Q_p ≠ 0` (the `Sum.inl` block of `hsQ` is a reindex of `prod`)
  have hsub : (hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inl id
      = (prod (redChain u M) p.1).submatrix (finCongr (redChain_zero u M).symm)
          (finCongr (dropHead_last_eq_redChain_last M u)) := by
    ext i k
    simp only [hsQ, Matrix.submatrix_apply, id_eq, Matrix.fromRows_apply_inl]
  have hQp : (hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inl id ≠ 0 := by
    rw [hsub]
    intro h0
    apply hp
    ext a c
    rw [Matrix.zero_apply]
    have hthis := congrFun (congrFun h0 ((finCongr (redChain_zero u M).symm).symm a))
      ((finCongr (dropHead_last_eq_redChain_last M u)).symm c)
    rw [Matrix.submatrix_apply, Matrix.zero_apply] at hthis
    simpa [Equiv.apply_symm_apply] using hthis
  -- apply the abstract positivity, restrict to `outerDom`, convert the `P⁻¹` form via `pivotEnergy_stack_eq`
  have hae := frobSq_stack_pos_ae (a := M 0 - u) hu
    ((hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inl id)
    ((hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inr id) hQp
  filter_upwards [ae_restrict_of_ae hae,
    ae_restrict_mem (measurableSet_outerDom u (M 0 - u) (M 1 - u) 1)] with x hx hxmem
  convert hx using 2
  exact pivotEnergy_stack_eq x (hsQ M u (deeperFlagZdeep M u) p.1 p.2) hxmem.2.2.2

end DLNFibre.DLN.RLCT
