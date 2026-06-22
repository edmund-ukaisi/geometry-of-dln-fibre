import Mathlib

/-!
# The zero set of a nonzero multivariate real polynomial is Lebesgue-null

A nonzero polynomial in `n` real variables vanishes only on a set of Lebesgue
measure zero; equivalently, it is almost-everywhere nonzero. This is a
network-free measure-theory building block (originally drafted for the
Aoyagi-full RLCT expedition; kept as a reusable Core lemma).

## Main results

* `MvPolynomial.volume_zeroSet_eq_zero` — for `p ≠ 0`, the zero set
  `{x : Fin n → ℝ | eval x p = 0}` has `volume` zero.
* `MvPolynomial.ae_eval_ne_zero` — the a.e. corollary: `∀ᵐ x, eval x p ≠ 0`.

## Strategy

Induction on the number of variables `n`, using the standard product Lebesgue
measure `volume` on `Fin n → ℝ` (`MeasureSpace` via `Measure.pi`).

* `n = 0` : a nonzero constant polynomial never vanishes, so its zero set is
  empty.
* `n + 1` : split off the **first** variable. Transport `volume` along the
  measure-preserving equivalence `(Fin (n+1) → ℝ) ≃ᵐ (Fin n → ℝ) × ℝ`
  (`piFinSuccAbove 0` then `prodComm`). In the transported coordinates the zero
  set is `{(s, y) | eval (Fin.cons y s) p = 0}`. View `p` as a univariate
  polynomial `q := finSuccEquiv ℝ n p` over `MvPolynomial (Fin n) ℝ`; its
  leading coefficient `c := q.leadingCoeff` is nonzero, so by the inductive
  hypothesis `{s | eval s c = 0}` is null; for every `s` off that null set the
  slice `p(s, ·)` is a nonzero univariate real polynomial, whose root set is
  finite (`Polynomial.finite_setOf_isRoot`) hence null. Fubini
  (`measure_prod_null_of_ae_null`) closes the step.
-/

open MeasureTheory Polynomial

namespace MvPolynomial

variable {n : ℕ}

/-- The zero set of a multivariate polynomial is measurable: it is the preimage
of `{0}` under the continuous evaluation map. -/
theorem measurableSet_zeroSet (p : MvPolynomial (Fin n) ℝ) :
    MeasurableSet {x : Fin n → ℝ | MvPolynomial.eval x p = 0} :=
  ((MvPolynomial.continuous_eval p).measurable (measurableSet_singleton 0))

/-- The map `(s, y) ↦ Fin.cons y s` is continuous. -/
private theorem continuous_cons_swap :
    Continuous (fun z : (Fin n → ℝ) × ℝ => (Fin.cons z.2 z.1 : Fin (n + 1) → ℝ)) := by
  refine continuous_pi (fun i => ?_)
  refine Fin.cases ?_ ?_ i
  · simpa using continuous_snd
  · intro j; simpa only [Fin.cons_succ] using (continuous_apply j).comp continuous_fst

/-- Measurability of the zero set in the transported `(Fin n → ℝ) × ℝ` coordinates. -/
private theorem measurableSet_consZeroSet (p : MvPolynomial (Fin (n + 1)) ℝ) :
    MeasurableSet {z : (Fin n → ℝ) × ℝ | MvPolynomial.eval (Fin.cons z.2 z.1) p = 0} :=
  ((MvPolynomial.continuous_eval p).comp continuous_cons_swap).measurable
    (measurableSet_singleton 0)

/-- The measure-preserving equivalence `(Fin (n+1) → ℝ) ≃ᵐ (Fin n → ℝ) × ℝ`
splitting off the first coordinate: `g ↦ (Fin.tail g, g 0)`. Carries `volume`
to the product `volume.prod volume`. -/
private noncomputable def consSplit (n : ℕ) :
    (Fin (n + 1) → ℝ) ≃ᵐ (Fin n → ℝ) × ℝ :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).trans MeasurableEquiv.prodComm

private theorem consSplit_apply (g : Fin (n + 1) → ℝ) :
    consSplit n g = (Fin.tail g, g 0) := by
  simp [consSplit, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm,
    Fin.insertNthEquiv]

private theorem measurePreserving_consSplit :
    MeasurePreserving (consSplit n) (volume : Measure (Fin (n + 1) → ℝ))
      ((volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ)) := by
  have h1 : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)
      (volume : Measure (Fin (n + 1) → ℝ))
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
    convert volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0 using 2
  exact Measure.measurePreserving_swap.comp h1

/-- A univariate polynomial whose `natDegree`-coefficient is sent to a nonzero
value by a ring map stays nonzero after `map`. -/
private theorem map_ne_zero_of_eval_leadingCoeff_ne_zero
    (q : Polynomial (MvPolynomial (Fin n) ℝ)) (s : Fin n → ℝ)
    (hs : MvPolynomial.eval s q.leadingCoeff ≠ 0) :
    Polynomial.map (MvPolynomial.eval s) q ≠ 0 := by
  intro hzero
  apply hs
  have hcoeff : (Polynomial.map (MvPolynomial.eval s) q).coeff q.natDegree
      = MvPolynomial.eval s (q.coeff q.natDegree) := Polynomial.coeff_map _ _
  rw [hzero, Polynomial.coeff_zero] at hcoeff
  rw [Polynomial.leadingCoeff]
  exact hcoeff.symm

/-- **The zero set of a nonzero multivariate real polynomial has Lebesgue
measure zero.** Here `volume` is the product Lebesgue measure on `Fin n → ℝ`. -/
theorem volume_zeroSet_eq_zero :
    ∀ {n : ℕ} (p : MvPolynomial (Fin n) ℝ), p ≠ 0 →
      volume {x : Fin n → ℝ | MvPolynomial.eval x p = 0} = 0
  | 0, p, hp => by
      -- A nonzero polynomial in no variables is a nonzero constant: its zero set is empty
      -- (evaluation at the empty point is injective).
      have hempty : {x : Fin 0 → ℝ | MvPolynomial.eval x p = 0} = ∅ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        have hinj : Function.Injective (MvPolynomial.eval x : MvPolynomial (Fin 0) ℝ → ℝ) := by
          rw [show (MvPolynomial.eval x : MvPolynomial (Fin 0) ℝ → ℝ) = aeval x from rfl,
            MvPolynomial.aeval_injective_iff_of_isEmpty]
          exact fun _ _ h => h
        exact fun h => hp (hinj (by simpa using h))
      rw [hempty]; simp
  | n + 1, p, hp => by
      -- View `p` as a univariate polynomial over `MvPolynomial (Fin n) ℝ`.
      set q : Polynomial (MvPolynomial (Fin n) ℝ) := MvPolynomial.finSuccEquiv ℝ n p with hq_def
      have hq : q ≠ 0 := by simpa [hq_def] using hp
      set c : MvPolynomial (Fin n) ℝ := q.leadingCoeff with hc_def
      have hc : c ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
      -- The transported zero set.
      set T : Set ((Fin n → ℝ) × ℝ) :=
        {z : (Fin n → ℝ) × ℝ | MvPolynomial.eval (Fin.cons z.2 z.1) p = 0} with hT_def
      have hTmeas : MeasurableSet T := measurableSet_consZeroSet p
      -- The original zero set is the preimage of `T` under the split.
      have hpre : {x : Fin (n + 1) → ℝ | MvPolynomial.eval x p = 0} = consSplit n ⁻¹' T := by
        ext g
        simp only [Set.mem_setOf_eq, Set.mem_preimage, hT_def, consSplit_apply]
        rw [Fin.cons_self_tail]
      rw [hpre, (measurePreserving_consSplit).measure_preimage_equiv]
      -- Fubini: slice over `s`. Off the (null, by IH) zero set of `c`, the slice is finite.
      refine Measure.measure_prod_null_of_ae_null hTmeas ?_
      have hIH : volume {s : Fin n → ℝ | MvPolynomial.eval s c = 0} = 0 :=
        volume_zeroSet_eq_zero c hc
      have hae : ∀ᵐ s : Fin n → ℝ, MvPolynomial.eval s c ≠ 0 := by
        rw [ae_iff]; simpa using hIH
      filter_upwards [hae] with s hs
      -- The slice `{y | (s, y) ∈ T}` is the root set of the nonzero univariate
      -- polynomial `q.map (eval s)`, which is finite, hence null.
      have hslice : (Prod.mk s ⁻¹' T) = {y : ℝ | MvPolynomial.eval (Fin.cons y s) p = 0} := by
        ext y; simp [hT_def]
      have hqs : Polynomial.map (MvPolynomial.eval s) q ≠ 0 :=
        map_ne_zero_of_eval_leadingCoeff_ne_zero q s (by rwa [← hc_def])
      have hslice_eq : {y : ℝ | MvPolynomial.eval (Fin.cons y s) p = 0}
          = {y : ℝ | (Polynomial.map (MvPolynomial.eval s) q).IsRoot y} := by
        ext y
        simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def]
        rw [MvPolynomial.eval_eq_eval_mv_eval' s y p]
      rw [Pi.zero_apply, hslice, hslice_eq]
      exact (Polynomial.finite_setOf_isRoot hqs).measure_zero volume

/-- A nonzero multivariate real polynomial is almost-everywhere nonzero
(w.r.t. the product Lebesgue measure on `Fin n → ℝ`). -/
theorem ae_eval_ne_zero (p : MvPolynomial (Fin n) ℝ) (hp : p ≠ 0) :
    ∀ᵐ x : Fin n → ℝ, MvPolynomial.eval x p ≠ 0 := by
  rw [ae_iff]
  simpa using volume_zeroSet_eq_zero p hp

end MvPolynomial
