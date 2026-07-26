import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Meta.Cordon

/-!
# `DLNFibre.Core.Analysis.PolyZeroNull` — the zero-set of a nonzero polynomial is Lebesgue-null

A reusable Core measure-theory brick: the zero-locus of a NONZERO multivariate real polynomial has
Lebesgue measure zero. `volume {x : Fin n → ℝ | MvPolynomial.eval x p = 0} = 0` for `p ≠ 0`.

This is the "codim ≥ 1 ⟹ null" fact that several downstream results need but Mathlib does not carry
directly (Mathlib's `SchwartzZippel` is the combinatorial Finset version, no Lebesgue measure). It
discharges the RLCT-cover's `hnull` ({X=0} = {mult=0} is null — one product entry is a nonzero
polynomial) and is the exact brick the direct-sum RLCT-superadditivity build (G2) also consumes.

## Proof (induction on `n`, the Schwartz–Zippel structure at the measure level)
- **Base `n = 0`:** `p ≠ 0` is a nonzero constant (`isEmptyRingEquiv`), so `eval x p ≠ 0` everywhere
  and the zero set is empty.
- **Step `n+1`:** split off variable `0` with `finSuccEquiv`, giving a univariate polynomial `q`
  over `MvPolynomial (Fin n)`. Transport `volume` through `(Fin (n+1) → ℝ) ≃ᵐ (Fin n → ℝ) × ℝ` (the
  `piFinSuccAbove 0` split, swapped so the last-`n` coords are first) and apply Fubini
  (`measure_prod_null`): for a.e. `s` (the last-`n` coords) the `y`-slice is the root set of the
  nonzero univariate `q.map (eval s)` — FINITE, hence null (`finite_setOf_isRoot`). The bad set of
  `s` (where `q.map (eval s) = 0`) sits inside `{s | eval s q.leadingCoeff = 0}`, null by the
  induction hypothesis (`q.leadingCoeff ≠ 0`).

Design validated decorrelated with Codex xhigh against the v4.29 source
(`threads/reroute-R2-tubecover/codex/polynull-{prompt,answer}.md`).

## Main results
- `volume_setOf_eval_eq_zero` — the headline: `p ≠ 0 → volume {x | eval x p = 0} = 0`.
- `witness_zeroLocus_null` — non-vacuity: a concrete nonzero polynomial has a null zero-set.
-/

open MeasureTheory Polynomial Set

namespace DLNFibre.Core.Analysis

variable {n : ℕ}

/-- The `(s, y) ↦ Fin.cons y s` reassembly is continuous (`y` into slot `0`, `s` into the tail). -/
private theorem continuous_cons_swap :
    Continuous (fun z : (Fin n → ℝ) × ℝ => (Fin.cons z.2 z.1 : Fin (n + 1) → ℝ)) := by
  refine continuous_pi (fun i ↦ ?_)
  refine Fin.cases ?_ ?_ i
  · simpa using continuous_snd
  · intro j
    simpa only [Fin.cons_succ] using (continuous_apply j).comp continuous_fst

/-- The `(s, y)`-form zero set of a polynomial is measurable (`eval` is continuous, zero-locus is
closed). -/
private theorem measurableSet_consZeroSet (p : MvPolynomial (Fin (n + 1)) ℝ) :
    MeasurableSet {z : (Fin n → ℝ) × ℝ | MvPolynomial.eval (Fin.cons z.2 z.1) p = 0} :=
  ((MvPolynomial.continuous_eval p).comp continuous_cons_swap).measurable
    (measurableSet_singleton 0)

/-- The measurable equiv `(Fin (n+1) → ℝ) ≃ᵐ (Fin n → ℝ) × ℝ` splitting off variable `0` (tail
first, so Fubini slices the univariate variable second). -/
private noncomputable def consSplit (n : ℕ) : (Fin (n + 1) → ℝ) ≃ᵐ (Fin n → ℝ) × ℝ :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0).trans MeasurableEquiv.prodComm

private theorem consSplit_apply (g : Fin (n + 1) → ℝ) :
    consSplit n g = (Fin.tail g, g 0) := by
  simp [consSplit, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm, Fin.insertNthEquiv]

/-- `consSplit` is measure-preserving to the product Lebesgue measure `(Fin n → ℝ) × ℝ`. -/
private theorem measurePreserving_consSplit :
    MeasurePreserving (consSplit n) (volume : Measure (Fin (n + 1) → ℝ))
      ((volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ)) := by
  have h1 : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0)
      (volume : Measure (Fin (n + 1) → ℝ))
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
    convert volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0 using 2
  exact Measure.measurePreserving_swap.comp h1

/-- If `q.map (eval s) = 0` then `eval s` kills the leading coefficient (extract coeff at
`natDegree`; evaluation is not injective, so avoid `leadingCoeff_map`). -/
private theorem eval_leadingCoeff_eq_zero_of_map_eq_zero
    (q : Polynomial (MvPolynomial (Fin n) ℝ)) (s : Fin n → ℝ)
    (hzero : Polynomial.map (MvPolynomial.eval s) q = 0) :
    MvPolynomial.eval s q.leadingCoeff = 0 := by
  have hcoeff : (Polynomial.map (MvPolynomial.eval s) q).coeff q.natDegree =
      MvPolynomial.eval s (q.coeff q.natDegree) := Polynomial.coeff_map _ _
  rw [hzero, Polynomial.coeff_zero] at hcoeff
  rw [Polynomial.leadingCoeff]
  exact hcoeff.symm

/-- **The zero-locus of a nonzero polynomial is Lebesgue-null.** For `p : MvPolynomial (Fin n) ℝ`
with `p ≠ 0`, `volume {x : Fin n → ℝ | MvPolynomial.eval x p = 0} = 0`. -/
theorem volume_setOf_eval_eq_zero : ∀ (n : ℕ) {p : MvPolynomial (Fin n) ℝ}, p ≠ 0 →
    volume {x : Fin n → ℝ | MvPolynomial.eval x p = 0} = 0 := by
  intro n
  induction n with
  | zero =>
      intro p hp
      have heval (x : Fin 0 → ℝ) : MvPolynomial.eval x p ≠ 0 := by
        rw [Subsingleton.elim x (fun i ↦ isEmptyElim i), ← MvPolynomial.isEmptyRingEquiv_apply]
        exact (MvPolynomial.isEmptyRingEquiv ℝ (Fin 0)).map_ne_zero_iff.mpr hp
      simp [heval]
  | succ n ih =>
      intro p hp
      set q : Polynomial (MvPolynomial (Fin n) ℝ) := MvPolynomial.finSuccEquiv ℝ n p with hq_def
      have hq : q ≠ 0 := by simpa [hq_def] using hp
      have hlc : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
      set T : Set ((Fin n → ℝ) × ℝ) :=
        {z | MvPolynomial.eval (Fin.cons z.2 z.1) p = 0} with hT_def
      have hTmeas : MeasurableSet T := measurableSet_consZeroSet p
      have hpre : {x : Fin (n + 1) → ℝ | MvPolynomial.eval x p = 0} = consSplit n ⁻¹' T := by
        ext g
        simp only [Set.mem_setOf_eq, Set.mem_preimage, hT_def, consSplit_apply]
        rw [Fin.cons_self_tail]
      rw [hpre, measurePreserving_consSplit.measure_preimage_equiv,
        Measure.measure_prod_null hTmeas]
      have hslice_bad : {s : Fin n → ℝ | volume (Prod.mk s ⁻¹' T) ≠ 0} ⊆
          {s : Fin n → ℝ | MvPolynomial.eval s q.leadingCoeff = 0} := by
        intro s hs
        by_contra hcoeff
        apply hs
        have hqs : Polynomial.map (MvPolynomial.eval s) q ≠ 0 := fun hzero =>
          hcoeff (eval_leadingCoeff_eq_zero_of_map_eq_zero q s hzero)
        have hslice : Prod.mk s ⁻¹' T = {y : ℝ | MvPolynomial.eval (Fin.cons y s) p = 0} := by
          ext y; simp [hT_def]
        have hslice_eq : {y : ℝ | MvPolynomial.eval (Fin.cons y s) p = 0} =
            {y : ℝ | (Polynomial.map (MvPolynomial.eval s) q).IsRoot y} := by
          ext y
          simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def]
          rw [MvPolynomial.eval_eq_eval_mv_eval' s y p]
        rw [hslice, hslice_eq]
        exact (Polynomial.finite_setOf_isRoot hqs).measure_zero volume
      have hslice_bad_null : volume {s : Fin n → ℝ | volume (Prod.mk s ⁻¹' T) ≠ 0} = 0 :=
        measure_mono_null hslice_bad (ih hlc)
      change ∀ᵐ s : Fin n → ℝ, volume (Prod.mk s ⁻¹' T) = 0
      rw [ae_iff]
      exact hslice_bad_null

/-! ## Non-vacuity -/

/-- Non-vacuity: the concrete nonzero polynomial `X 0 · X 1 - 1` on `Fin 2` has a Lebesgue-null
zero-set (the hyperbola `{x₀·x₁ = 1}`). -/
theorem witness_zeroLocus_null :
    volume {x : Fin 2 → ℝ |
      MvPolynomial.eval x (MvPolynomial.X 0 * MvPolynomial.X 1 - 1 :
        MvPolynomial (Fin 2) ℝ) = 0} = 0 := by
  refine volume_setOf_eval_eq_zero 2 ?_
  intro h
  have := congrArg (MvPolynomial.eval (fun _ => (0 : ℝ))) h
  simp at this

-- Forced axiom gate: the poly-null brick + witness rest only on the foundational axioms.
#assert_banked_clean_batch [volume_setOf_eval_eq_zero, witness_zeroLocus_null]

end DLNFibre.Core.Analysis
