All code below typechecks with pinned Lean/Mathlib v4.29 via `lake env lean`.

## 1. BASE CASE

```lean
| zero =>
    intro p hp
    have heval (x : Fin 0 → ℝ) : MvPolynomial.eval x p ≠ 0 := by
      rw [Subsingleton.elim x (fun i ↦ isEmptyElim i),
        ← MvPolynomial.isEmptyRingEquiv_apply]
      exact (MvPolynomial.isEmptyRingEquiv ℝ (Fin 0)).map_ne_zero_iff.mpr hp
    simp [heval]
```

## 2. TRANSPORT

The required factor order is

```lean
(Fin n → ℝ) × ℝ
```

because `measure_prod_null` fixes the first coordinate and measures the second-coordinate slice. Thus `s` must be first and `y` second.

`piFinSuccAbove 0` initially produces `ℝ × (Fin n → ℝ)`, so `prodComm` is required:

```lean
open MeasureTheory Polynomial

variable {n : ℕ}

private theorem continuous_cons_swap :
    Continuous (fun z : (Fin n → ℝ) × ℝ =>
      (Fin.cons z.2 z.1 : Fin (n + 1) → ℝ)) := by
  refine continuous_pi (fun i ↦ ?_)
  refine Fin.cases ?_ ?_ i
  · simpa using continuous_snd
  · intro j
    simpa only [Fin.cons_succ] using
      (continuous_apply j).comp continuous_fst

private theorem measurableSet_consZeroSet
    (p : MvPolynomial (Fin (n + 1)) ℝ) :
    MeasurableSet {z : (Fin n → ℝ) × ℝ |
      MvPolynomial.eval (Fin.cons z.2 z.1) p = 0} :=
  ((MvPolynomial.continuous_eval p).comp continuous_cons_swap).measurable
    (measurableSet_singleton 0)

private noncomputable def consSplit (n : ℕ) :
    (Fin (n + 1) → ℝ) ≃ᵐ (Fin n → ℝ) × ℝ :=
  (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) ↦ ℝ) 0).trans
    MeasurableEquiv.prodComm

private theorem consSplit_apply (g : Fin (n + 1) → ℝ) :
    consSplit n g = (Fin.tail g, g 0) := by
  simp [consSplit, MeasurableEquiv.piFinSuccAbove,
    MeasurableEquiv.prodComm, Fin.insertNthEquiv]

private theorem measurePreserving_consSplit :
    MeasurePreserving (consSplit n)
      (volume : Measure (Fin (n + 1) → ℝ))
      ((volume : Measure (Fin n → ℝ)).prod
        (volume : Measure ℝ)) := by
  have h1 :
      MeasurePreserving
        (MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (n + 1) ↦ ℝ) 0)
        (volume : Measure (Fin (n + 1) → ℝ))
        ((volume : Measure ℝ).prod
          (volume : Measure (Fin n → ℝ))) := by
    convert volume_preserving_piFinSuccAbove
      (fun _ : Fin (n + 1) ↦ ℝ) 0 using 2
  exact Measure.measurePreserving_swap.comp h1
```

Inside the successor case:

```lean
set q : Polynomial (MvPolynomial (Fin n) ℝ) :=
  MvPolynomial.finSuccEquiv ℝ n p with hq_def
have hq : q ≠ 0 := by simpa [hq_def] using hp
have hlc : q.leadingCoeff ≠ 0 :=
  Polynomial.leadingCoeff_ne_zero.mpr hq

set T : Set ((Fin n → ℝ) × ℝ) :=
  {z | MvPolynomial.eval (Fin.cons z.2 z.1) p = 0} with hT_def
have hTmeas : MeasurableSet T := measurableSet_consZeroSet p

have hpre :
    {x : Fin (n + 1) → ℝ | MvPolynomial.eval x p = 0} =
      consSplit n ⁻¹' T := by
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_preimage, hT_def,
    consSplit_apply]
  rw [Fin.cons_self_tail]

rw [hpre, measurePreserving_consSplit.measure_preimage_equiv,
  Measure.measure_prod_null hTmeas]
```

The goal is now exactly

```lean
(fun s ↦ volume (Prod.mk s ⁻¹' T)) =ᵐ[volume] 0
```

No separate `Measure.prod_swap` rewrite is needed. The exact product-volume lemma is `Measure.volume_eq_prod`, but the proof above targets `.prod` explicitly.

## 3. AE-SLICE

The safe leading-coefficient argument avoids any invalid use of `leadingCoeff_map`:

```lean
private theorem map_eq_zero_imp_eval_leadingCoeff_eq_zero
    (q : Polynomial (MvPolynomial (Fin n) ℝ))
    (s : Fin n → ℝ)
    (hzero : Polynomial.map (MvPolynomial.eval s) q = 0) :
    MvPolynomial.eval s q.leadingCoeff = 0 := by
  have hcoeff :
      (Polynomial.map (MvPolynomial.eval s) q).coeff q.natDegree =
        MvPolynomial.eval s (q.coeff q.natDegree) :=
    Polynomial.coeff_map _ _
  rw [hzero, Polynomial.coeff_zero] at hcoeff
  rw [Polynomial.leadingCoeff]
  exact hcoeff.symm
```

Then:

```lean
have hslice_bad :
    {s : Fin n → ℝ | volume (Prod.mk s ⁻¹' T) ≠ 0} ⊆
      {s : Fin n → ℝ |
        MvPolynomial.eval s q.leadingCoeff = 0} := by
  intro s hs
  by_contra hcoeff
  apply hs

  have hqs : Polynomial.map (MvPolynomial.eval s) q ≠ 0 := by
    intro hzero
    exact hcoeff
      (map_eq_zero_imp_eval_leadingCoeff_eq_zero q s hzero)

  have hslice :
      Prod.mk s ⁻¹' T =
        {y : ℝ | MvPolynomial.eval (Fin.cons y s) p = 0} := by
    ext y
    simp [hT_def]

  have hslice_eq :
      {y : ℝ | MvPolynomial.eval (Fin.cons y s) p = 0} =
        {y : ℝ |
          (Polynomial.map (MvPolynomial.eval s) q).IsRoot y} := by
    ext y
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def]
    rw [MvPolynomial.eval_eq_eval_mv_eval' s y p]

  rw [hslice, hslice_eq]
  exact (Polynomial.finite_setOf_isRoot hqs).measure_zero volume

have hslice_bad_null :
    volume {s : Fin n → ℝ |
      volume (Prod.mk s ⁻¹' T) ≠ 0} = 0 :=
  measure_mono_null hslice_bad (ih hlc)

change ∀ᵐ s : Fin n → ℝ, volume (Prod.mk s ⁻¹' T) = 0
rw [ae_iff]
exact hslice_bad_null
```

## 4. PITFALLS

- `piFinSuccAbove 0` returns `(y,s)`. Fubini needs `(s,y)`, hence `MeasurableEquiv.prodComm` and `Measure.measurePreserving_swap`.
- Annotate all three `volume` types in the transport lemma; otherwise product-volume versus Pi-volume inference becomes fragile.
- Evaluation is not injective, so do not use an unconditional `leadingCoeff_map`. Extract coefficient `q.natDegree` via `Polynomial.coeff_map`.
- `piFinSuccAbove.symm` is expressed using `Fin.insertNthEquiv`; use the checked `consSplit_apply` and `Fin.cons_self_tail` rather than expecting definitional reduction.