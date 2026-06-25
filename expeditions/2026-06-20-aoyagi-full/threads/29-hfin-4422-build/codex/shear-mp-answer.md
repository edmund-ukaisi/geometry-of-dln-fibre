**VERDICT:** option **(A)**. Mathlib v4.29 already has the product-coordinate lemma: `volume_preserving_pi`, backed by `measurePreserving_pi`.

```lean
open MeasureTheory
open scoped BigOperators

-- assumes your `measurePreserving_shearAt` theorem is already in scope
theorem measurePreserving_perRowShear (p n : ℕ) (ell : Fin n) (c : Fin n → ℝ)
    (hc : c ell = 1) :
    MeasurePreserving
      (fun X : Fin p → Fin n → ℝ =>
        fun i k => if k = ell then (∑ k', X i k' * c k') else X i k)
      (volume : Measure (Fin p → Fin n → ℝ)) volume := by
  cases n with
  | zero =>
      exact Fin.elim0 ell
  | succ N =>
      let rowShear : (Fin (N + 1) → ℝ) → (Fin (N + 1) → ℝ) :=
        fun r k => if k = ell then (∑ k', r k' * c k') else r k
      have hrow : MeasurePreserving rowShear
          (volume : Measure (Fin (N + 1) → ℝ)) volume := by
        let g : (Fin N → ℝ) → ℝ :=
          fun y => ∑ k : Fin N, y k * c (ell.succAbove k)
        have hg : Measurable g := by fun_prop
        have h := measurePreserving_shearAt (n := N) ell g hg
        have hfun :
            (fun x : Fin (N + 1) → ℝ =>
                Function.update x ell
                  (x ell + g (fun k => x (ell.succAbove k)))) = rowShear := by
          funext x k
          by_cases hk : k = ell
          · subst k
            rw [Function.update_self]
            dsimp [rowShear, g]
            rw [if_pos rfl]
            rw [Fin.sum_univ_succAbove (fun k' => x k' * c k') ell]
            simp [hc]
          · rw [Function.update_of_ne hk]
            dsimp [rowShear]
            rw [if_neg hk]
        rw [hfun] at h
        exact h
      simpa [rowShear] using
        (volume_preserving_pi (ι := Fin p)
          (f := fun _ : Fin p => rowShear)
          (fun _ : Fin p => hrow))
```

The helper is **in Mathlib**, no custom proof needed:

```lean
measurePreserving_pi :
  (∀ i, MeasurePreserving (f i) (μ i) (ν i)) →
  MeasurePreserving (fun a i => f i (a i)) (Measure.pi μ) (Measure.pi ν)

volume_preserving_pi :
  (∀ i, MeasurePreserving (f i)) →
  MeasurePreserving (fun a i => f i (a i))
```

I verified the lemma names from the local Mathlib v4.29 source. I could not run an elaboration check in this sandbox because non-read Lean execution was blocked.