Pick **(i)**, but use it as a term proof via `trans`, not `rw`.

```lean
-- after `rw [reindex_finCongr_mul ...]`
set X := Matrix.reindex (finCongr emid) (finCongr ecolk)
  (prodAux (Mtail M) (Atail M A) k (Nat.lt_of_succ_lt hk)) with hX
set Y := Matrix.reindex (finCongr eP1.symm) (finCongr eP2.symm)
  (A (⟨k + 1, Nat.lt_of_succ_lt_succ hk⟩ : Fin (L + 1))) with hY

trans A 0 * (X * Y)
· exact Matrix.mul_assoc (A 0) X Y
·
  -- now split the remaining RHS equality
  congr 1
  -- then split `X * Y = _ * _` as you were doing
```

This avoids `rw` occurrence search entirely. `rw [Matrix.mul_assoc (A 0) X Y]` may also work after the `set`s, but `trans ...; exact Matrix.mul_assoc ...` is the robust form.

For the layer goal, add this local lemma. **VERIFY** only because I could not run Lean here, but it is exactly the `Atail` definition exposed as a rewrite lemma.

```lean
theorem Atail_apply_cast (M : Fin (L + 1 + 1) → ℕ) (A : Params M) (s : Fin L) :
    (Atail M A) s =
      (by
        have e1 : Mtail M s.castSucc = M s.succ.castSucc := by
          simp only [Mtail]; congr 1
        have e2 : Mtail M s.succ = M s.succ.succ := rfl
        rw [e1, e2]
        exact A s.succ :
        Matrix (Fin (Mtail M s.castSucc)) (Fin (Mtail M s.succ)) ℝ) := rfl
```

Then the subgoal closes by collapsing all six reindexes:

```lean
rw [show (finCongr eP1.symm) = Equiv.refl _ from finCongr_refl _,
    show (finCongr eP2.symm) = Equiv.refl _ from finCongr_refl _,
    show (finCongr hb) = Equiv.refl _ from finCongr_refl _,
    show (finCongr ecol) = Equiv.refl _ from finCongr_refl _,
    show (finCongr eT1.symm) = Equiv.refl _ from finCongr_refl _,
    show (finCongr eT2.symm) = Equiv.refl _ from finCongr_refl _]
erw [Matrix.reindex_refl_refl]
erw [Matrix.reindex_refl_refl]
erw [Matrix.reindex_refl_refl]

rw [Atail_apply_cast M A (⟨k, Nat.lt_of_succ_lt_succ hktail⟩ : Fin L)]
rfl
```

If your remaining `Atail` index proof is not syntactically `Nat.lt_of_succ_lt_succ hktail`, replace that one proof with the exact proof appearing in the goal; the lemma is proof-irrelevant at the `Fin` index, but `rw` matching is happier when the displayed term matches.