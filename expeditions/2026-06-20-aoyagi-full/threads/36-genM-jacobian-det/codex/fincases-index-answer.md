    (x 0 • (!![1, x 7] :
        Matrix (Fin (Text M222 tach222 2)) (Fin (Wext M222 2)) ℝ)
      - (!![x 1] :
          Matrix (Fin (Text M222 tach222 2))
            (Fin (Wext M222 1 - Text M222 tach222 2)) ℝ)
        * (!![x 2, x 3] :
          Matrix (Fin (Wext M222 1 - Text M222 tach222 2))
            (Fin (Wext M222 2)) ℝ))
    =
    (!![x 0 - x 1 * x 2, x 0 * x 7 - x 1 * x 3] :
      Matrix (Fin (Text M222 tach222 2)) (Fin (Wext M222 2)) ℝ) := by
  simpa [Text222_2, Wext222_1, Wext222_2] using row0_222_lit x
```

Then in the residual goal:

```lean
  rw [row0_222_dep x]
  dsimp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val]
  rfl
```

Do not use `decide` for the ℝ entry equality. It is the wrong tool. Use `ring`/`ring_nf` for scalar algebra, and use `decide` only for width/proof obligations like `0 < Wext ...`.

The “both sides same form” trick is the best pattern here: prove the arithmetic matrix identity once at literal `Fin 1`/`Fin 2`, transport it by `simpa`/`change` to the dependent widths, then leave the remaining row/column selection to `dsimp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val]` and `rfl`.
tokens used
160,876
Yes. The clean local fix is to normalize the `Fin.mk` indices created by `fin_cases` before asking matrix/vector notation to reduce.

Use this immediately after `fin_cases`:

```lean
  dsimp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val]
```

Then your scalar closer should be:

```lean
  fin_cases i <;> fin_cases j
  all_goals
    dsimp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val]
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply,
      Matrix.of_apply, Fin.sum_univ_one,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      smul_eq_mul]
    ring
```

For this specific row, I would bank the literal-width identity and reuse it:

```lean
private theorem row0_222_lit (x : Fin 8 → ℝ) :
    (x 0 • (!![1, x 7] : Matrix (Fin 1) (Fin 2) ℝ)
      - (!![x 1] : Matrix (Fin 1) (Fin 1) ℝ)
        * (!![x 2, x 3] : Matrix (Fin 1) (Fin 2) ℝ))
    =
    (!![x 0 - x 1 * x 2, x 0 * x 7 - x 1 * x 3] :
      Matrix (Fin 1) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply,
      Fin.sum_univ_one, smul_eq_mul] <;>
    ring

private theorem row0_222_dep (x : Fin 8 → ℝ) :
    (x 0 • (!![1, x 7] :
        Matrix (Fin (Text M222 tach222 2)) (Fin (Wext M222 2)) ℝ)
      - (!![x 1] :
          Matrix (Fin (Text M222 tach222 2))
            (Fin (Wext M222 1 - Text M222 tach222 2)) ℝ)
        * (!![x 2, x 3] :
          Matrix (Fin (Wext M222 1 - Text M222 tach222 2))
            (Fin (Wext M222 2)) ℝ))
    =
    (!![x 0 - x 1 * x 2, x 0 * x 7 - x 1 * x 3] :
      Matrix (Fin (Text M222 tach222 2)) (Fin (Wext M222 2)) ℝ) := by
  simpa [Text222_2, Wext222_1, Wext222_2] using row0_222_lit x
```

Then in the residual goal:

```lean
  rw [row0_222_dep x]
  dsimp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val]
  rfl
```

Do not use `decide` for the ℝ entry equality. It is the wrong tool. Use `ring`/`ring_nf` for scalar algebra, and use `decide` only for width/proof obligations like `0 < Wext ...`.

The “both sides same form” trick is the best pattern here: prove the arithmetic matrix identity once at literal `Fin 1`/`Fin 2`, transport it by `simpa`/`change` to the dependent widths, then leave the remaining row/column selection to `dsimp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val]` and `rfl`.
