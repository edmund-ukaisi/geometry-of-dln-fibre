Use the `cases`-the-index-equalities idiom. Do not try to congruence `submatrix` across `HEq` directly.

For the core step:

```lean
have hsub :
    HEq ((A ⟨0, hkL⟩).submatrix Rf id) (Mstep.submatrix Rf id) := by
  cases e1
  cases e2
  cases (eq_of_heq hM)
  rfl
```

If the goal has `A'` on the left:

```lean
rw [hA']
cases e1
cases e2
cases (eq_of_heq hM)
rfl
```

Here `e1/e2` are the `Fin` index equalities used to build `Mstep`, e.g. the row equality between `⟨0, hk0⟩` and `(firstLayerIdx hL).castSucc`, and the column equality between `⟨0+1, hk⟩` and `(firstLayerIdx hL).succ`. After `cases e1; cases e2`, `hM` becomes homogeneous, so `eq_of_heq hM` is available and `submatrix` is just ordinary congruence by substitution.