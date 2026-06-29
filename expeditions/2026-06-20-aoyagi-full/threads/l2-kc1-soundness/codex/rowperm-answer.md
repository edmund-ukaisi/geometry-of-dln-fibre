Use the shifted positive-prefix invariant, not a permutation-matrix invariant.

```lean
∀ k (hk : k + 1 < L + 1),
  prodAux H (paramRowFirst H hL R A) (k + 1) hk
    = (prodAux H A (k + 1) hk).submatrix
        (R : Fin (H 0) → Fin (H 0)) id
```

This is the clean version of your `1 ≤ k` invariant: base `k = 0` is exactly `prodAux 1`, where the first layer is read. The “perm-matrix times prefix for all `k`” invariant is false at `k = 0`, as you noticed, so it only reintroduces the same positive-prefix split.

For the propagation step, after rewriting both sides with `prodAux_step` and using the IH, close the matrix identity with:

```lean
simpa using
  (Matrix.submatrix_mul_equiv
    (prodAux H A k hk')
    Mstep
    (R : Fin (H 0) → Fin (H 0))
    (Equiv.refl (Fin (H ⟨k, hk'⟩)))
    (id : Fin (H ⟨k + 1, hk⟩) → Fin (H ⟨k + 1, hk⟩)))
```

or equivalently, in a `rw` style:

```lean
rw [← Matrix.submatrix_mul_equiv
      (prodAux H A k hk') Mstep
      (R : Fin (H 0) → Fin (H 0))
      (Equiv.refl (Fin (H ⟨k, hk'⟩)))
      (id : Fin (H ⟨k + 1, hk⟩) → Fin (H ⟨k + 1, hk⟩)))]
simp
```

The lemma is `Matrix.submatrix_mul_equiv`; choose `e₁ = R`, middle equiv `e₂ = Equiv.refl _`, and `e₃ = id`.

`Function.update` at `firstLayer` is the right definition. The asymmetry is proof-shape only: the last-layer proof uses `prodAux_update_eq_of_le` to show the earlier prefix ignores the update. For first-layer row permutation, every positive prefix contains the updated layer, so that helper is basically not the tool. Use `Function.update_self` in the base `prodAux 1`, then in every later step use `Function.update_of_ne` for the step layer `⟨k, _⟩ ≠ firstLayer hL`, proved by `simp [firstLayer]`/`omega`.

One cast gotcha: mirror the column proof’s `finCongr` transport if needed. A robust row definition uses a lemma like

```lean
H ((firstLayer hL).castSucc) = H 0
```

and conjugates `R` into the first layer’s row width via `finCongr`, just as `paramColPermLast` does for the last layer’s `.succ` width.