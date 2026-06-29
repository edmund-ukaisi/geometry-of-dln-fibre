Source-checked names in the local mathlib tree; I could not run Lean in this sandbox.

**1. Product/Submatrix**

Use `Matrix.submatrix_mul`.

```lean
Matrix.submatrix_mul
  (M : Matrix m n α) (N : Matrix n p α)
  (e₁ : l → m) (e₂ : o → n) (e₃ : q → p)
  (he₂ : Function.Bijective e₂) :
  (M * N).submatrix e₁ e₃ =
    M.submatrix e₁ e₂ * N.submatrix e₂ e₃
```

For the row restriction through the product:

```lean
have hrow :
    (layer0 * X).submatrix top0 (id : Fin hlast → Fin hlast)
      = (layer0.submatrix top0 (id : Fin h1 → Fin h1)) * X := by
  simpa using
    (Matrix.submatrix_mul layer0 X top0
      (id : Fin h1 → Fin h1)
      (id : Fin hlast → Fin hlast)
      Function.bijective_id)
```

`Matrix.submatrix_mul_equiv` also works with `(Equiv.refl _)`, but `submatrix_mul` is the right lemma when only the middle map needs bijectivity.

**2. Zero-Tail Collapse**

I would package the crux as a small reusable lemma using `Finset.map (Fin.castLEEmb hrn)`, `Finset.sum_map`, and `Finset.sum_subset`. This avoids block APIs and avoids splitting `Fin n` by an opaque equality.

```lean
private lemma zeroTail_mul_eq_leading_mul_top
    {r n c : ℕ} (hrn : r ≤ n)
    (A : Matrix (Fin r) (Fin n) ℝ) (X : Matrix (Fin n) (Fin c) ℝ)
    (hA_tail : ∀ i (j : Fin n), r ≤ (j : ℕ) → A i j = 0) :
    A * X =
      (A.submatrix (id : Fin r → Fin r) (Fin.castLE hrn)) *
        (X.submatrix (Fin.castLE hrn) (id : Fin c → Fin c)) := by
  classical
  ext i k
  let f : Fin n → ℝ := fun j => A i j * X j k
  change (∑ j : Fin n, f j) = ∑ j : Fin r, f (Fin.castLE hrn j)

  let S : Finset (Fin n) := Finset.univ.map (Fin.castLEEmb hrn)

  have hsmall :
      (∑ j : Fin r, f (Fin.castLE hrn j)) = ∑ j ∈ S, f j := by
    simpa [S] using
      (Finset.sum_map
        (s := (Finset.univ : Finset (Fin r)))
        (e := Fin.castLEEmb hrn)
        (f := f)).symm

  have hbig :
      (∑ j : Fin n, f j) = ∑ j ∈ S, f j := by
    refine (Finset.sum_subset
      (s₁ := S) (s₂ := Finset.univ) (f := f)
      (by intro j _; exact Finset.mem_univ j) ?_).symm
    intro j _ hjnot
    have hjge : r ≤ (j : ℕ) := by
      by_contra hjnge
      have hjlt : (j : ℕ) < r := Nat.lt_of_not_ge hjnge
      apply hjnot
      change j ∈ (Finset.univ : Finset (Fin r)).map (Fin.castLEEmb hrn)
      refine Finset.mem_map.mpr ⟨⟨(j : ℕ), hjlt⟩, by simp, ?_⟩
      ext
      simp
    simp [f, hA_tail i j hjge]

  exact hbig.trans hsmall.symm
```

Call-site shape:

```lean
have hcollapse :
    (layer0.submatrix top0 (id : Fin h1 → Fin h1)) * X = LB * Y := by
  have htail :
      ∀ i (j : Fin h1), r ≤ (j : ℕ) →
        (layer0.submatrix top0 (id : Fin h1 → Fin h1)) i j = 0 := by
    intro i j hj
    simpa using
      deepestPoint_layer0_cols_vanish H r B hB hr hL s0 hL2
        (by simp [s0]) (top0 i) j hj

  simpa [LB, Y, Matrix.submatrix_submatrix] using
    zeroTail_mul_eq_leading_mul_top (hr s0.succ)
      (layer0.submatrix top0 (id : Fin h1 → Fin h1)) X htail
```

If the final `simpa [LB, Y, Matrix.submatrix_submatrix]` hesitates, replace it with `ext i j; rfl`-style identification of the two submatrices; `Matrix.submatrix_apply` is `[simp]`.

**3. Slicker Route**

No genuinely cleaner route. A linear-map version exists:

```lean
topB.mulVecLin = LB.mulVecLin.comp Y.mulVecLin
```

then use `LinearMap.rank_comp_le_left`, but proving that equality is the same zero-tail collapse in disguise. `Matrix.rank_submatrix_le` also does not remove the problem; it will not infer that zero tail columns contribute no rank. The packaged matrix identity above is the best choke point.

Then the rank squeeze is exactly:

```lean
have hge : r ≤ LB.rank := by
  rw [← htop, htopB_factors]
  exact Matrix.rank_mul_le_left LB Y

have hle : LB.rank ≤ r := Matrix.rank_le_height LB
have hLB : LB.rank = r := le_antisymm hle hge
exact isUnit_of_rank_eq_card LB hLB
```