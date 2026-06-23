I would use **nested `Finset.sum_eq_single_of_mem` on `i` and `v`**.

This is least fragile because the triangular dependencies stay local. For `i = 1`, membership is just `1 ∈ Icc 1 L`. For `v = L`, membership is proved inside the current `j` branch from `j ∈ Icc u L`, so `L ∈ Icc j L`. No `j/v` swap is needed.

**1. Quadruple Collapse**

Use:

- `Finset.sum_eq_single_of_mem` — **confident**
  ```lean
  Finset.sum_eq_single_of_mem a ha hzero
  ```
  generated additive signature:
  ```lean
  (a : ι) → a ∈ s →
    (∀ b ∈ s, b ≠ a → f b = 0) →
    ∑ x ∈ s, f x = f a
  ```

- `Finset.mem_Icc` — **confident**
  ```lean
  x ∈ Finset.Icc a b ↔ a ≤ x ∧ x ≤ b
  ```

Sketch:

```lean
by_cases hL : (1 : ℤ) ≤ (L : ℤ)
· rw [Finset.sum_eq_single_of_mem (a := (1 : ℤ))
      (h := by exact Finset.mem_Icc.2 ⟨le_rfl, hL⟩)]
  · -- remaining i = 1 body
    simp only [sub_self] -- or norm_num for `1 - 1`
    -- enter u,j and kill v-sum at v = L
  · intro i hi hine
    apply Finset.sum_eq_zero
    intro u hu
    apply Finset.sum_eq_zero
    intro j hj
    apply Finset.sum_eq_zero
    intro v hv
    -- use support-zero for m (i-1) (j-1)
    -- hi,hj,hine imply i-1 ≠ 0 and j-1 ≠ L
    have : m (i - 1) (j - 1) = 0 := by
      apply h_support_zero
      -- all index contradictions by omega
      omega
    simp [this]
· -- degenerate L < 1 branch
  rw [Finset.Icc_eq_empty_of_lt (lt_of_not_ge hL)]
  simp
```

Then inside the `u,j` sums:

```lean
rw [Finset.sum_eq_single_of_mem (a := (L : ℤ))
    (h := by
      exact Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hj).2, le_rfl⟩)]
· -- term at v = L
  rw [h_top_row, h_right_col]
  -- m 0 (j-1) = ρ (j-1) - ρ j
  -- m u L     = q u - q (u-1)
· intro v hv hvne
  have : m u v = 0 := by
    apply h_support_zero
    -- u ≥ 1 kills top row; hvne kills right column
    omega
  simp [this]
```

To orient the surviving triangle as `j` outer, prove one local lemma:

- `Finset.sum_sigma'` — **confident**
- `Finset.sum_nbij'` — **confident**
- `Finset.mem_sigma` — **confident**

```lean
lemma sum_Icc_Icc_comm_int {A : Type*} [AddCommMonoid A]
    (L : ℤ) (F : ℤ → ℤ → A) :
    (∑ u ∈ Finset.Icc (1 : ℤ) L,
        ∑ j ∈ Finset.Icc u L, F u j)
      =
    ∑ j ∈ Finset.Icc (1 : ℤ) L,
        ∑ u ∈ Finset.Icc (1 : ℤ) j, F u j := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij'
    (fun x ↦ ⟨x.2, x.1⟩)
    (fun x ↦ ⟨x.2, x.1⟩)
    ?_ ?_ (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) <;>
  simp only [Finset.mem_sigma, Finset.mem_Icc, Sigma.forall] <;>
  omega
```

Mathlib has `Finset.sum_Ico_Ico_comm` — **confident** — but only for `ℕ`/`Ico`, so for `ℤ`/`Icc` I would use the local lemma above.

**2. j/v Reordering**

No swap needed.

Use `Finset.sum_eq_single_of_mem` inside the `j` sum. Since `j ∈ Icc u L`, `L ∈ Icc j L` is immediate:

```lean
have hLmem : (L : ℤ) ∈ Finset.Icc j (L : ℤ) := by
  exact Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hj).2, le_rfl⟩

rw [Finset.sum_eq_single_of_mem (a := (L : ℤ)) hLmem]
```

So `Finset.sum_sigma'`, `Finset.sum_comm`, or `sum_comm'` are not needed for `j/v`.

**3. Inner Telescope**

Use range telescoping after shifting `Icc 1 j` to a range.

- `Finset.sum_range_sub` — **confident**
  ```lean
  Finset.sum_range_sub (fun n : ℕ => Q n) N :
    (∑ n ∈ Finset.range N, Q (n + 1) - Q n) = Q N - Q 0
  ```

- `Int.Icc_eq_finset_map` — **confident**
- `Finset.sum_map` — **confident**
- `Int.toNat_of_nonneg` — **confident**

Sketch:

```lean
lemma telescope_Icc_int (q : ℤ → ℤ) {j : ℤ} (hj : 0 ≤ j) :
    (∑ u ∈ Finset.Icc (1 : ℤ) j, q u - q (u - 1)) = q j - q 0 := by
  rw [Int.Icc_eq_finset_map (1 : ℤ) j, Finset.sum_map]
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply]
  -- now a range over `j.toNat`, summand is q (n+1) - q n
  simpa [Int.toNat_of_nonneg hj] using
    Finset.sum_range_sub (fun n : ℕ => q ((n : ℤ))) j.toNat
```

`Finset.sum_range_succ_sub_sum` — **verify**, not needed here. The direct telescope is `Finset.sum_range_sub`.

**4. ℤ-Icc to `Fin L`**

Prefer:

- `Int.Icc_eq_finset_map` — **confident**
- `Finset.sum_map` — **confident**
- `Fin.sum_univ_eq_sum_range` — **confident**

This avoids a fragile hand-written `sum_bij`.

For `L : ℕ`:

```lean
lemma sum_Icc_one_natCast_eq_fin
    (f : ℤ → ℤ) :
    (∑ j ∈ Finset.Icc (1 : ℤ) (L : ℤ), f j)
      =
    ∑ k : Fin L, f (((k : ℕ) : ℤ) + 1) := by
  rw [Int.Icc_eq_finset_map (1 : ℤ) (L : ℤ), Finset.sum_map]
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply]
  simp
  rw [← Fin.sum_univ_eq_sum_range
    (fun n : ℕ => f ((n : ℤ) + 1)) L]
```

Then finish by `Finset.sum_congr` / `congr` on the `Fin L` summand and your definitions:
`ρ k - ρ (k+1) = tPrev M T k - T k`, and
`q (k+1) = M k.succ - T k`.