**1. Recommendation**

Use a **third route**: Route A’s truncation map, but prove only `InjOn` on `Set.range (rankFn d)` via a `cumul` left-inverse lemma, then use `Equiv.Set.imageOfInjOn`. Do not try to transport through `RealizableDiffArray`; its carrier is polluted by artifacts. The key observation is purely combinatorial: for `i ≤ j`, `cumul` only sums entries `(a,b)` with `a ≤ b`, so it cannot see the truncation. Then add the literal predicate to the image subtype by `Equiv.subtypeEquivRight`.

**2. Recommended Type**

```lean
def IsLiteralKostantArray {N : ℕ} (m : SuppArray (N : ℤ) ℤ) : Prop :=
  (∀ i j : ℤ, j < i → m.1 i j = 0) ∧
  (∀ i j : ℤ, 0 ≤ m.1 i j)

noncomputable def kostantArrayOfRank {N : ℕ}
    (r : Fin (N + 1) → Fin (N + 1) → ℕ) :
    SuppArray (N : ℤ) ℤ :=
  ⟨fun i j ↦ if i ≤ j then (diffArrayOfRank r).1 i j else 0, by
    -- supported: use support of `diffArrayOfRank r` in the `i ≤ j` branch
    aesop⟩

abbrev KostantPartition {k : Type u} [Field k] {N : ℕ}
    (d : Fin (N + 1) → ℕ) :=
  { m : SuppArray (N : ℤ) ℤ //
      m ∈ kostantArrayOfRank (N := N) '' Set.range (rankFn (k := k) d) ∧
      IsLiteralKostantArray (N := N) m }
```

**3. Lemmas / Combinators**

- `kostantArrayOfRank_apply_of_le`, `kostantArrayOfRank_apply_of_gt`: **trivial**.
  ```lean
  (kostantArrayOfRank r).1 i j = (diffArrayOfRank r).1 i j
  (kostantArrayOfRank r).1 i j = 0
  ```

- `cumul_trunc_eq_cumul_of_le`: **moderate**, pure `Finset.sum_congr` + `omega`.
  ```lean
  theorem cumul_trunc_eq_cumul_of_le
      (f : ℤ → ℤ → ℤ) {i j : ℤ} (hij : i ≤ j) :
      cumul (N : ℤ) (fun a b ↦ if a ≤ b then f a b else 0) i j
        = cumul (N : ℤ) f i j
  ```
  Reason: in the sum, `a ∈ Icc 0 i`, `b ∈ Icc j N`, and `i ≤ j`, hence `a ≤ b`.

- `cumul_kostantArrayOfRank_apply_fin_of_le`: **moderate**, uses previous lemma, `cumul_diff`, `embedRank_apply_fin`.
  ```lean
  theorem cumul_kostantArrayOfRank_apply_fin_of_le
      (r : Fin (N + 1) → Fin (N + 1) → ℕ)
      {i j : Fin (N + 1)} (hij : i ≤ j) :
      cumul (N : ℤ) (kostantArrayOfRank r).1 (i : ℤ) (j : ℤ)
        = (r i j : ℤ)
  ```

- `kostantArrayOfRank_injOn_range`: **moderate**, but cheap after the previous lemma.
  ```lean
  theorem kostantArrayOfRank_injOn_range (d : Fin (N + 1) → ℕ) :
      Set.InjOn (kostantArrayOfRank (N := N))
        (Set.range (rankFn (k := k) d))
  ```
  For `i ≤ j`, compare `cumul` of equal arrays. For `¬ i ≤ j`, both realized rank functions are `0`.

- `barMult_nonneg`, `barMult_eq_zero_of_gt`: **trivial/moderate**, by `Finset.sum_nonneg`, `singleDelta`, `omega`.

- `isLiteralKostantArray_of_mem_image`: **moderate/hardest**, uses `exists_cumul_barMult`.
  ```lean
  theorem isLiteralKostantArray_of_mem_image
      {m : SuppArray (N : ℤ) ℤ}
      (hm : m ∈ kostantArrayOfRank (N := N) '' Set.range (rankFn (k := k) d)) :
      IsLiteralKostantArray (N := N) m
  ```

- Equiv combinators:
  - `Equiv.Set.imageOfInjOn`: **confirmed in v4.29**.
  - `Equiv.Set.image`: **confirmed**, but needs global `Injective`; do not use here.
  - `Equiv.subtypeEquivRight`: **confirmed**.
  - `.trans`: **confirmed**.

Skeleton:
```lean
noncomputable def rankKostantPartitionEquiv (d : Fin (N + 1) → ℕ) :
    RealizableRank (k := k) d ≃ KostantPartition (k := k) d :=
  (Equiv.Set.imageOfInjOn
      (kostantArrayOfRank (N := N))
      (Set.range (rankFn (k := k) d))
      (kostantArrayOfRank_injOn_range (k := k) d)).trans
    (Equiv.subtypeEquivRight (fun m ↦
      ⟨fun hm ↦ ⟨hm, isLiteralKostantArray_of_mem_image (d := d) hm⟩,
       fun hm ↦ hm.1⟩))

noncomputable def orbitKostantPartitionEquiv (d : Fin (N + 1) → ℕ) :
    Quotient (orbitSetoid (k := k) d) ≃ KostantPartition (k := k) d :=
  (orbitKostantEquiv d).trans (rankKostantPartitionEquiv (k := k) d)
```

**4. Hardest Obligation**

The hardest obligation is `isLiteralKostantArray_of_mem_image`, specifically nonnegativity. Discharge it by taking `m = kostantArrayOfRank (rankFn d A)`, applying `exists_cumul_barMult A`, and proving on `i ≤ j` that the truncated diff equals that `barMult`; below the diagonal it is `0` by definition. The equality is a four-term `diff_apply` proof using that `embedRank (rankFn d A)` agrees with `cumul N (barMult ...)` on all upper-triangular terms that the four-term difference reads.