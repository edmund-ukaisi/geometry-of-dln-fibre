**1. Verdict**

Your 4-step route is correct. Cleanest variant: define a single per-vertex equiv

```lean
vertexEq k hk :
  Fin r ⊕ Fin (H ⟨k,hk⟩ - r) ≃
    Fin r ⊕ Fin (deepestChainWidth H k - r)
```

with the same composite as `rowEq`/`colEq`. Then derive one `vertexInr k hk`. Now `rowInr s` and `colInr s` are just specializations, and middle cancellation is proof-irrelevance, not a separate theorem.

I would not prove the sum-of-squares directly. The matrix equality plus `sum_sq_reindex_gen` is less work and more reusable.

**2. Block-Diagonal Equiv Idiom**

No direct Mathlib helper for “fixes `inl` implies `sumCongr refl _`” in this checkout. Use `Sum.getRight` + `Equiv.ofBijective`, then prove the decomposition once.

Sketch:

```lean
noncomputable def rightEquivOfFixInl
    (e : α ⊕ β ≃ α ⊕ γ)
    (hL : ∀ a, e (Sum.inl a) = Sum.inl a) : β ≃ γ :=
  Equiv.ofBijective
    (fun b => (e (Sum.inr b)).getRight (by
      cases h : e (Sum.inr b) with
      | inl a =>
          have : Sum.inr b = Sum.inl a := e.injective (by simpa [hL a, h])
          cases this
      | inr c => trivial))
    -- injective/surjective from `e.injective` and `e.surjective`
    sorry
```

Immediately add:

```lean
@[simp] lemma rightEquivOfFixInl_inr :
  e (Sum.inr b) = Sum.inr (rightEquivOfFixInl e hL b) := ...

@[simp] lemma rightEquivOfFixInl_symm_inr :
  e.symm (Sum.inr c) = Sum.inr ((rightEquivOfFixInl e hL).symm c) := ...

lemma eq_sumCongr_right :
  e = Equiv.sumCongr (Equiv.refl α) (rightEquivOfFixInl e hL) := by
  ext x <;> cases x <;> simp [hL]
```

Then the `₂₂` lemma is an `ext` plus:

```lean
simp [Matrix.toBlocks₂₂, Matrix.reindex_apply, eq_sumCongr_right, Equiv.sumCongr_symm]
```

**3. Telescope Statement**

State the prefix theorem:

```lean
theorem blockDiagProd_blockToChainGen_prefix
    (B : BlockParamsGen H r) :
  ∀ k hk,
    blockDiagProd (blockToChainGen H r hr ι hι B) k =
      Matrix.reindex (vertexInr 0 (Nat.zero_lt_succ L)) (vertexInr k hk)
        (prodAux (fun s => H s - r)
          (fun s => (B s).toBlocks₂₂) k hk)
```

Induct on `k`. Base: `submatrix_one_equiv`. Step: unfold `blockDiagProd`, use `prodAux_succ`, `reindex_mul_split_gen`, IH, and the layer lemma

```lean
(blockToChainGen ... B k).toBlocks₂₂ =
  Matrix.reindex (vertexInr k hk') (vertexInr (k+1) hk)
    ((B ⟨k,hkL⟩).toBlocks₂₂)
```

Then specialize `k = L`; unfold `prod`.

**4. Traps**

Proof-irrelevance around `finCongr` is real: isolate it in `vertexEq_inl`.

For `genChainSplit.symm` on pivots, use `← sumSplit_inl` plus `Equiv.symm_apply_apply`.

Do not rely on `deepestChainWidth H L` being defeq to `H (Fin.last L)`; use `H_eq_deepestChainWidth H L (Nat.lt_succ_self L)` under subtraction.

Use `prodAux_succ`; avoid unfolding raw `prodAux` casts.