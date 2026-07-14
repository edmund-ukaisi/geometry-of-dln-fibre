## Q1

Use the repository’s `rawProd` invariant. It is the right-associated fold already related to `prod` by the sorry-free `rawProd_reindex_eq_prod`; this avoids both head truncation and `prod_front_peel`.

First define reversal exactly as:

```lean
def revParams (M : Fin (L + 1) → ℕ) (A : Params M) :
    Params (M ∘ Fin.rev) :=
  fun s ↦
    Matrix.reindex
      (finCongr (congrArg M (Fin.rev_castSucc s).symm))
      (finCongr (congrArg M (Fin.rev_succ s).symm))
      (A (Fin.rev s))ᵀ
```

Here `Fin.rev_castSucc` and `Fin.rev_succ` are both confident; their exact statements are:

```lean
Fin.rev_castSucc s : Fin.rev s.castSucc = (Fin.rev s).succ
Fin.rev_succ s     : Fin.rev s.succ     = (Fin.rev s).castSucc
```

The recommended induction invariant is:

```lean
private def revPrefixIdx {L : ℕ} (k t : ℕ) (ht : t < k)
    (hk : k < L + 1) : Fin L :=
  ⟨k - (t + 1), by omega⟩

theorem rawProd_rev_prefix_eq_transpose
    (H : Fin (L + 1) → ℕ) (A : Params H)
    (k : ℕ) (hk : k < L + 1)
    (W : ℕ → ℕ)
    (a : (t : ℕ) → Matrix (Fin (W t)) (Fin (W (t + 1))) ℝ)
    (hfirst : W 0 = H ⟨k, hk⟩)
    (hlast : W k = H 0)
    (hrow : ∀ t (ht : t < k),
      W t = H (revPrefixIdx k t ht hk).succ)
    (hcol : ∀ t (ht : t < k),
      W (t + 1) = H (revPrefixIdx k t ht hk).castSucc)
    (hlayer : ∀ t (ht : t < k),
      Matrix.reindex
          (finCongr (hrow t ht))
          (finCongr (hcol t ht))
          (a t)
        = (A (revPrefixIdx k t ht hk))ᵀ) :
    Matrix.reindex
        (finCongr hfirst)
        (finCongr hlast)
        (rawProd W a k)
      = (prodAux H A k hk)ᵀ := by
  -- induction on k
```

This says that the right-associated raw product

```text
Aₖ₋₁ᵀ · (Aₖ₋₂ᵀ · … · A₀ᵀ)
```

is the transpose of the left-associated prefix `prodAux H A k`.

The desired final statement is then:

```lean
theorem prod_revParams
    (M : Fin (L + 1) → ℕ) (A : Params M) :
    prod (M ∘ Fin.rev) (revParams M A)
      =
    Matrix.reindex
      (finCongr (congrArg M (Fin.rev_zero L).symm))
      (finCongr (congrArg M (Fin.rev_last L).symm))
      (prod M A)ᵀ := by
  ...
```

`Fin.rev_zero` and `Fin.rev_last` are confident.

Ordered proof steps:

1. Import/reuse repo-local `rawProd`, `rawProd_succ`, and `rawProd_reindex_eq_prod` from `RouteMSuffixBridge`.

2. Prove `rawProd_rev_prefix_eq_transpose` by induction on `k`.

   - Base: rewrite with repo-local `rawProd_zero`, `Matrix.transpose_one` (confident), and normalize equal endpoint reindexes using `finCongr_refl` (confident) plus `Matrix.reindex_refl_refl` (confident). `Matrix.submatrix_one_equiv` (confident) is an alternative.

   - Successor: rewrite the raw fold with `rawProd_succ`, then distribute its endpoint cast with repo-local `reindex_finCongr_mul`.

   - Rewrite the first factor with `hlayer 0`; rewrite the tail with the IH applied to `fun n ↦ W (n+1)` and `fun n ↦ a (n+1)`. The required `revPrefixIdx` equalities are `Fin.ext` plus `omega`.

   - Rewrite the right side with repo-local `prodAux_succ`, then `Matrix.transpose_mul` (confident) and `Matrix.transpose_reindex` (confident).

   - The `e1/e2` casts supplied to `prodAux_succ` are rfl-true. Collapse them at the equivalence level with `finCongr_refl` and `Matrix.reindex_refl_refl`.

   No reassociation lemma is needed in this induction.

3. Instantiate `W` as the reversed widths, extended beyond `L` by clamping:

```lean
let M' := M ∘ Fin.rev
let W : ℕ → ℕ :=
  fun n ↦ M' ⟨min n L, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
```

Define `a n` for `n < L` as `revParams M A ⟨n, _⟩`, reindexed from its natural `M'` widths to `W n`, `W (n+1)`; use `0` when `L ≤ n`. All width equalities are proved with `Nat.min_eq_left`, `Fin.ext`, `Fin.val_rev`, and `omega`. `Fin.val_rev` is confident.

4. Apply `rawProd_reindex_eq_prod` to `M'` and `revParams M A`, giving the reversed `prod`. Apply the new invariant at `k = L`, giving `(prod M A)ᵀ`.

5. Reconcile the two endpoint reindexes using `Matrix.reindex_trans` (confident). If dependent rewriting does not match, use the repository-tested fallback:

```lean
simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix]
congr 1 <;> ext x <;> simp [finCongr]
```

Uncertainty: the clamped dependent definition of `a` may require an explicit `Matrix.reindex` ascription rather than `simpa`. The induction statement and cast orientations above are stable; only that local elaboration detail is untested.

## Q2

Choose Route B. The whole transformation is one permutation of scalar coordinates, so it avoids proving transpose-measure-preservation and dependent `piCongrRight` facts. Also, no equality `flatDim M = flatDim M'` is needed: `piCongrLeft` accepts an equivalence between the two different `Fin` index types.

Let `M' := M ∘ Fin.rev`. Define the slot equivalence

```lean
revFlatIdxEquiv M : FlatIdx M' ≃ FlatIdx M
```

whose forward map is:

```lean
fun q ↦
  let s := q.1.1
  ⟨⟨Fin.rev s,
      Fin.cast (congrArg M (Fin.rev_succ s)) q.2⟩,
    Fin.cast (congrArg M (Fin.rev_castSucc s)) q.1.2⟩
```

Thus `((s,i),j)` goes to `((rev s,j),i)`. The inverse sends `((r,i),j)` to `((rev r,j),i)` with casts:

```lean
have hr :
    M r.succ = M' (Fin.rev r).castSucc := by
  change M r.succ = M (Fin.rev ((Fin.rev r).castSucc))
  rw [Fin.rev_castSucc, Fin.rev_rev]

have hc :
    M r.castSucc = M' (Fin.rev r).succ := by
  change M r.castSucc = M (Fin.rev ((Fin.rev r).succ))
  rw [Fin.rev_succ, Fin.rev_rev]
```

Prove the inverse laws with nested `Sigma.ext` and `Fin.ext`; casts preserve `Fin.val`. This proof is standard but compile-sensitive because of dependent `Sigma` transport.

Now define:

```lean
noncomputable def revCoord (M : Fin (L + 1) → ℕ) :
    Fin (flatDim (M ∘ Fin.rev)) ≃ Fin (flatDim M) :=
  (Fintype.equivFin (FlatIdx (M ∘ Fin.rev))).symm
    |>.trans (revFlatIdxEquiv M)
    |>.trans (Fintype.equivFin (FlatIdx M))

noncomputable def flatRev (M : Fin (L + 1) → ℕ) :
    (Fin (flatDim M) → ℝ) ≃ᵐ
      (Fin (flatDim (M ∘ Fin.rev)) → ℝ) :=
  MeasurableEquiv.piCongrLeft
    (fun _ : Fin (flatDim (M ∘ Fin.rev)) ↦ ℝ)
    (revCoord M).symm

noncomputable def revParamsEquiv (M : Fin (L + 1) → ℕ) :
    Params M ≃ᵐ Params (M ∘ Fin.rev) :=
  (paramsEquivFlat M).trans
    ((flatRev M).trans (paramsEquivFlat (M ∘ Fin.rev)).symm)
```

Measure-preserving factors:

- `volume_measurePreserving_piCongrLeft` — confident.
- `MeasurePreserving.trans` — confident.
- `MeasurePreserving.symm` — confident.
- Repo-local `measurePreserving_paramsEquivFlat`.

Concretely:

```lean
(measurePreserving_paramsEquivFlat M).trans
  ((volume_measurePreserving_piCongrLeft
      (fun _ : Fin (flatDim (M ∘ Fin.rev)) ↦ ℝ)
      (revCoord M).symm).trans
    ((measurePreserving_paramsEquivFlat (M ∘ Fin.rev)).symm _))
```

Prove `revParamsEquiv M A = revParams M A` after applying the injective `paramsEquivFlat M'`, using:

- repo-local `paramsEquivFlat_decodeM`;
- `MeasurableEquiv.trans_apply` — confident;
- `MeasurableEquiv.piCongrLeft_apply_apply` — confident;
- `MeasurableEquiv.apply_symm_apply` / `symm_apply_apply` — confident;
- `Matrix.reindex_apply` — confident.

For box preservation, prove the preimage form directly:

```lean
revParamsEquiv M ⁻¹' paramsBoxM M' 1 = paramsBoxM M 1
```

This is what `setLIntegral_comp_preimage_emb` consumes. Conjugate both sides with repo-local `paramsEquivFlat_preimage_paramsBoxM`; the remaining statement is that `flatRev` preserves `cubeBox`, proved coordinatewise from `MeasurableEquiv.piCongrLeft_apply_apply`. The literal image equality follows by surjectivity, taking the reverse witness `(revParamsEquiv M).symm B`.

For Frobenius invariance, bank:

```lean
frobSq (Matrix.reindex e₁ e₂ X) = frobSq X
frobSq Xᵀ = frobSq X
```

The first follows from `Matrix.reindex_apply` (confident) and `Equiv.sum_comp` (confident); the second from `Finset.sum_comm` (confident). Combine these with `prod_revParams`.

Finally apply `MeasurePreserving.setLIntegral_comp_preimage_emb` (confident), using `MeasurableEquiv.measurableEmbedding` (confident), rewrite the box preimage, and close the integrand equality with `setLIntegral_congr_fun` (confident).