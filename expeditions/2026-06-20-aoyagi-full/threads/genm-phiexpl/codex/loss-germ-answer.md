Use the **germ statement as the main deliverable**, but do **not** leave `F` as a completely anonymous existential.

Cleanest shape:

```lean
noncomputable def schurReadoutF_L2 ... : (Fin (flatDim H) → ℝ) → ℝ := ...
```

then prove a pivot-parametric theorem:

```lean
theorem schur_loss_germ_L2_at_pivot ... :
  ∃ Φ f',
    ContDiff ℝ 2 Φ ∧
    HasFDerivAt Φ (f' : _ →L[ℝ] _) 0 ∧
    Φ 0 = 0 ∧
    lossFlatShift H B v =ᶠ[𝓝 0]
      fun w => schurReadoutF_L2 ... (Φ w)
```

and a thin wrapper using `exists_common_pivot_L2_at`. Add the `dln_hchart_flat` consequence as a **separate corollary**, not inside the germ theorem. It is one line and keeping it separate preserves a reusable algebraic germ statement.

For `F`, keep the **single residual Frobenius sum** for this tide:

```lean
∑ a, ∑ b,
  ((recoverProduct (b x + C) - B.submatrix sI sJ) a b)^2
```

Do the `(∑ regular²) + (∑ ₂₂²)` split later. Splitting now will force extra `fromBlocks` sum bookkeeping into the germ proof before it pays rent.

`recoverProduct` is the right route. Prove one isolated lemma:

```lean
recoverProduct_schurChartRaw
  (P : BlockParamsL2 H r)
  (hX : ...)
  (hM11 : ...) :
  recoverProduct (schurChartRaw H r P) = P.1 * P.2
```

Inside that lemma, instantiate `Invertible` from det hypotheses once, rewrite `⁻¹` to `⅟` using `Matrix.invOf_eq_nonsing_inv`, use `fromBlocks_multiply` for the regular blocks, and `schur_product_factor` only for the `₂₂` block. Do not spread the `⅟`/`⁻¹` juggling through the germ proof.

For the reindex product, prefer proving a helper first:

```lean
(blockFlatEquiv_L2 ... x).1 * (blockFlatEquiv_L2 ... x).2
  = (prod H ((paramsEquivFlatLinear H).symm x)).submatrix sI sJ
```

`Matrix.reindex_apply` is `rfl`, and `Equiv.symm_symm` should clean the `(sumSplit K).symm.symm` issue. `Matrix.reindexLinearEquiv_mul` may match the construction of `b` even better than raw `submatrix_mul_equiv`.

Flat bridge: set

```lean
flatv := (paramsEquivFlat H) v
P₀ := b flatv
```

and prove once:

```lean
(paramsEquivFlatLinear H).symm flatv = v
```

by `paramsEquivFlatLinear_symm_coe` and `symm_apply_apply`. Then `b w + P₀ = b (w + flatv)` is just `map_add`.

`H (Fin.last 2)` vs `H 2` should not be a serious wall in this file, but normalize locally to `H 2` for block work and let `prod_two_factor_L2` bridge back to the loss.

Single biggest risk: **an opaque existential `F`**. The next tide needs to rewrite/split `F`; if the theorem only says `∃ F`, you lose the definitional handle. Name `F`, or include an explicit `F = schurReadoutF_L2 ...` witness in the statement.
