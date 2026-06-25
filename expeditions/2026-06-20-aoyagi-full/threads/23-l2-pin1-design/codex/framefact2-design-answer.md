**1.** Pick **(I)**. It is materially shorter: no permutation matrix, no `Pπ * Q'` orientation chase, no arbitrary `rank_normal_form_right_only` witness. Define in split coordinates:
`Q̃ := Matrix.fromBlocks VJ (-(VJ⁻¹ * VK)) 0 1`, `Q := Matrix.reindex e.symm e.symm Q̃`.
Then `toBlocks₂₂` is `1` by computation.

**2.** Chains:
`Q̃` unit: `Matrix.isUnit_nonsing_inv_iff.mpr hVJ`, `Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨…, isUnit_one⟩`.
`Q` unit: `Matrix.reindex_apply` + `(Matrix.isUnit_submatrix_equiv e e).mpr hQ̃`.
`toBlocks₂₂`: `Matrix.reindex_symm`, `Equiv.apply_symm_apply`, `Matrix.toBlocks_fromBlocks₂₂`.
Pin downstream value as:
`Matrix.reindex (rThresholdSplit r a ha) e (A * Q) = Matrix.fromBlocks 1 0 0 0`,
using `Matrix.submatrix_mul_equiv`, `Matrix.fromBlocks_multiply`, `Matrix.mul_nonsing_inv`, tail-row zero.

**3.** Yes, the σ bridge is still needed. `exists_pivot_cols_of_rank` gives unit for `V.submatrix id J` in `J`’s order, while `pivotThresholdSplit` uses sorted `Set.range J`. Need `σ : Fin r ≃ Fin r` with `e.symm (Sum.inl k) = J (σ k)`, then transfer unit by `Matrix.isUnit_submatrix_equiv (Equiv.refl _) σ`. Exact local σ-bridge name: verify.

**4.** Current chart source is threshold-indexed: `deepestEPivot`, `framedParams_split_eq_frame_raw`, and loss-squeeze block reads use `rThresholdSplit`. So (I) is not drop-in unless the same `J` is threaded there. Corrected architecture may use any pivot-aligned corner, but it must read blocks with the same `pivotThresholdSplit`; in those split coordinates it still wants `blockdiag[I,0]`.

RECOMMENDATION: construction (I), and the single biggest risk: shared-`J` threading through the chart, not the frame algebra.