<task>
Lean 4 / Mathlib v4.29. Corrected design for a "pivot-aligned frame fact". Your prior review found the gap:
corM (identity in FIRST r columns) is threshold-indexed, but the keystone needs identity in the chosen PIVOT
columns. So I must CONSTRUCT a pivot-aligned frame, not reuse the corM frame. I want the CLEANEST construction
and the lemma chain. DIAGNOSIS not code.

GOAL (standalone lemma): given
  - A : Matrix (Fin a)(Fin b) ℝ, A.rank = r, tail rows vanish (A i j = 0 for (i:ℕ) ≥ r),  [so r ≤ a, r ≤ b]
produce
  - J : Fin r ↪ Fin b   and   Q : Matrix (Fin b)(Fin b) ℝ   with   IsUnit Q
  - such that  IsUnit ((Matrix.reindex e e Q).toBlocks₂₂)   where e := pivotThresholdSplit r b ha J.
(The downstream consumer also needs A * Q to be the block-normal corner so the rest of the chart works — but
for THIS lemma the toBlocks₂₂-unit conclusion is the target; tell me if A*Q's value must also be pinned and what.)

AVAILABLE (banked, sorry-free):
  - exists_pivot_cols_of_rank : V.rank = r → ∃ J : Fin r ↪ Fin b, IsUnit (V.submatrix id J).
  - V := A.submatrix (Fin.castLE h) id is the top r rows; V.rank = r is provable (rank_submatrix_le + zero-extension).
  - pivotThresholdSplit r b ha J : Fin b ≃ Fin r ⊕ Fin (b-r); e.symm(inl k) = k-th sorted pivot, e.symm(inr k)=complement.
  - toBlocks22_isUnit_of_pivot_corner (KEYSTONE): VJ VK Q11 Q12 Q21 Q22, IsUnit VJ, IsUnit (fromBlocks Q11 Q12 Q21 Q22),
      VJ*Q11+VK*Q21=1, VJ*Q12+VK*Q22=0 ⊢ IsUnit Q22.
  - Mathlib: isUnit_submatrix_equiv, submatrix_mul_equiv, reindex_apply, fromBlocks_multiply, isUnit_fromBlocks_zero₂₁,
      Matrix.fromCols / ColumnRowPartitioned API, nonsingInv (⅟ / Matrix.inv), Matrix.mul_nonsing_inv etc.

TWO CANDIDATE CONSTRUCTIONS — pick the cleanest, give the lemma chain, flag pitfalls:

(I) EXPLICIT FRAME in split coords. Let VJ := V's pivot cols (Fin r × Fin r, a unit via the σ-permutation bridge
    from your Q1 answer), VK := V's complement cols (Fin r × Fin (b-r)). Define Q̃ := fromBlocks (VJ⁻¹) (−VJ⁻¹*VK) 0 1
    : Matrix (Fin r ⊕ Fin (b-r)) (Fin r ⊕ Fin (b-r)) ℝ. Set Q := reindex e.symm e.symm Q̃ (so reindex e e Q = Q̃).
    Then toBlocks₂₂ Q̃ = 1 (trivially unit), IsUnit Q̃ via isUnit_fromBlocks_zero₂₁ (VJ⁻¹ and 1 units). And IsUnit Q
    via isUnit_submatrix_equiv. CONCERN: does this Q satisfy the downstream "A*Q = corner" the chart needs? In split
    coords (reindex refl e V)=fromCols VJ VK, times Q̃ = fromCols (VJ·VJ⁻¹) (VJ·(−VJ⁻¹VK)+VK) = fromCols I 0. So V*Q
    has identity in pivot cols, zero elsewhere — pivot-aligned, NOT corM. Is that the correct corner for the
    re-architected chart? Confirm whether the chart wants corM (threshold) or this pivot-aligned corner, and which
    objects downstream read it.

(II) RE-TARGET rank_normal_form_right_only on the column-permuted A. Let Pπ := the permutation matrix of e (move
    pivots to front), A' := A * Pπ; A'.rank = r, A' tail rows vanish, A''s first r cols are pivots. Apply
    rank_normal_form_right_only A' to get Q' with A'*Q' = corM. Then the frame for A is Q := Pπ * Q'. Use the
    KEYSTONE on V (htop1/htop2 from A*Q reindexed). CONCERN: this still has the corM-vs-pivot indexing mismatch
    unless the reindex e absorbs Pπ. Does reindex e e (Pπ * Q') relate cleanly to corM under e? 

QUESTIONS:
1. Which construction (I) or (II) is materially shorter / lower-risk in Lean v4.29? 
2. For the chosen one, give the EXACT lemma chain for: (Q-unit), (toBlocks₂₂ unit), and (A*Q corner value, if needed).
3. Is the σ-permutation bridge for VJ-unit (from your prior Q1) STILL needed in construction (I), or does Q̃ sidestep
   it (since Q̃ is defined FROM VJ which is already V's pivot cols in sorted order)?
4. CRITICAL: does the downstream gauge chart (deepestEPivot's residual blocks read via reindex (rThresholdSplit ...) 
   on the PRODUCT, and the loss-squeeze energy identification) actually require A*Q = corM specifically, or does any
   pivot-aligned invertible corner suffice provided the SAME pivot split J is used everywhere? This determines whether
   (I) is a drop-in or breaks the corner-normalization the rest of the chart assumes.
</task>

<output_contract>
Answer the 4 questions, each ≤ 7 lines. Pick ONE construction and commit. Give exact v4.29 lemma names (flag any
you're <80% sure of as "verify"). End with: RECOMMENDATION: construction (I|II), and the single biggest risk.
</output_contract>

<grounding_rules>
Distinguish "lemma exists in v4.29" from "should exist". If you cannot tell whether the chart needs corM vs
pivot-aligned without the chart source, say so and state the assumption you're making.
</grounding_rules>
