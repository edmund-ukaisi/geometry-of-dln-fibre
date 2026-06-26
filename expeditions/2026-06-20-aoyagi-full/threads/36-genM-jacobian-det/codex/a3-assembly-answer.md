1. **Q1:** Yes, the worry is real: the lower block is not diagonal.  
`(L⁻¹ * lowMat dl * diag q) i j` for `j < i` depends on `dl k j` with `j < k ≤ i`; the `k = i` term gives diagonal coefficient `q j`, and `k < i` gives unipotent lower-triangular mixing. So it is triangular, not diagonal.

2. **Q2:** Use triangular determinants, not polynomial independence. The coordinate matrix of the lower block is lower-triangular in the inherited lex order on `LowIdx t`; prove its diagonal is `p ↦ q p.1.2`, then use:
`LinearMap.det_toMatrix'` + `Matrix.det_of_lowerTriangular`.

**Recommendation**

1. Set `L := 1 + lowMat l`, `U := 1 + upMat u`, `D := Matrix.diagonal q`. Prove local lemmas:
   `L.det = 1`, `U.det = 1` by `Matrix.det_of_lowerTriangular` / `Matrix.det_of_upperTriangular`.

2. Package inverses using `Matrix.isUnit_iff_isUnit_det` and `IsUnit.invertible`; get triangularity of `L⁻¹`, `U⁻¹` from `Matrix.blockTriangular_inv_of_blockTriangular`. Add local lemmas that their diagonals are `1`.

3. Factor
   `lduCoreDeriv = E ∘ₗ core`, where  
   `E = matrixSplit.toLinearMap ∘ₗ (mulLeftMat L ∘ₗ mulRightMat U) ∘ₗ matrixSplit.symm.toLinearMap`.  
   Prove `det E = 1` via `LinearMap.det_conj`, `LinearMap.det_comp`, `det_mulLeft_matrixSpace`, `det_mulRight_matrixSpace`.

4. Show `core` is block diagonal on `Low × Diag × Up`; apply your `lowerTri_det` twice and `LinearMap.det_id`.

5. Prove:
   `det lowerBlock = ∏ p : LowIdx t, q p.1.2` and  
   `det upperBlock = ∏ p : UpIdx t, q p.1.1`  
   using `LinearMap.toMatrix'_apply`, `Matrix.mul_apply`, `Matrix.diagonal_apply`, `Pi.single_apply`, then `Matrix.det_of_lowerTriangular`.

6. Convert the products: use your landed LowIdx count; get the UpIdx count by swapping `UpIdx t ≃ LowIdx t`. Combine with `Finset.prod_mul_distrib` and `pow_add`.

**Biggest Risk**

The inverse-diagonal lemma is the likely time sink. Pre-empt it as a general local lemma: if `A` is triangular, `A i i = 1`, and `A.det` is a unit, then `(A⁻¹) i i = 1`, proved from `Matrix.nonsing_inv_mul` or `Matrix.mul_nonsing_inv` plus triangular zero terms.