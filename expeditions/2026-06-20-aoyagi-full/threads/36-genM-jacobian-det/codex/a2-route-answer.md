1. I would treat Q1 as **no, build it**. Mathlib v4.29 has `LinearMap.det_prodMap` for block-diagonal product maps and matrix-level triangular tools, but I would not expect an abstract “det of triangular endomorphism of a product” lemma for arbitrary product modules.

2. I would also **not use** a nilpotent/unitriangular lemma here. Even if some nilpotent determinant lemma exists, the robust route is to realize the operator as block-triangular and use either `Matrix.BlockTriangular.det` or nested `Matrix.det_fromBlocks_zero₂₁` / `Matrix.det_fromBlocks_zero₁₂`.

3. Recommendation: **(a), but via nested binary product matrices**, not a full flattened entry matrix.

Key lemma chain:

1. Put `E` as `A × (B × (C × F))`, where  
   `A = Matrix (Fin t) (Fin t) ℝ`, `B = Matrix (Fin t) (Fin c) ℝ`,  
   `C = Matrix (Fin r) (Fin t) ℝ`, `F = Matrix (Fin r) (Fin c) ℝ`.

2. Use `LinearMap.det_toMatrix` or `LinearMap.det_toMatrix'` after choosing bases, then show the matrix of `D` is nested lower block-triangular:
   first split `A | rest`, then `B | rest`, then `C | F`.

3. At each split use:
   `Matrix.det_fromBlocks_zero₁₂`  
   because the upper-right block is zero: later input blocks do not affect earlier outputs.

4. Diagonal determinants:
   `dK ↦ dK`: `LinearMap.det_id`;  
   `dN ↦ K * dN`: your A1 `mulLeftMat_det = K.det ^ c`;  
   `dX ↦ dX * K`: your A1 `mulRightMat_det = K.det ^ r`;  
   `dE ↦ dE`: `LinearMap.det_id`.

5. Finish:
   ```lean
   ring_nf
   rw [← pow_add]
   rw [abs_pow]
   ```
   or more directly prove `D.det = K.det ^ c * K.det ^ r`, rewrite by `← pow_add`, then apply `abs_pow`.

The most likely failure point is identifying the diagonal blocks after reassociating products. Pre-empt it by defining explicit `LinearEquiv`s for the 4-fold product association once, conjugating `D` by them, and proving the three block-matrix equalities by extensionality on product components. Keep A1 stated for exactly the matrix-space types appearing on the diagonal, so the final rewrites are just your A1 lemmas plus `LinearMap.det_conj`.