**VERDICT**
[fact] The product target is the right base for L=2: `BlockParamsL2 H r = A0 × A1` gives the Schur bricks the exact objects they want, `[[X,Y],[Z,W]]` and `[[S,T],[U,V]]`, with the middle type definitionally shared. [inference] A dependent `Fin 2` pi is more general but would reintroduce projection/cast noise; a single flattened `fromBlocks` target or flat slicing would hide the matrix algebra and make the product/Schur lemmas harder to apply. Keep this product-of-two-block-matrices model.

**ROUTING**
[fact] Routing through `paramsEquivFlatLinear.symm` is sound and natural: the chart needs linear/CLE structure for smoothness, derivatives, and determinant plumbing, while `paramsEquivFlat` is the measurable/semantic flattening. The proved coe bridge `paramsEquivFlatLinear_symm_coe` means the germ can transfer by rewriting functions, not by a new theorem. [inference] The only practical risk is rewrite hygiene if downstream mixes `paramsEquivFlat`, `paramsEquivFlatLinear`, and `paramsEquivFlatCLE`; mathematically this is not a smell.

**RISKS**
[fact] The shared middle index is good, but product rewrites can still hit dependent-`Fin`/`HMul` friction unless there is a blocked-product lemma. [inference] Expect pain around: `toBlocks` versus `submatrix` orientation, especially `Y/Z/U`; `H s - r` casts and missing explicit `r ≤ H s`; converting pivot `det ≠ 0` into the `[Invertible X]` / `[Invertible M11]` instances the Schur lemmas use; confusing second-layer `S` with product pivot `M11 = X*S + Y*U`; and arbitrary complement ordering from `sumSplit` if later compared to a canonical reduced-core flattening.

**MISSING**
Add now: all eight block-readback lemmas for layer0/layer1, not only `toBlocks₁₁_fst`; a blocked product lemma
`reindex I J (prod decode) = block0 * block1`, with four `toBlocks` corollaries; symm/reconstruction lemmas for `blockFlatEquiv_L2.symm`; determinant/invertibility transport lemmas from the pivot minors to `toBlocks₁₁`; and named complement maps from `sumSplit` plus `r ≤ H s` consequences. [inference] Without these, `Φ_expl` will probably not need a different equiv, but it will burn time on local cast and orientation proofs.