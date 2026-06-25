Verdict: **SOUND**, with one small interpretive caveat on Q5.

I inspected the local proof at [DeepestPivotFrame.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/DeepestPivotFrame.lean:147). The construction matches the informal theorem.

**Q1: SOUND.**  
The proof sets `Qt = fromBlocks VJ⁻¹ (-(VJ⁻¹ * VK)) 0 1`, then `Q = reindex e.symm e.symm Qt`. It proves `reindex e e Q = Qt`, rewrites with `Matrix.toBlocks_fromBlocks₂₂`, and gets `isUnit_one`; see [lines 169-187](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/DeepestPivotFrame.lean:169). So yes: the `₂₂` block is literally the bottom-right block of `fromBlocks`, in the pivot split.

The unit claim for `Q` is also sound: `Qt` is block upper triangular with unit diagonal blocks, and reindexing by equivalences preserves `IsUnit`; see [lines 173-181](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/DeepestPivotFrame.lean:173).

**Q3: SOUND.**  
The proof explicitly proves

`reindex rsplit e A = fromBlocks VJ VK 0 0`

then multiplies by `Qt` using `Matrix.fromBlocks_multiply`; see [lines 193-223](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/DeepestPivotFrame.lean:193). The algebra is correct:

`[VJ VK; 0 0] * [VJ⁻¹ -VJ⁻¹VK; 0 1] = [1 0; 0 0]`.

The cancellation uses `VJ * VJ⁻¹ = 1`, justified by the proved unit of `VJ`.

**Q4: SOUND. No hidden first-column restriction.**  
This is the crucial part: the bottom blocks vanish only because the row split is the threshold split. The theorem uses

`(rThresholdSplit r a hra).symm (Sum.inr i) = r + i`

from [DeepestFrameRaw.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/DeepestFrameRaw.lean:74), then applies `htail` in both bottom-block cases; see [DeepestPivotFrame.lean lines 214-215](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/DeepestPivotFrame.lean:214). No property of `J` is used there.

`J` affects only the column split. Locally, `pivotThresholdSplit` is defined so its left block is `Set.range J` in sorted order and its right block is the complement; see [DeepestSplitReindex.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:166). The proof even handles the order mismatch between `J` and the sorted split via a permutation bridge; see [DeepestPivotFrame.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/DeepestPivotFrame.lean:34). So this is not secretly assuming the first `r` columns are pivots.

**Q5: SOUND / non-vacuous.**  
For `r=1`, `a=b=2`,

`A = [[0, 1], [0, 0]]`.

Then:

`V = [0, 1]`.

Choose `J(0)=1`. The pivot split has

`e.symm (inl 0) = 1`, `e.symm (inr 0) = 0`.

So

`VJ = [1]`, `VK = [0]`.

Thus

`Qt = [[1, 0], [0, 1]]`

in the pivot-indexed order `(pivot column 1) ⊕ (complement column 0)`, and `Q = I` in standard coordinates. Hence `Q` is a unit, and `((reindex e e Q).toBlocks₂₂) = [1]`.

The normalized product is not a first-column statement:

`A * Q = A = [[0, 1], [0, 0]]`

in standard column order, but after the pivot column split `e`, columns are read as `(1, 0)`, giving

`reindex rsplit e (A * Q) = [[1, 0], [0, 0]] = fromBlocks 1 0 0 0`.

Caveat: in this particular example `Q = I`, so many one-dimensional `B22` readings are numerically `[1]` by accident. The non-front-pivot content is visible in the column reindexing: the identity corner is at original column `1`, not original column `0`.