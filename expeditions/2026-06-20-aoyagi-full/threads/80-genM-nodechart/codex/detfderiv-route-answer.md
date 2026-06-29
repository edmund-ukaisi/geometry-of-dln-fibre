**Short verdict:** the direct locality route should be treated as blocked for the real `phiFlatLiveR1`. The staircase is not merely a heavier proof of the same square block-triangular fact; it is the way to express the rectangular/input-output partition mismatch.

1. **Why locality alone does not close**

`fderiv_abs_det_eq_prod_diagBlocks` needs one grading `g : Fin N → ℕ` used for both rows and columns. But the real chart has two different natural partitions:

- output rows: `paramsEquivFlat` / `FlatIdx`, layer sizes `M_s * M_{s+1}`;
- input columns: `chartIdxEquiv` / `ChartIdx`, boundary sizes `schurDim s + liftDim s`.

The banked obstruction `flatLayer_ne_chartBoundary_222` is decisive: for `(2,2,2)`, these are `(4,4)` versus `(6,2)`. So:

- with `g = bLayer`, the column grading is meaningful, but row grades do not match output layers;
- with `g = flatLayer`, rows are meaningful, but the reader-locality columns are wrong;
- with a coarsening, the diagonal blocks no longer have the engine determinant factors.

So if someone hands you `himg/hR/hB` for the direct `toSquareBlock (toDual ∘ bLayer)` route, the headline follows formally. The problem is that those hypotheses are not the real chart’s geometry.

2. **Is `toSquareBlock` less cast-painful?**

Likely no. It is probably worse.

`toSquareBlock g a` indexes both rows and columns by the same subtype `{i // g i = a}`. But the engine block wants output coordinates from one indexing story and input coordinates from another. To compare it with `schurFrameDeriv` / `lduCoreDeriv`, you would need subtype equivalences back to native `Fin` block widths anyway.

The concrete `(3,3,3,3)` proofs already show the pattern: `det_submatrix_equiv_self`, hand-built `e9`, `Matrix.toSquareBlock_def`, and explicit coordinate normalization. That was manageable at literal `Fin 27`; over opaque `Text`/`Wext`, this reintroduces the same dependent-`Fin` pain, but spread across every block.

The staircase route at least concentrates the pain into one layer-collecting presentation, after which `hR/hB` can be stated on native engine linear maps.

3. **Best third option**

Yes: prove the remaining work componentwise as `HasFDerivAt` statements for layer-restricted maps, then assemble those into the staircase hypothesis.

Concretely, aim for lemmas of the form:

```lean
HasFDerivAt (boundaryRestrictedChart s) boundaryEngineDeriv u
```

where `boundaryEngineDeriv` is built from `schurFrameDeriv`, `lduCoreDeriv`, and the det-1 shear/identity pieces. Then assemble these componentwise derivative identities into the `hconj` required by `interiorDet_phiFlatLiveR1_of_stairConj`.

If the current single-`e` conjugacy fights the natural input/output partitions, introduce a two-equivalence wrapper:

```lean
eOut ∘ D ∘ eIn.symm = stairMap ...
|det eOut| = 1
|det eIn| = 1
```

and prove the same determinant conclusion by `det_comp`. That is still a staircase presentation, but it may be less artificial than forcing one coordinate equivalence to serve both roles.

**Recommendation:** do not spend the next tide on direct `toSquareBlock` identification for `bLayer`. Push the componentwise `HasFDerivAt` route, feeding a staircase or two-sided staircase determinant wrapper. That is the least-cast path that respects the actual partition mismatch.