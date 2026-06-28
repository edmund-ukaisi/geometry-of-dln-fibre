# Statement Card - A2 generic shear/product abs-det wrappers

## Lean Names

Expected in `lean/DLNFibre/DLN/Aoyagi/MatrixLinearDeterminant.lean`:

```text
linearEquiv_prodCongr_abs_det_eq_one
linearEquiv_skewProd_refl_refl_det_eq_one
linearEquiv_skewProd_refl_refl_abs_det_eq_one
linearEquivUpperShear_abs_det_eq_one
```

## Mathematical Content

These are generic finite-dimensional determinant wrappers.

For a product linear equivalence, if both factors have absolute determinant one,
then their product congruence has absolute determinant one:

```text
|det(eM.prodCongr eN)| = |det(eM)| * |det(eN)| = 1.
```

For the lower refl/refl skew shear and the upper additive shear, the existing
determinant-one lemmas imply the corresponding absolute-determinant-one facts.

## Dependencies

```text
linearEquiv_prodCongr_det_eq_mul
linearEquiv_det_skewProd_toLinearMap_eq_mul
linearEquivUpperShear_det_eq_one
```

## Non-Claims

This does not construct a retained-passive target normalizer, prove the raw
coordinate Jacobian determinant equality, transport source priors, prove normal
crossings, compute pole order, compute RLCT, or perform analytic extraction.
