# Reproduction - A2 generic shear/product abs-det wrappers

Date: 2026-06-28.

Status: controller pen-and-paper reproduction for a determinant-infrastructure
rung.

This note is independent of the quiver-based paper.  It records generic finite
linear algebra needed later for a target-side normalizer.  It does not construct
that normalizer.

## Product congruence

For finite free modules `M` and `N`, the existing determinant formula is

```text
det(eM.prodCongr eN) = det(eM) * det(eN).
```

Over an ordered coefficient ring, if

```text
|det(eM)| = 1,
|det(eN)| = 1,
```

then

```text
|det(eM.prodCongr eN)|
  = |det(eM) * det(eN)|
  = |det(eM)| * |det(eN)|
  = 1.
```

This is the wrapper needed to assemble determinant-one shears over nested
product coordinates.

## Lower skew shear

For a lower shear

```text
(LinearEquiv.refl R M).skewProd (LinearEquiv.refl R N) f,
```

the existing determinant formula gives

```text
det(skew) = det(refl M) * det(refl N) = 1.
```

Taking absolute values gives

```text
|det(skew)| = 1.
```

No sign or permutation issue is involved because this is the product order used
by `skewProd`.

## Upper shear

The existing upper-shear theorem gives

```text
det(linearEquivUpperShear f) = 1.
```

Therefore

```text
|det(linearEquivUpperShear f)| = 1.
```

## Lean target

Expected Lean names in `MatrixLinearDeterminant.lean`:

```text
linearEquiv_prodCongr_abs_det_eq_one
linearEquiv_skewProd_refl_refl_det_eq_one
linearEquiv_skewProd_refl_refl_abs_det_eq_one
linearEquivUpperShear_abs_det_eq_one
```

## Dependencies

```text
linearEquiv_prodCongr_det_eq_mul
linearEquiv_det_skewProd_toLinearMap_eq_mul
linearEquivUpperShear_det_eq_one
abs_mul
```

## Kill Conditions

- Do not claim a retained-passive target-side normalizer has been constructed.
- Do not claim determinant equality for `topologyTupleEdgeRawOrder`.
- Do not introduce permutation-sign assertions; the product wrapper should only
  assume absolute determinant one on its factors.
- Do not claim measure transport, normal crossings, pole order, RLCT, or
  analytic extraction from these finite-dimensional wrappers.
