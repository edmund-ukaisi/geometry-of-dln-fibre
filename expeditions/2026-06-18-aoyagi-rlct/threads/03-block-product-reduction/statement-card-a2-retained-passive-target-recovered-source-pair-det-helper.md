# Statement Card - A2 target-recovered source pair and product determinant helper

## Lean names

In `lean/DLNFibre/DLN/Aoyagi/MatrixLinearDeterminant.lean`:

```text
linearEquiv_prodCongr_det_eq_mul
```

In `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`:

```text
retainedPassiveTargetRecoveredSourcePairAt
retainedPassiveTargetRecoveredSourcePairAt_fderiv_eq_sourcePair
retainedPassiveTargetRecoveredSourceCAt
retainedPassiveTargetRecoveredSourceCAt_fderiv_eq_sourceC
```

## Mathematical content

`retainedPassiveTargetRecoveredSourcePairAt hz w` first forms the target-side
normalized `(F2,C)` pair from the arbitrary target tuple `w`, then applies the
point-specialized inverse formal edge-pair equivalence.  On an actual
raw-order derivative target it recovers the source `(F2,C)` tangent pair:

```text
retainedPassiveTargetRecoveredSourcePairAt hz ((fderiv raw z) v)
  = (v.F2, v.C).
```

The `retainedPassiveTargetRecoveredSourceCAt` projection gives the component
formula

```text
retainedPassiveTargetRecoveredSourceCAt hz ((fderiv raw z) v) q = v.C(q).
```

`linearEquiv_prodCongr_det_eq_mul` states that the determinant of a product
linear equivalence is the product of the factor determinants.

## Dependencies

The target-recovered source pair uses:

```text
retainedPassiveTargetEdgePairShearAt
retainedPassiveTargetEdgePairShearAt_fderiv_recovers_sourcePair
retainedPassiveFormalRawF2CLinearEquivAt
```

The determinant helper uses:

```text
linearMap_det_prodMap_eq_mul
LinearEquiv.coe_prodCongr
```

## Non-claims

This checkpoint does not construct the determinant-one target normalizer, does
not prove the actual raw-order determinant formula, and does not target-stage
the positive-tail lower-left recurrence.  It only supplies two inputs for that
future construction: target-side recovery of source `C` tangents and a product
determinant helper.

