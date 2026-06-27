# Statement card - A2 retained-passive formal-at-point Jacobian bridge

Status: Lean-proved; xhigh-reviewed.

## Claim

The formal retained-passive raw-order Jacobian can be specialized at a tuple
point `z` by reading the solved coordinate data from `z`.  On the retained
passive determinant chart, this formal determinant is a unit, hence its
absolute value is positive.

## Lean status

Lean-proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`.

Main objects:

```text
retainedPassiveFormalRawOrderJacobianAt
retainedPassiveFormalRawOrderJacobianAbsDetAt
```

Main theorems:

```text
retainedPassiveFormalRawOrderJacobianAt_det_eq
retainedPassiveFormalRawOrderJacobianAt_det_isUnit_of_mem_topologyTupleDetChartSet
retainedPassiveFormalRawOrderJacobianAbsDetAt_pos_of_mem_topologyTupleDetChartSet
topologyTupleEdgeRawOrder_fderiv_det_and_formal_det_isUnit_of_mem_topologyTupleDetChartSet
```

## Caveat

This is not the true-formal Jacobian equality.  The expected remaining bridge
is an absolute determinant equality proved from a triangular/shear
factorization of the true Frechet derivative.
