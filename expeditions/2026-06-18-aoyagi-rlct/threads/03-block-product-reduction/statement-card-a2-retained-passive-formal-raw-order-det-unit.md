# Statement card - A2 retained-passive formal raw-order determinant unit

Status: Lean-proved; review pending.

## Claim

At a retained-passive determinant-chart raw tuple `z`, the determinant of the
chart-specialized formal raw-order Jacobian is a unit.

The specialization uses:

```text
Tail    = retainedPassiveA1TailAfterFirst data.A1seed
A p     = data.toCoordinateData.solvedA1 p
H p     = data.toCoordinateData.F2 p.succ
G p     = data.toCoordinateData.solvedA3 p
LastTop = data.toCoordinateData.solvedA1 (Fin.last M).
```

## Lean status

Proved in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveFormalRawOrder.lean`.

Theorems:

```text
matrix_det_inv_isUnit_of_det_isUnit
matrix_det_neg_isUnit_of_det_isUnit
retainedPassiveFormalRawOrderJacobian_det_isUnit_of_mem_topologyTupleDetChartSet
```

## Caveat

This is not the analytic determinant theorem for
`fderiv topologyTupleEdgeRawOrder`.  It is the formal-side unit result for the
comparison target.  It matches the existing analytic `IsUnit` result at the
level of unit/nonzero status, not at the level of determinant equality.
