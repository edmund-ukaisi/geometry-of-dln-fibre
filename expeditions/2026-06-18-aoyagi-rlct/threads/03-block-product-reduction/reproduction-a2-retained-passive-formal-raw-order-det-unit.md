# A2 retained-passive formal raw-order determinant unit

Status: controller reproduced; Lean-proved; review pending.

## Scope

This note records the determinant-chart specialization of the formal
raw-order determinant calculation.  It proves that the determinant of the
formal raw-order map is a unit at a retained-passive determinant-chart point.
It does not identify this formal map with the analytic Frechet derivative of
`topologyTupleEdgeRawOrder`.

## Formal parameters at a chart point

Let `z` be a raw retained-passive `TopologyTuple`, and let

```text
data = ofTopologyTuple z
coord = data.toCoordinateData.
```

The chart-specialized formal raw-order map uses:

```text
Tail    = retainedPassiveA1TailAfterFirst data.A1seed
A p     = coord.solvedA1 p
H p     = coord.F2 p.succ
G p     = coord.solvedA3 p
LastTop = coord.solvedA1 (Fin.last M).
```

The determinant-chart predicate gives:

```text
IsUnit data.Ctop.det
forall p : Fin M, IsUnit (data.A1passive p).det.
```

Existing retained-passive lemmas turn these into:

```text
IsUnit (det Tail)
forall p : Fin (M+1), IsUnit (det (coord.solvedA1 p)).
```

The `Tail` expression is written with `data.A1seed`.  This is the same
passive top-left tail used in the solved `A1` construction; the first active
block is not part of the tail.

## Unit calculation

The formal raw-order determinant theorem gives

```text
det(formalRawOrderJacobian)
  =
det(Tail^{-1}) ^ card rho
*
(prod p : Fin (M+1), det(-(A p)) ^ card (kappa' p.castSucc))
*
det(-LastTop) ^ card (kappa' (Fin.last (M+1))).
```

Each factor is a unit:

- `det(Tail^{-1})` is a unit because `Tail^{-1} * Tail = 1`.
- `det(-(A p))` is a unit because `det(-A p) = (-1)^n * det(A p)`.
- powers and finite products of units are units.

Lean helper theorems:

```text
matrix_det_inv_isUnit_of_det_isUnit
matrix_det_neg_isUnit_of_det_isUnit
```

Lean chart-specialized theorem:

```text
retainedPassiveFormalRawOrderJacobian_det_isUnit_of_mem_topologyTupleDetChartSet
```

## Relation to analytic derivative work

The existing analytic theorem

```text
fderiv_topologyTupleEdgeRawOrder_det_isUnit_of_mem_topologyTupleDetChartSet
```

proves that the true Frechet derivative determinant is a unit on the same
chart, using the inverse chart rather than an explicit determinant formula.
This note proves the analogous unit property for the formal raw-order
comparison target.  The remaining bridge is still a determinant comparison
between the true derivative and the formal map, expected to pass through a
triangular/shear factorization.
