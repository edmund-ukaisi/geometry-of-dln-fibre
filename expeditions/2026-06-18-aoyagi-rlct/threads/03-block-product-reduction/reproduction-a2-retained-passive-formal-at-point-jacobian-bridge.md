# A2 retained-passive formal-at-point Jacobian bridge scaffold

Status: controller reproduced; Lean-proved; xhigh-reviewed.

## Scope

This checkpoint packages the formal retained-passive raw-order Jacobian at a
tuple point.  It is a bridge scaffold between two existing layers:

```text
true analytic layer:
  fderiv topologyTupleEdgeRawOrder

formal determinant layer:
  retainedPassiveFormalRawOrderJacobian
```

It does not assert that the formal map is the Frechet derivative.  The true
comparison still needs a triangular/shear factorization.

## Point specialization

For a tuple `z`, write

```text
data  = ofTopologyTuple z
coord = data.toCoordinateData
A p   = coord.solvedA1 p
G p   = coord.solvedA3 p
H p   = coord.F2 p.succ
Tail  = retainedPassiveA1TailAfterFirst data.A1seed
Last  = coord.solvedA1 (Fin.last M).
```

The point-specialized formal raw-order map is

```text
retainedPassiveFormalRawOrderJacobian Tail A H G Last.
```

This is exactly the determinant-bearing core from the earlier formal raw-order
calculation.

## Determinant facts

The determinant formula specializes to

```text
det J_formal(z)
  =
    det(Tail^{-1})^|rho|
    * product_p det(-(A p))^|kappa' p.castSucc|
    * det(-Last)^|kappa' (Fin.last (M+1))|.
```

On the retained-passive determinant chart, the existing unit facts imply that
all displayed determinants are units.  Therefore the specialized formal
determinant is nonzero, and its absolute value is positive.

## Relation to the true derivative

The analytic layer already proves that

```text
det (fderiv topologyTupleEdgeRawOrder z)
```

is a unit on the same determinant chart.  The new bridge file records the two
unit statements side by side, but it does not identify the determinants.

The missing theorem is expected to have the form

```text
absdet (fderiv topologyTupleEdgeRawOrder z)
  =
absdet (retainedPassiveFormalRawOrderJacobianAt z)
```

proved by factoring the true derivative through determinant-one shears and
product-coordinate permutations around the formal determinant core.

## Lean objects

Lean-proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`:

```text
retainedPassiveFormalRawOrderJacobianAt
retainedPassiveFormalRawOrderJacobianAt_det_eq
retainedPassiveFormalRawOrderJacobianAt_det_isUnit_of_mem_topologyTupleDetChartSet
retainedPassiveFormalRawOrderJacobianAbsDetAt
retainedPassiveFormalRawOrderJacobianAbsDetAt_pos_of_mem_topologyTupleDetChartSet
topologyTupleEdgeRawOrder_fderiv_det_and_formal_det_isUnit_of_mem_topologyTupleDetChartSet
```

## Nonclaims

No true-formal determinant equality, no `HasFDerivAt` component formula, no
measure pushforward, no normal-crossing extraction, and no RLCT statement is
proved here.
