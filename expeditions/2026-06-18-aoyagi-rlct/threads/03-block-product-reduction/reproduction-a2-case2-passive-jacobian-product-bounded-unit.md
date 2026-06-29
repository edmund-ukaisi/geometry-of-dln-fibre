# Reproduction - A2 Case 2 Passive Jacobian Product Bounded Unit

Date: 2026-06-29.

Status: controller pen-and-paper reproduction before Lean.  This is a
passive-Jacobian accounting step, not a source-prior transport theorem.

## Question

For the passive-parameter Case 2 selected-entry retained-passive datum, can the
retained-passive raw-order Jacobian product be treated locally as a bounded
positive unit?

Answer: yes, on any point of the determinant chart and under the same
continuity and determinant-unit hypotheses already used for the passive source
chart.  This follows from the existing retained-passive Jacobian theorem: the
solved-`A1` product determinant density is continuous and positive on the
retained-passive determinant chart.

## Coordinate Map

Let

```text
center = case2ResidualBlockPivotEntries n S (J + 1).
```

The passive selected-entry coordinate point is

```text
z = (theta, y) : eta x (center -> R).
```

The retained-passive coordinate datum is

```text
rawData z =
  case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
    (A1passive theta) (F2 theta) (A3passive theta)
    (Ctop theta) (F3 theta) y eNext.
```

After endpoint transport into the fixed-base retained-passive domain,

```text
retainedData z = (rawData z).endpointTransport e.
```

The topology-tuple coordinate map used by the retained-passive Jacobian
package is

```text
Y z = topologyTuple (retainedData z).
```

## Determinant Chart

At the base point `z0 = (theta0, y0)`, the determinant-chart conditions are:

```text
IsUnit ((Ctop theta0).det)
forall p : Fin 1, IsUnit ((A1passive theta0 p).det).
```

The selected-entry residual coordinates `y` do not enter these determinant
conditions.  The passive fields do enter the source matrices, but the local
unit statement only needs that `Y z0` is in the retained-passive determinant
chart at the base point.

## Continuity

The existing passive selected-entry continuity theorem proves continuity of

```text
z |-> rawData z
```

from continuity of the passive fields

```text
A1passive, F2, A3passive, Ctop, F3.
```

Endpoint transport is continuous on determinant-chart data, and
`topologyTuple` is continuous for the induced product topology.  Hence

```text
Y : eta x (center -> R) -> TopologyTuple ...
```

is continuous at every base point.

## Jacobian Unit

The retained-passive Jacobian package defines

```text
retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z).
```

It is the solved-`A1` product formula for the absolute determinant of the
raw-order coordinate change.  On the determinant chart, it equals the actual
Frechet absolute determinant and is positive.  By continuity and positivity at
`Y z0`, there are constants

```text
epsilon > 0, K > 0
```

such that eventually near `z0`,

```text
epsilon <= retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z)
retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z) <= K.
```

This is precisely the bounded-unit statement needed before using the
passive variables in a measure comparison.

## Nonclaims

- This does not prove determinant-chart Haar pushforward for the passive
  selected-entry sector.
- This does not identify an original DLN source prior.
- This does not prove selected-entry image coverage or source-rank coverage.
- This does not remove a measure hypothesis by itself.
- This does not prove normal crossings, pole order, or RLCT.

## Lean Target

The Lean theorem should instantiate

```text
exists_pos_eventually_bounds_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_comp
```

with the Case 2 passive selected-entry transported topology-tuple map.  The
statement should keep passive-field continuity explicit, require determinant
units only at the base point, and conclude only eventual positive lower and
upper bounds for the composed product-Jacobian density.
