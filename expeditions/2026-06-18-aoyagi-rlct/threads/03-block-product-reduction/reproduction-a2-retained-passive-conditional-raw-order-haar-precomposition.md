# Reproduction - A2 retained-passive conditional raw-order Haar precomposition

Date: 2026-06-30.

## Goal

Record the pen-and-paper calculation behind the conditional retained-passive
raw-order transport theorem.

The theorem is not an original-prior theorem.  It says that if a source-side
parametrisation already has the correct determinant-chart Haar pushforward,
then composing it with the retained-passive raw-order map has the expected
inverse-Jacobian density on the raw source chart.

## Calculation

Let `S` be the retained-passive determinant chart set and `T` the raw-order
source-recursive determinant chart set.  Write

```text
Phi = topologyTupleEdgeRawOrder
Jinv(y) = topologyTupleEdgeRawOrderInverseJacobianDensity(y).
```

The existing retained-passive change-of-variables theorem gives

```text
map Phi (m|S) = (m|T).withDensity Jinv.
```

Now let `pre : X -> TopologyTuple` be any measurable source-side chart and
let `eta` be any source-side measure satisfying the explicit hypothesis

```text
map pre eta = m|S.
```

Then the desired identity is just associativity of pushforward:

```text
map (Phi o pre) eta
  = map Phi (map pre eta)
  = map Phi (m|S)
  = (m|T).withDensity Jinv.
```

The only analytic side conditions are the a.e. measurability of `pre` with
respect to `eta` and of `Phi` with respect to `map pre eta`, both needed for
the first equality.  The latter is supplied from the determinant-chart equality
above: `Phi` is continuous on `S`, so it is a.e.-measurable with respect to
`m|S`, hence also with respect to `map pre eta` after rewriting by the
source-side pushforward hypothesis.

## Boundary

This does not prove that any passive-theta domain measure pushes forward to
`m|S`.  It also does not compare an original DLN source prior to the
chart-produced measure.  Those remain separate source-prior/image frontiers.
