# Reproduction - A2 Case 2 passive-source raw-Haar inverse-Jacobian domination

Date: 2026-07-01.

Status: pen-and-paper reproduction for a conditional Lean socket.

## Question

What honest raw-Haar statement follows from the current Case 2 passive-theta
infrastructure without assuming that the arbitrary passive measure itself is a
Haar/product-volume source?

## Calculation

On the local Case 2 determinant/pivot sector write

```text
Y z =
  case2PassiveThetaEndpointTopologyTuple z

rawMap z =
  topologyTupleEdgeRawOrder (Y z)

mu =
  passiveSource.restrict V.
```

Let `rawHaar` be any additive Haar measure on the topology-tuple space.  Put

```text
detSet =
  topologyTupleDetChartSet

rawSet =
  topologyTupleRawOrderSourceRecursiveDetChartSet

invJac y =
  ofReal (topologyTupleEdgeRawOrderInverseJacobianDensity y).
```

The retained-passive raw-order change-of-variables theorem gives

```text
Measure.map topologyTupleEdgeRawOrder (rawHaar.restrict detSet)
=
(rawHaar.restrict rawSet).withDensity invJac.
```

Therefore, if the still-missing determinant-chart comparison is supplied as

```text
Measure.map Y mu <= c • rawHaar.restrict detSet,
```

then monotonicity of `Measure.map` and `Measure.map_smul` give

```text
Measure.map topologyTupleEdgeRawOrder (Measure.map Y mu)
  <= c • Measure.map topologyTupleEdgeRawOrder (rawHaar.restrict detSet)
  = c • (rawHaar.restrict rawSet).withDensity invJac.
```

Since `Y` is continuous and raw-order is a.e.-measurable on the determinant
chart reference, the composed-map identity rewrites the left side as

```text
Measure.map rawMap mu.
```

Thus the correct conditional theorem is

```text
Measure.map rawMap (passiveSource.restrict V)
  <= c • (rawHaar.restrict rawSet).withDensity invJac
```

under the explicit hypothesis

```text
Measure.map Y (passiveSource.restrict V)
  <= c • rawHaar.restrict detSet.
```

## Boundary

This does not prove the determinant-chart hypothesis.  It only says that once
the endpoint topology-tuple image of the passive-product theta reference is
dominated by determinant-chart Haar, the raw-order image is dominated by the
corresponding inverse-Jacobian raw-order Haar measure.

For arbitrary `passiveMeasure`, exact raw-Haar transport is not derivable from
the present hypotheses.  A singular passive measure could concentrate the raw
image on a lower-dimensional set.  The theorem therefore leaves passive-source
to determinant-Haar comparison as the next frontier.
