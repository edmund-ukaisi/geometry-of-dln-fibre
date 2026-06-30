# Reproduction - A2 Case 2 passive theta endpoint local injectivity and measurable image

Date: 2026-06-30.

Status: pen-and-paper check before Lean.  This is a local image/injectivity
consequence of the endpoint source-chart readback and raw-order source-chart
bridge.  It is not Haar transport or source-prior comparison.

## Question

Can the local coordinate readback be used to show that the concrete endpoint
theta map is locally injective, and hence that the named endpoint sector image
is measurable under the standard Lusin-Souslin hypotheses?

Answer: yes.  The direct source chart has a local left inverse.  The endpoint
topology tuple determines the direct source chart locally through the raw-order
p.13 source chart.  Therefore the endpoint topology tuple is locally
injective.  A continuous injective image of a measurable set in a Polish domain
is measurable.

## Setup

Write

```text
Y(z) =
  case2PassiveThetaEndpointTopologyTuple ... z eNext e

rawMap(z) =
  topologyTupleEdgeRawOrder (Y(z))

sourceChart(z) =
  case2PassiveThetaEndpointSourceChart ... z

readback(X) =
  case2PassiveThetaEndpointSourceChartReadback ... X.
```

The previous readback theorem gives an open neighborhood `V_read` of a
determinant-sector, nonzero-pivot base point such that

```text
readback(sourceChart(z)) = z
```

for every `z ∈ V_read`.

The raw-order bridge gives an open neighborhood `V_raw` of the same base point
such that

```text
rawChart(rawMap(z)) = sourceChart(z)
```

for every `z ∈ V_raw`, where `rawChart` is the fixed-base retained-passive
p.13 raw-order source chart.

Let

```text
V = V_read ∩ V_raw.
```

Then `V` is open and contains the base point.

## Source-chart injectivity

Suppose `z,z' ∈ V` and

```text
sourceChart(z) = sourceChart(z').
```

Apply `readback` to both sides.  Since `z,z' ∈ V_read`,

```text
z  = readback(sourceChart(z))
   = readback(sourceChart(z'))
   = z'.
```

Therefore `sourceChart` is injective on `V`.

## Endpoint topology-tuple injectivity

Suppose `z,z' ∈ V` and

```text
Y(z) = Y(z').
```

Then applying `topologyTupleEdgeRawOrder` gives

```text
rawMap(z) = rawMap(z').
```

Since `z,z' ∈ V_raw`,

```text
sourceChart(z)
  = rawChart(rawMap(z))
  = rawChart(rawMap(z'))
  = sourceChart(z').
```

The source-chart injectivity on `V` gives `z = z'`.  Hence `Y` is injective on
`V`.

## Measurable endpoint image

Assume the theta coordinate domain is a Polish Borel measurable space, the
endpoint topology-tuple target has opens measurable, and `V` is measurable
because it is open.  The map `Y` is continuous by
`continuous_case2PassiveThetaEndpointTopologyTuple`, hence continuous on `V`.
Since `Y` is injective on `V`, Lusin-Souslin gives

```text
MeasurableSet (Y '' V).
```

By definition,

```text
Y '' V = case2PassiveThetaEndpointSectorSet ... V.
```

Therefore the endpoint sector image is measurable for this returned local
neighborhood.

## Lean Targets

Add to

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean
```

Suggested public names:

```text
exists_open_case2PassiveThetaEndpointTopologyTuple_sourceChart_injOn
exists_open_measurableSet_case2PassiveThetaEndpointSectorSet
```

The first theorem should return one open set `V` and both local injectivity
facts:

```text
Set.InjOn sourceChart V
Set.InjOn Y V
```

The second theorem should return an open `V` with

```text
MeasurableSet (case2PassiveThetaEndpointSectorSet ... V)
```

under explicit Borel/Polish hypotheses, using
`MeasurableSet.image_of_continuousOn_injOn`.

## Nonclaims

This slice does not prove global endpoint-sector measurability, source-image
equality, source-rank coverage, exact passive-sector Haar transport,
determinant-chart Haar transport, raw-order Haar transport, source-prior
comparison, normal crossings, pole order, or RLCT extraction.

