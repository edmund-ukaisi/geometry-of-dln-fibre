# Reproduction - A2 Case 2 endpoint-reference raw-order/source-chart handoff

Date: 2026-07-01.

Status: pen-and-paper reproduction for the functorial handoff from the
endpoint reference image to the raw-order image and then to the p.13 source
chart.

## Question

The concrete passive-theta reference source is already named, and its raw-order
image is already named.  The next bookkeeping question is to prove that these
names commute with the actual maps:

```text
Phi_* (Y_* referenceSource|V) = rawMap_* referenceSource|V
rawChart_* (rawMap_* referenceSource|V) = sourceChart_* referenceSource|V.
```

Here `rawMap = Phi o Y`, where `Phi = topologyTupleEdgeRawOrder`.

## Coordinates and Measures

Let

```text
Theta = Case2PassiveTheta ...
rho = Fin (Module.finrank R U0)
kappa' = throughSubspaceEndpointComplementIndex ...
RawTuple = TopologyTuple rho kappa' R.
```

The reference source is

```text
referenceSource =
  case2PassiveThetaReferenceSourceMeasure n hS hnext Rres.
```

The endpoint map is

```text
Y(theta) =
  case2PassiveThetaEndpointTopologyTuple ... theta eNext e.
```

The raw-order map on topology tuples is

```text
Phi(y) =
  topologyTupleEdgeRawOrder y.
```

The theta-domain raw map is

```text
rawMap(theta) = Phi(Y(theta)).
```

The p.13 source-chart maps are

```text
rawChart =
  paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart W2 B2 U0 hU0

sourceChart(theta) =
  case2PassiveThetaEndpointSourceChart W2 B2 ... theta.
```

## Local Shrink

The existing local raw-order/source-chart package gives an open set `V` inside
any prescribed open neighborhood `G` of the base point such that:

```text
Y(theta) in topologyTupleDetChartSet,
rawMap(theta) in topologyTupleRawOrderSourceRecursiveDetChartSet,
rawChart(rawMap(theta)) = sourceChart(theta)
```

for all `theta in V`.

This is the same local shrink that requires both determinant-sector membership
at the base point and the nonzero selected-entry pivot.  The pivot condition is
for the source-chart/inverse-readout package, not for determinant-chart support
alone.

## First Identity

The endpoint reference image is

```text
endpointReferenceImage =
  Y_* (referenceSource restricted to V).
```

The raw-order reference image is

```text
rawOrderReferenceImage =
  rawMap_* (referenceSource restricted to V).
```

Since `Y(theta)` lies in the determinant chart for `theta in V`, the endpoint
reference image is a.e. supported on the determinant chart.  The map `Phi` is
continuous on the determinant-chart subtype, hence a.e. measurable for this
endpoint image.  Therefore the standard `map_map` identity applies:

```text
Phi_* endpointReferenceImage
  = (Phi o Y)_* (referenceSource restricted to V)
  = rawOrderReferenceImage.
```

## Second Identity

The local package also gives the measure-level two-stage identity for every
theta-domain source measure:

```text
rawChart_* (rawMap_* sourceMeasure|V)
  =
sourceChart_* sourceMeasure|V.
```

Instantiating `sourceMeasure = referenceSource` gives:

```text
rawChart_* rawOrderReferenceImage
  =
sourceChart_* (referenceSource restricted to V).
```

## Boundary

These are functorial image-measure identities.  They do not prove that the
endpoint image, raw-order image, or source-chart image is unrestricted Haar,
original volume, or an original/source prior.  The endpoint image remains a
selected-entry chart-image slice.

## Kill Conditions

- Do not assume global measurability of `Phi`; use determinant-chart support
  and continuity on the determinant-chart subtype.
- Do not write `sourceChart` as a map out of the endpoint image.  The
  endpoint-to-source path is `rawChart o Phi`.
- Do not replace `rawOrderReferenceImage` by raw Haar.
- Do not claim source-image coverage or source-rank coverage.
