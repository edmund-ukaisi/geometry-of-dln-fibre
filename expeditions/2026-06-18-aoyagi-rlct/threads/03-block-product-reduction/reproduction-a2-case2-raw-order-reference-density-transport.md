# Reproduction - A2 Case 2 raw-order reference density transport

Date: 2026-07-01.

Status: pen-and-paper reproduction for transporting a density on the named
raw-order reference image through the p.13 raw-order source chart.

## Question

The raw-order reference image is now named:

```text
rawOrderReferenceImage =
  rawMap_* (referenceSource restricted to V).
```

If `rawDensity` is a measurable density on this named image measure, what is
the corresponding source-chart image after applying the p.13 raw-order chart?

## Setup

Let

```text
referenceSource =
  case2PassiveThetaReferenceSourceMeasure ...

Y(theta) =
  case2PassiveThetaEndpointTopologyTuple ... theta

Phi(y) =
  topologyTupleEdgeRawOrder y

rawMap(theta) = Phi(Y(theta))

rawChart =
  paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart ...

sourceChart(theta) =
  case2PassiveThetaEndpointSourceChart ... theta.
```

The local raw-order/source-chart theorem supplies an open set `V` such that

```text
rawChart(rawMap(theta)) = sourceChart(theta)
```

for all `theta in V`, and its measure-level package gives the two-stage
identity for any theta-domain source measure.

## Density Transport

Let

```text
rawOrderReferenceImage =
  Measure.map rawMap (referenceSource.restrict V).
```

Assume

```text
rawDensity : RawTuple -> ENNReal
```

is a.e. measurable with respect to `rawOrderReferenceImage`.

The reusable measure lemma says that if `rawMap` is a.e. measurable for
`referenceSource.restrict V`, then

```text
Measure.map rawChart
  (rawOrderReferenceImage.withDensity rawDensity)
=
Measure.map sourceChart
  ((referenceSource.withDensity
    (fun theta => rawDensity (rawMap theta))).restrict V).
```

The a.e. measurability of `rawMap` is local: the same shrink gives
`Y(theta)` in the determinant chart on `V`, `Y` is continuous, and
`topologyTupleEdgeRawOrder` is continuous on the determinant-chart subtype.

## Boundary

This transports a density on the actual named raw-order image.  It is not a
raw-Haar statement and does not identify the image with unrestricted raw
coordinate volume.  The density is a supplied raw-image density, not an
original/source-prior density constructed from Aoyagi's statistical model.

## Kill Conditions

- Do not replace `rawOrderReferenceImage` by raw Haar.
- Do not assume global measurability of `rawMap`; use the local determinant
  chart support.
- Do not claim this constructs the original source prior or proves bounded
  density.
- Do not claim normal crossings, pole order, or RLCT extraction.
