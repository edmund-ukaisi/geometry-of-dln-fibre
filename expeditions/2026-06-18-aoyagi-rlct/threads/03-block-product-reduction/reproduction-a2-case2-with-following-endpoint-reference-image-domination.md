# Reproduction - A2 Case 2 with-following endpoint reference image domination

Date: 2026-07-02.

Status: endpoint-reference image domination reproduced and formalised.  This
note does not claim determinant-chart Haar domination, raw-map pushforward,
source-image coverage, normal crossings, pole order, or RLCT extraction.

## Source Boundary

Aoyagi's Case 2 calculation, PDF pp. 19-21, supplies the enlarged local
coordinate source with passive-theta coordinates and an independent following
factor.  In Lean the concrete coordinate reference measure is

```text
referenceSource =
  case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
    (rho := rho) (tau := tau) n hS hnext Rres.
```

The named endpoint reference image of a source set `Omega` is

```text
endpointReferenceImage =
  Measure.map Y (referenceSource.restrict Omega),
```

where

```text
Y z =
  case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
    ... z eNext e.
```

The present step is only measure domination through this named image map.
It does not identify `endpointReferenceImage` with determinant-chart Haar.

## Calculation

Assume a source-domain measure `sourceMeasure` is dominated by a scalar
multiple of the coordinate reference:

```text
sourceMeasure <= d • referenceSource.
```

Restricting both sides to the same source set preserves domination:

```text
sourceMeasure.restrict Omega
  <= (d • referenceSource).restrict Omega
  = d • referenceSource.restrict Omega.
```

The endpoint map `Y` is continuous, hence a.e.-measurable with respect to
`referenceSource.restrict Omega`.  The standard pushforward domination
adapter gives

```text
Measure.map Y (sourceMeasure.restrict Omega)
  <=
d • Measure.map Y (referenceSource.restrict Omega).
```

By definition of the named endpoint reference image, the right side is

```text
d • endpointReferenceImage.
```

Therefore

```text
Measure.map Y (sourceMeasure.restrict Omega)
  <= d • endpointReferenceImage.
```

## Checks

- No measurability assumption on `Omega` is required for the domination
  statement: restriction is available for arbitrary sets, and the map is
  globally continuous.
- The target measure is the actual endpoint image of the concrete coordinate
  reference source restricted to the same `Omega`.
- No claim is made that this endpoint image is a Haar/product reference on the
  determinant chart.
- No raw-order Jacobian factor appears; that belongs to the later map
  `topologyTupleEdgeRawOrder o Y`.

This theorem is a source-to-endpoint image domination socket.  It lets later
localized source-density bounds travel through the full endpoint map without
overstating endpoint Haar transport.
