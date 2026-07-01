# Reproduction - A2 Case 2 source-image forward domination from raw domination

Date: 2026-07-01.

Status: pen-and-paper boundary check before Lean implementation.

## Question

If a local Case 2 passive-theta raw-order pushforward is only dominated by
raw Haar on the raw-order source-recursive determinant chart, what original
edge-family volume comparison follows?

## Calculation

On the local Case 2 shrink `V`, the concrete endpoint source chart factors
through the raw-order map:

```text
sourceChart = rawChart o rawMap
```

as a measure identity on every theta-domain source measure:

```text
Measure.map sourceChart (thetaReference.restrict V)
 =
Measure.map rawChart (Measure.map rawMap (thetaReference.restrict V)).
```

Assume the forward raw domination

```text
Measure.map rawMap (thetaReference.restrict V)
  <= C * rawHaar.restrict rawSourceSet.
```

The p.13 raw-order source chart is a.e. measurable for
`rawHaar.restrict rawSourceSet`: on `rawSourceSet` it agrees with the
continuous map

```text
y |-> tupleToEdgeFamily (rawOrderMatrixTuple y).
```

Mapping the domination by `rawChart` gives

```text
Measure.map sourceChart (thetaReference.restrict V)
 <= C * Measure.map rawChart (rawHaar.restrict rawSourceSet).
```

The existing p.13 raw-order/original-volume bridge identifies the right-hand
reference pushforward:

```text
Measure.map rawChart (rawHaar.restrict rawSourceSet)
 =
cHaar * originalVolume.restrict p13SourceSet,
```

where

```text
cHaar =
  ((Measure.map rawLinearEquiv rawHaar)
    .addHaarScalarFactor (originalTupleVolume d)).
```

Therefore

```text
Measure.map sourceChart (thetaReference.restrict V)
 <= (C * cHaar) * originalVolume.restrict p13SourceSet.
```

## Direction Check

This is the forward comparison:

```text
source-image measure <= constant * original volume.
```

The original-volume readback finite-integral theorem needs the reverse
direction, or equality on the local source image, to dominate the readback of
`originalVolume.restrict chartPiece` by the theta coordinate source measure.
Thus this theorem does not remove the raw-pushforward equality from the
existing original-volume finite-integral statement.

## Boundary

This theorem is still useful bedrock: it records exactly what the weaker raw
domination hypothesis proves and prevents it being overread as original-volume
transport.  Removing the equality/reverse gap still requires a local
change-of-variables theorem, coverage theorem, or lower-bound density
comparison for the passive-theta raw/source image.
