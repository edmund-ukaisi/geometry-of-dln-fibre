# A2 with-following original-volume readback from reverse raw-source domination

Date: 2026-07-02.

## Source calculation

Aoyagi's p.13 retained-passive chart has two elementary coordinate changes in
this lane.

First, on the determinant chart, the raw-order map `Phi` has formal product
Jacobian

```text
formalDensity(y)
  = |det d Phi_y| = retainedPassiveFormalRawOrderJacobianProductAbsDetAt(y).
```

The retained-passive COV theorem already formalizes:

```text
map Phi ((rawHaar | rawDetChart).withDensity formalDensity)
  = rawHaar | rawSourceSet.
```

Second, the p.13 source chart `p13SourceChart` sends the raw-order source chart
to the original edge-family source coordinates.  The p.13 source-measure bridge
already formalizes the scalar comparison:

```text
map p13SourceChart (rawHaar | rawSourceSet)
  = cHaar • originalVolume | p13SourceSet
```

where `cHaar` is the tuple-side Haar normalization scalar.  Equivalently, after
restricting to a measurable p.13 chart piece,

```text
originalVolume | chartPiece
  <= (cHaar^-1 * D) • sourceRef
```

whenever the formal-product chart measure on that piece is dominated by
`D • sourceRef`.

## With-following source-reference handoff

On the local with-following Case 2 shrink, the endpoint raw map factors through
the same raw-order source chart:

```text
rawChart (rawMap z) = sourceChart z.
```

Therefore a supplied finite reverse raw-source domination

```text
rawHaar | rawSourceSet
  <= D • map rawMap (thetaReference | V)
```

pushes through the p.13 source chart to

```text
formalProductMeasure | chartPiece
  <= D • map sourceChart (thetaReference | V)
```

for any measurable chart piece in the p.13 source set.  Combining with the
p.13 original-volume scalar comparison gives

```text
originalVolume | chartPiece
  <= (cHaar^-1 * D) • map sourceChart (thetaReference | V).
```

## Readback step

The local with-following source chart has a readback left inverse on the same
shrink:

```text
readback (sourceChart z) = z,
```

and `sourceChart` is continuous and injective on `V`, with measurable image.
Thus the chart-produced source reference pulls back exactly:

```text
map readback (map sourceChart (thetaReference | V))
  = thetaReference | V.
```

Since `V subset G`, the pullback is dominated by `thetaReference | G`.  The
standard readback domination handoff then turns

```text
originalVolume | chartPiece
  <= (cHaar^-1 * D) • sourceRef
```

into

```text
map readback (originalVolume | chartPiece)
  <= (cHaar^-1 * D) • thetaReference | G.
```

## Boundary

This is not determinant-Haar production and not source-density positivity.  The
reverse raw-source domination remains an explicit input.  The intended use is
to consume the reverse raw-source domination supplied by the with-following
raw-image handoff, with `thetaReference` instantiated as the coordinate source
measure.
