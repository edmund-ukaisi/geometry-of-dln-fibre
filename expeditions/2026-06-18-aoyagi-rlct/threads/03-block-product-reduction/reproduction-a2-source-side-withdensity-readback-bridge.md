# A2 source-side withDensity readback bridge

Date: 2026-07-06

Status: Lean proved and verified.

## Claim

Let

```text
sourceChart : Theta -> E
readback : E -> Theta
thetaReference : Measure Theta
externalMeasure : Measure E
V subset W
chartPiece subset E
density : E -> ENNReal.
```

Assume the local chart/readback hypotheses already used by the source-image
readback socket: `sourceChart` is measurable on `thetaReference.restrict V`,
`readback` is measurable on the chart-produced source image, and

```text
readback(sourceChart theta) = theta
```

for `theta in V`.  Also assume a bounded density:

```text
density(E) <= c
```

almost everywhere for

```text
(Measure.map sourceChart (thetaReference.restrict V)).restrict chartPiece.
```

If the restricted external measure is supplied in theta-side weighted form,

```text
externalMeasure.restrict chartPiece =
  (Measure.map sourceChart
    ((thetaReference.withDensity
      (fun theta => density(sourceChart theta))).restrict V)).restrict
    chartPiece,
```

then the existing readback domination conclusion follows:

```text
AEMeasurable readback (externalMeasure.restrict chartPiece)

Measure.map readback (externalMeasure.restrict chartPiece) <=
  c • thetaReference.restrict W.
```

## Calculation

The source-side identity is converted to the edge-side source-image identity by
the standard restricted `withDensity` pushforward formula.  With

```text
sourceBase = Measure.map sourceChart (thetaReference.restrict V),
```

we have

```text
Measure.map sourceChart
  ((thetaReference.withDensity
    (fun theta => density(sourceChart theta))).restrict V)
=
sourceBase.withDensity density.
```

The only factorization condition is pointwise:

```text
(fun theta => density(sourceChart theta)) theta =
  density(sourceChart theta).
```

Thus the supplied theta-side equality becomes

```text
externalMeasure.restrict chartPiece =
  (sourceBase.withDensity density).restrict chartPiece.
```

The already-proved readback socket then applies directly, using the same
left-inverse hypothesis, the same measurable chart piece, the same `V subset W`,
and the same a.e. density bound.

## p.13 wrapper

For the p.13 formal-product chart measure, the same calculation gives a
caller-facing theorem whose `externalMeasure` is the p.13 raw-order
formal-product measure:

```text
Measure.map
  (fun z => p13SourceChart(topologyTupleEdgeRawOrder z))
  ((m.restrict rawDetChart).withDensity formalProductAbsDet).
```

The wrapper consumes the theta-side identity

```text
formalProductMeasure.restrict chartPiece =
  (Measure.map sourceChart
    ((coordinateSourceMeasure.withDensity
      (fun theta => formalDensity(sourceChart theta))).restrict V)).restrict
    chartPiece
```

and returns readback domination by

```text
D • coordinateSourceMeasure.restrict W.
```

## Lean targets

Generic:

```text
aemeasurable_readback_and_measure_map_readback_restrict_piece_le_smul_restrict_superset_of_restrict_eq_map_sourceChart_withDensity

aemeasurable_readback_and_measure_map_readback_restrict_piece_le_smul_restrict_superset_of_restrict_eq_map_sourceChart_withDensity_of_continuousOn_injOn
```

in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
```

p.13 wrapper:

```text
map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_readback_le_smul_coordinateSourceMeasure_restrict_of_sourceImageReference_eq_map_sourceChart_withDensity_of_continuousOn_injOn
```

in:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13ReadbackFiniteIntegral.lean
```

## Boundary

This is measure bookkeeping only.  It does not prove the theta-side weighted
identity, the a.e. density bound, source-image coverage, determinant/raw Haar
transport, exact source/product-coordinate measure transport, original-prior
transport, normal crossings, pole order, or RLCT extraction.

For the Aoyagi p.13 program, the remaining mathematical input is still a real
source/product-coordinate measure identity or domination for the actual chart
and density.  This bridge only makes that input usable once supplied.

## Verification

Focused Lean checks, focused module builds, full local `lake build DLNFibre`,
`scripts/sorries`, `git diff --check`, touched-file marker scan, and direct
axiom probes passed.  The three new declarations report:

```text
[propext, Classical.choice, Quot.sound]
```
