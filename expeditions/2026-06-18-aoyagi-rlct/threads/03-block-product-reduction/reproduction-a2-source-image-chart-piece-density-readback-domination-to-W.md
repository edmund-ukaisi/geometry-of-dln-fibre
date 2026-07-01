# Reproduction - A2 Source-image Chart-piece Density Readback Domination to W

Date: 2026-07-01.

Status: pen-and-paper check completed before Lean; Lean implementation and
verification passed.

## Question

The chart-piece bounded-density pullback gives domination by
`thetaReference.restrict V`.  In the Aoyagi finite-integral sockets, the
coordinate source measure is usually restricted to the larger open set `W`,
with a returned containment

```text
V subset W.
```

Can the same density identity also provide the readback a.e.-measurability and
domination hypotheses needed by wrappers whose target is
`thetaReference.restrict W`?

## Calculation

Let

```text
sourceBase = Measure.map sourceChart (thetaReference.restrict V).
```

Assume

```text
externalMeasure.restrict chartPiece =
  (sourceBase.withDensity density).restrict chartPiece,
density <= c  sourceBase.restrict chartPiece-a.e.
```

The with-density bound gives

```text
(sourceBase.withDensity density).restrict chartPiece <= c • sourceBase.
```

Using the equality,

```text
externalMeasure.restrict chartPiece << sourceBase.
```

Therefore any `AEMeasurable readback sourceBase` transfers to

```text
AEMeasurable readback (externalMeasure.restrict chartPiece).
```

The already proved chart-piece pullback gives

```text
Measure.map readback (externalMeasure.restrict chartPiece) <=
  c • thetaReference.restrict V.
```

Finally, from `V subset W`,

```text
thetaReference.restrict V <= thetaReference.restrict W,
```

and scalar monotonicity gives

```text
c • thetaReference.restrict V <= c • thetaReference.restrict W.
```

Hence

```text
AEMeasurable readback (externalMeasure.restrict chartPiece)
Measure.map readback (externalMeasure.restrict chartPiece) <=
  c • thetaReference.restrict W.
```

For the p.13 original edge-family volume, set

```text
externalMeasure = originalEdgeFamilyVolume fixedBasis
thetaReference = coordinateSourceMeasure
```

and use the supplied local source-image chart data.

## Lean Target

Add generic helper lemmas to
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean`:

```text
aemeasurable_readback_and_measure_map_readback_restrict_piece_le_smul_restrict_superset_of_restrict_eq_withDensity

aemeasurable_readback_and_measure_map_readback_restrict_piece_le_smul_restrict_superset_of_restrict_eq_withDensity_of_continuousOn_injOn
```

Add the p.13 original-volume specialization to
`lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13ReadbackFiniteIntegral.lean`:

```text
originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_coordinateSourceMeasure_restrict_of_sourceImageReference_eq_withDensity_of_continuousOn_injOn
```

## Nonclaims

This does not prove the original/source density identity or density bound.  It
does not prove source-image coverage, source-rank coverage, Haar transport, a
Jacobian formula, normal crossings, pole order, or RLCT extraction.
