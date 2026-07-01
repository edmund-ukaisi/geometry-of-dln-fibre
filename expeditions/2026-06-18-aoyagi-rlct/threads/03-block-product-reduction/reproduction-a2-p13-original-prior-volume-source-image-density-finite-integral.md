# Reproduction - A2 p.13 Original-prior Volume Source-image Density Finite Integral

Date: 2026-07-01.

Status: pen-and-paper check completed before Lean; Lean theorem implemented and verified.

## Question

The current source-image finite-integral wrapper assumes the chart-piece
comparison

```text
originalVolume.restrict chartPiece <=
  D • Measure.map sourceChart (coordinateSourceMeasure.restrict V).
```

Can we replace this arbitrary domination hypothesis by the more structured
local density socket

```text
originalVolume.restrict chartPiece =
  ((Measure.map sourceChart (coordinateSourceMeasure.restrict V))
    .withDensity volumeDensity).restrict chartPiece

volumeDensity <= D
  a.e. for (Measure.map sourceChart (coordinateSourceMeasure.restrict V))
    .restrict chartPiece,
```

and recover the same finite-integral conclusion?

## Calculation

Let

```text
sourceRef := Measure.map sourceChart (coordinateSourceMeasure.restrict V).
```

Assume

```text
originalVolume.restrict chartPiece =
  (sourceRef.withDensity volumeDensity).restrict chartPiece
```

and

```text
volumeDensity E <= D
for sourceRef.restrict chartPiece-a.e. E.
```

The elementary measure lemma

```text
restrict_withDensity_le_smul_of_ae_le
```

gives

```text
(sourceRef.withDensity volumeDensity).restrict chartPiece <= D • sourceRef.
```

Rewriting by the supplied density identity gives

```text
originalVolume.restrict chartPiece <= D • sourceRef.
```

This is exactly the remaining measure comparison required by the previous
source-image finite-integral wrapper.  Thus the new wrapper is a direct
consumer of the previous theorem, with the arbitrary domination field replaced
by a density identity plus a local a.e. upper bound.

## Lean Target

Add to:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13ReadbackFiniteIntegral.lean
```

Target theorem:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_originalVolumeSourceImageReference_eq_withDensity_bounded_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

## Nonclaims

This does not prove the density identity for the original volume, prove the
density bound, identify a global passive-theta image, prove source coverage,
prove chart-image equality, normalize Haar scalars, construct normal crossings,
compute pole order, or extract an RLCT.
