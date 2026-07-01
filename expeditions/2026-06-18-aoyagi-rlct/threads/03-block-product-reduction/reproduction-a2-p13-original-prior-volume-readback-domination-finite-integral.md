# Reproduction - A2 p.13 Original-prior Volume-readback Domination Finite Integral

Date: 2026-07-01.

Status: pen-and-paper check completed before Lean; Lean theorem implemented.

## Question

The previous p.13 wrapper accepts an abstract source reference `sourceRef` and
requires both

```text
Measure.map readback sourceRef <= Csource • coordinateSourceMeasure.restrict W
(originalEdgeFamilyVolume b).restrict chartPiece <= D • sourceRef.
```

Can we specialize this to the concrete source reference

```text
sourceRef := (originalEdgeFamilyVolume b).restrict chartPiece
```

so that the only remaining measure-comparison input is the readback domination
of the restricted original edge-family volume itself?

## Calculation

Set

```text
volumePiece := (originalEdgeFamilyVolume b).restrict chartPiece.
sourceRef := volumePiece.
D := 1.
```

The source-reference theorem's restricted-volume hypothesis becomes

```text
volumePiece <= 1 • volumePiece,
```

which is just reflexivity after `1 • volumePiece = volumePiece`.

If the caller supplies

```text
AEMeasurable readback volumePiece,
Measure.map readback volumePiece <= Csource • coordinateSourceMeasure.restrict W,
Csource < infinity,
```

then the previous source-reference domination wrapper applies with

```text
Cformal = ((cHaar : ENNReal) * 1) * Csource.
```

The exact scalar does not need to be normalized to `cHaar * Csource`; keeping
the theorem as an instantiation of the previous wrapper avoids asserting any
Haar scalar cancellation.  Finiteness follows from finiteness of `cHaar :
ENNReal`, `1 < infinity`, and `Csource < infinity`.

## Lean Target

Add to:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13ReadbackFiniteIntegral.lean
```

Target:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_originalVolume_readback_le_smul_coordinateSourceMeasure_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

It should be a thin consumer of:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_originalVolumeSourceReference_readback_le_smul_coordinateSourceMeasure_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

## Kill Conditions

- If the theorem claims readback domination of the restricted original volume,
  it overstates this step; that domination remains an explicit hypothesis.
- If it constructs or identifies a passive-theta source image, it overclaims.
- If it claims source coverage, chart-image equality, Haar scalar
  normalization, normal crossings, pole order, or RLCT extraction, it
  overclaims.
