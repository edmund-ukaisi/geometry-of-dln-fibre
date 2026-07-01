# Reproduction - A2 p.13 Original-prior Volume-source-reference Readback

Date: 2026-07-01.

Status: pen-and-paper check before Lean.

## Question

The original-prior p.13 readback bridge currently consumes readback domination
of the formal p.13 measure `muP13`.  The previous bridge reduces that formal
domination to a source-reference domination of restricted original edge-family
volume.

Can we package the composition so the original-prior readback theorem consumes
only:

```text
originalEdgeFamilyVolume.restrict chartPiece <= D • sourceRef,
AEMeasurable readback sourceRef,
Measure.map readback sourceRef = thetaRef?
```

## Calculation

The existing bounded-prior bridge gives

```text
originalPriorPiece <= alpha • muP13
```

where

```text
alpha = ENNReal.ofReal K * ((c^-1 : NNReal) : ENNReal).
```

The formal-volume source-reference bridge gives

```text
muP13 <= ((c : ENNReal) * D) • sourceRef,
```

and the supplied readback identity for `sourceRef` gives

```text
AEMeasurable readback muP13,
Measure.map readback muP13 <= ((c : ENNReal) * D) • thetaRef.
```

Composing the original-prior readback bridge with this formal readback result
yields

```text
AEMeasurable readback originalPriorPiece,
Measure.map readback originalPriorPiece
  <= (alpha * ((c : ENNReal) * D)) • thetaRef.
```

If `D < ∞`, then the displayed scalar is finite because `ENNReal.ofReal K`,
`(c^-1 : NNReal)`, and `c : NNReal` are all finite ENNReal scalars.

## Lean Target

Add to:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13SourceMeasureBridge.lean
```

```text
originalEdgeFamilyPrior_map_readback_restrict_chartPiece_le_smul_of_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceMeasure
originalEdgeFamilyPrior_p13VolumeReadbackDominationScalar_lt_top
```

## Kill Conditions

- If the theorem proves the restricted-volume domination, it overclaims.
- If it identifies `sourceRef` or `thetaRef` with a passive-theta source image
  or coordinate measure, it overclaims.
- If it proves source coverage, chart-image equality, scalar cancellation,
  normal crossings, pole order, or RLCT extraction, it overclaims.
