# Statement Card - A2 p.13 Original-prior Volume-source-reference Readback

## Claim

A restricted-volume source-reference domination supplies the original-prior
readback domination used by downstream finite-integral sockets.

If

```text
originalEdgeFamilyVolume.restrict chartPiece <= D • sourceRef,
AEMeasurable readback sourceRef,
Measure.map readback sourceRef = thetaRef,
```

then the locally bounded original prior restricted to `chartPiece` is
a.e.-measurable for `readback` and its readback pushforward is dominated by

```text
(alpha * ((c : ENNReal) * D)) • thetaRef,
alpha = ENNReal.ofReal K * ((c^-1 : NNReal) : ENNReal).
```

The companion scalar lemma proves this scalar is finite when `D < ∞`.

## Public Lean Names

```text
originalEdgeFamilyPrior_map_readback_restrict_chartPiece_le_smul_of_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceMeasure
originalEdgeFamilyPrior_p13VolumeReadbackDominationScalar_lt_top
```

## Inputs Used

- the existing original-prior-to-formal-p.13 domination bridge;
- the formal-volume source-reference readback bridge;
- scalar-measure domination composition;
- ENNReal finiteness of `ofReal` and coerced `NNReal` scalars.

## Nonclaims

This theorem does not prove the restricted-volume domination, identify the
source reference or theta reference, prove passive-theta source-image equality,
prove source coverage, chart-image equality, Haar scalar normalization or
cancellation, normal crossings, pole order, or RLCT extraction.
