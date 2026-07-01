# Statement Card - A2 p.13 Formal-volume Source-reference Domination

## Claim

The formal-product p.13 chart-piece measure is dominated by a source reference
measure once the restricted original edge-family volume on the same chart piece
is dominated by that source reference.

If

```text
originalEdgeFamilyVolume.restrict chartPiece <= D • sourceRef,
```

then, using the already-proved p.13 equality

```text
muP13 = c • originalEdgeFamilyVolume.restrict chartPiece,
```

one gets

```text
muP13 <= ((c : ENNReal) * D) • sourceRef.
```

## Public Lean Names

```text
map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_le_smul_sourceMeasure_of_originalEdgeFamilyVolume_restrict_chartPiece_le_smul
map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_readback_le_smul_of_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceMeasure
```

## Inputs Used

- the existing formal-product p.13 chart-piece measure equality;
- the supplied domination of restricted original edge-family volume;
- scalar-measure domination composition;
- for the readback wrapper, the supplied source-reference readback identity.

## Nonclaims

This theorem does not prove the restricted-volume domination, identify the
source reference, prove passive-theta source-image equality, prove source
coverage, chart-image equality, Haar scalar normalization, normal crossings,
pole order, or RLCT extraction.
