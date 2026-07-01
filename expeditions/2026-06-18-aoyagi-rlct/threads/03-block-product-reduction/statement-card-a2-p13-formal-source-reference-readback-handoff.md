# Statement Card - A2 p.13 Formal Source-reference Readback Handoff

## Claim

A source-reference domination of the formal-product p.13 chart-piece measure
supplies the readback measurability and domination hypotheses used by the
original-prior finite-integral bridge.

If

```text
AEMeasurable readback sourceRef
Measure.map readback sourceRef = thetaRef
muP13 <= Cformal • sourceRef,
```

then

```text
AEMeasurable readback muP13
Measure.map readback muP13 <= Cformal • thetaRef.
```

The p.13 wrapper specializes `muP13` to the formal-product raw-order p.13 chart
measure restricted to a supplied chart piece.

## Public Lean Names

```text
readback_aemeasurable_and_map_le_smul_of_le_smul_source_measure
map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_readback_le_smul_of_le_smul_sourceMeasure
```

## Inputs Used

- absolute continuity from scalar measure domination;
- `map_le_smul_map_of_le_smul_aemeasurable`;
- the supplied identity `Measure.map readback sourceRef = thetaRef`.

## Nonclaims

This theorem does not prove formal p.13 domination by a passive source-image
measure, identify the source reference, prove source coverage, chart-image
equality, source-rank coverage, Haar scalar normalization, normal crossings,
pole order, or RLCT extraction.
