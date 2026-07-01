# Reproduction - A2 p.13 Formal Source-reference Readback Handoff

Date: 2026-07-01.

Status: pen-and-paper check before Lean.  This is elementary measure
bookkeeping after the p.13 formal-product measure has been named.

## Question

The original-prior finite-integral bridge needs the formal p.13 chart-piece
measure `muP13` to satisfy

```text
AEMeasurable readback muP13
Measure.map readback muP13 <= Cformal • thetaRef.
```

A more geometric target is often easier to state as domination by a
source-image reference measure:

```text
muP13 <= Cformal • sourceRef,
```

where `readback` is already known to pull `sourceRef` back to `thetaRef`:

```text
AEMeasurable readback sourceRef
Measure.map readback sourceRef = thetaRef.
```

Can these source-reference facts supply the formal readback assumptions?

## Calculation

From

```text
muP13 <= Cformal • sourceRef
```

we get absolute continuity `muP13 << sourceRef`.  Therefore
`AEMeasurable readback sourceRef` implies `AEMeasurable readback muP13`.

Mapping scalar domination by an a.e. measurable map gives

```text
Measure.map readback muP13
  <= Cformal • Measure.map readback sourceRef.
```

Using the supplied pullback identity for `sourceRef`, this becomes

```text
Measure.map readback muP13 <= Cformal • thetaRef.
```

No source-image equality or domination is proved here; it is a hypothesis.

## Lean Target

Add a generic helper to:

```text
lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
```

```text
readback_aemeasurable_and_map_le_smul_of_le_smul_source_measure
```

and a p.13 wrapper to:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13SourceMeasureBridge.lean
```

```text
map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_readback_le_smul_of_le_smul_sourceMeasure
```

## Kill Conditions

- If the theorem proves or suggests `muP13 <= Cformal • sourceRef`, it
  overclaims.
- If it identifies `sourceRef` with the passive-theta source image, it
  overclaims.
- If it proves p.13/passive-theta source coverage, chart-image equality,
  normal crossings, pole order, or RLCT extraction, it overclaims.
