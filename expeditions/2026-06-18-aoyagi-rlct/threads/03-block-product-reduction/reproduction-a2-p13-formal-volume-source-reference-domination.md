# Reproduction - A2 p.13 Formal-volume Source-reference Domination

Date: 2026-07-01.

Status: pen-and-paper check before Lean.

## Question

The previous source-reference readback handoff reduces the downstream p.13
formal readback assumptions to

```text
muP13 <= Cformal • sourceRef.
```

The p.13 source-measure bridge already proves the chart-piece equality

```text
muP13 = c • originalEdgeFamilyVolume.restrict chartPiece,
```

where `c` is the tuple-side Haar scalar.  If a later source-image argument can
show

```text
originalEdgeFamilyVolume.restrict chartPiece <= D • sourceRef,
```

then the formal domination follows with scalar `c * D`.

## Calculation

By the existing p.13 chart-piece measure comparison,

```text
muP13 = c • volumePiece.
```

The supplied source-reference domination is

```text
volumePiece <= D • sourceRef.
```

Monotonicity of scalar multiplication and associativity of measure scaling give

```text
muP13 <= c • volumePiece
      <= c • (D • sourceRef)
       = (c * D) • sourceRef.
```

Here `c` is coerced from the positive Haar `NNReal` scalar to `ENNReal` for the
measure-scalar calculation.  No finiteness of `D` or `c * D` is claimed by this
bridge.

## Lean Target

Add a p.13 wrapper to:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13SourceMeasureBridge.lean
```

```text
map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_le_smul_sourceMeasure_of_originalEdgeFamilyVolume_restrict_chartPiece_le_smul
map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_readback_le_smul_of_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceMeasure
```

The second theorem composes the first theorem with the generic readback handoff:
if `AEMeasurable readback sourceRef` and `Measure.map readback sourceRef =
thetaRef`, then the formal p.13 chart-piece measure is a.e.-measurable for
`readback` and its readback pushforward is dominated by `((c : ENNReal) * D) •
thetaRef`.

## Kill Conditions

- If the theorem proves `volumePiece <= D • sourceRef`, it overclaims.
- If it identifies `sourceRef` with a passive-theta source image, it overclaims.
- If it proves source coverage, chart-image equality, normal crossings, pole
  order, or RLCT extraction, it overclaims.
