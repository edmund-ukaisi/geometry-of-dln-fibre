# Reproduction - A2 p.13 Original-prior Volume-source-reference Domination Finite Integral

Date: 2026-07-01.

Status: pen-and-paper check before Lean.

## Question

The previous finite-integral wrapper requires an exact source-reference
readback identity:

```text
Measure.map readback sourceRef = coordinateSourceMeasure.restrict W.
```

For later local shrinking, the natural source reference may pull back only to a
measure dominated by the returned coordinate source measure, for example when a
smaller theta chart `V` satisfies `V ⊆ W`:

```text
Measure.map readback sourceRef <= Csource • coordinateSourceMeasure.restrict W.
```

Can the p.13 original-prior finite-integral theorem consume this dominated
source-reference pullback, with `Csource < infinity`, without changing any
geometric assumptions?

## Calculation

Assume on a measurable p.13 chart piece:

```text
(originalEdgeFamilyVolume b).restrict chartPiece <= D • sourceRef.
```

The existing formal-volume source-reference bridge gives

```text
muP13 <= ((cHaar : ENNReal) * D) • sourceRef.
```

If additionally

```text
AEMeasurable readback sourceRef,
Measure.map readback sourceRef <= Csource • coordinateSourceMeasure.restrict W,
```

then the generic readback handoff gives

```text
AEMeasurable readback muP13,
Measure.map readback muP13
  <= (((cHaar : ENNReal) * D) * Csource) • coordinateSourceMeasure.restrict W.
```

The old finite-integral theorem applies with

```text
Cformal := (((cHaar : ENNReal) * D) * Csource).
```

This scalar is finite when `D < infinity` and `Csource < infinity`, because
`cHaar : NNReal` is finite as an `ENNReal` scalar.

## Lean Target

Add to:

```text
lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13SourceMeasureBridge.lean
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13ReadbackFiniteIntegral.lean
```

Targets:

```text
readback_aemeasurable_and_map_le_smul_of_le_smul_source_measure_le
map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_readback_le_smul_of_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceMeasure_le
exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_originalVolumeSourceReference_readback_le_smul_coordinateSourceMeasure_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

## Kill Conditions

- If the theorem claims an exact pullback identity, it overstates this variant.
- If it proves the restricted-volume domination, it overclaims.
- If it identifies `sourceRef` with a passive-theta source image or coordinate
  measure, it overclaims.
- If it proves source coverage, chart-image equality, Haar scalar
  normalization, normal crossings, pole order, or RLCT extraction, it
  overclaims.
