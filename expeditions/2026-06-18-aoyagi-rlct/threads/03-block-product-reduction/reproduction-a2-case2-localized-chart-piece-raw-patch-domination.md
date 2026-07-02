# A2 reproduction: localized p.13 chart-piece raw patch domination

Date: 2026-07-02

## Claim

Fix the with-following Case 2 passive-theta source chart.  Let

```text
rawChart =
  paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
rawSourceSet =
  topologyTupleRawOrderSourceRecursiveDetChartSet
```

and let `chartPiece` be a measurable p.13 edge-family chart piece.  The correct
raw localization for this chart piece is

```text
rawPatch = rawSourceSet inter rawChart^{-1}(chartPiece).
```

More generally, any patch `P` satisfying

```text
P subset rawSourceSet,
rawPatch subset P
```

is sufficient.  If

```text
rawHaar.restrict P <= D * Measure.map rawMap (thetaReference.restrict V),
```

then the p.13 formal-product measure restricted to `chartPiece` is dominated by
`D` times the with-following source reference.

## Reproduction

The existing p.13 formal-product identity gives

```text
formalProductMeasure =
  (Measure.map rawChart (rawHaar.restrict rawSourceSet)).restrict p13SourceSet.
```

If `chartPiece subset p13SourceSet`, then

```text
formalProductMeasure.restrict chartPiece =
  (Measure.map rawChart (rawHaar.restrict rawSourceSet)).restrict chartPiece.
```

Since `chartPiece` is measurable and `rawChart` is a.e. measurable on
`rawHaar.restrict rawSourceSet`,

```text
(Measure.map rawChart (rawHaar.restrict rawSourceSet)).restrict chartPiece
= Measure.map rawChart
    ((rawHaar.restrict rawSourceSet).restrict (rawChart^{-1}(chartPiece))).
```

The inner restriction is exactly the chart-piece raw patch:

```text
(rawHaar.restrict rawSourceSet).restrict (rawChart^{-1}(chartPiece))
= rawHaar.restrict (rawSourceSet inter rawChart^{-1}(chartPiece)).
```

Thus

```text
formalProductMeasure.restrict chartPiece
<= Measure.map rawChart (rawHaar.restrict P)
```

whenever `rawPatch subset P`.  Pushing the supplied domination through
`rawChart`, using a.e. measurability on the theta raw image, gives

```text
Measure.map rawChart (rawHaar.restrict P)
<= D * Measure.map rawChart (Measure.map rawMap (thetaReference.restrict V)).
```

The two-stage source-chart identity rewrites the target as

```text
Measure.map sourceChart (thetaReference.restrict V).
```

The original-volume bridge then applies the established p.13 inverse Haar
scalar conversion, and the readback bridge applies the existing same-shrink
left-inverse/readback package.

## Lean landing

Implemented in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaFormalProductSourceReference.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeBridge.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadback.lean
```

New theorem sockets:

```text
exists_open_subset_formalProductMeasure_restrict_chartPiece_le_smul_sourceReference_of_restrict_patch_le_smul_case2PassiveThetaWithFollowingFactor_rawMap
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceReference_of_restrict_patch_le_smul_case2PassiveThetaWithFollowingFactor_rawMap
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_restrict_patch_le_smul_case2PassiveThetaWithFollowingFactor_rawMap
```

## Kill conditions checked

- Patch domination on an arbitrary raw patch is insufficient unless the patch
  contains `rawSourceSet inter rawChart^{-1}(chartPiece)`.
- The proof needs `MeasurableSet chartPiece`; omitting it would overstate the
  clean measure-transport route through `Measure.restrict_map_of_aemeasurable`.
- The localized identity is only after restricting the target to `chartPiece`;
  it is not an equality between the whole formal-product measure and the
  raw-patch pushforward.
- This step proves no determinant-Haar transport, source-density lower bound,
  original-prior transport, coverage, normal crossings, pole order, or RLCT
  extraction.
