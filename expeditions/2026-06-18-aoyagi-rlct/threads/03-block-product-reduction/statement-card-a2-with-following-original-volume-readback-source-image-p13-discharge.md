# Statement card - A2 with-following original-volume readback with p.13 support discharged

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadback.lean
```

Name:

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource_of_chartPiece_subset_sourceImage
```

The exported constant is under:

```text
DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData
```

## Claim

After one local shrink, a supplied with-following raw-pushforward equality
implies readback a.e. measurability and readback domination for every
measurable chart piece contained in the actual local source-chart image.  The
caller no longer supplies a separate `chartPiece subset p13SourceSet`
hypothesis.

The conclusion is:

```text
AEMeasurable readback (originalVolume.restrict chartPiece)
Measure.map readback (originalVolume.restrict chartPiece)
  <= D • thetaReference.restrict G,
```

where:

```text
D = ((cHaar^-1 : NNReal) : ENNReal) * 1.
```

## Proved

Lean first obtains a local support shrink `V0` with:

```text
sourceChart '' V0 subset p13SourceSet.
```

It then applies the existing with-following readback domination theorem inside
`V0`, producing `V subset V0`.  On `V`, source-image membership implies p.13
membership, so the old p.13 chart-piece hypothesis is discharged internally.

The old readback theorem initially returns domination by
`thetaReference.restrict V0`.  Since `V0 subset G`, Lean composes this with:

```text
thetaReference.restrict V0 <= thetaReference.restrict G
```

using the existing scalar-domination composition helper, giving the stated
target `thetaReference.restrict G`.

## Assumed

The theorem still assumes:

- `MeasurableSet chartPiece`;
- `chartPiece subset sourceChart '' V`;
- `Measure.map rawMap (thetaReference.restrict V) = rawHaar.restrict rawSourceSet`;
- the local det-sector and selected-pivot-nonzero hypotheses at the base point.

## Cited

None.

## Deferred

No raw Haar transport, no determinant-chart Haar transport, no source-image
coverage beyond the local chart image, no source-prior or original-prior
transport, no density lower-bound removal, no normal crossings, no pole order,
and no RLCT extraction.

## Status

Focused module build, full local `lake build DLNFibre`, no-sorry audit,
whitespace check, touched-file marker scan, and direct axiom probe passed.  The
theorem reports `[propext, Classical.choice, Quot.sound]`.  Xhigh reviewer
`Avicenna the 2nd` passed with no findings.
