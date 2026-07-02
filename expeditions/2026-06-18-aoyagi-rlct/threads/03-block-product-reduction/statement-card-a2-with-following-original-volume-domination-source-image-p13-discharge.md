# Statement card - A2 with-following original-volume domination with p.13 support discharged

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeBridge.lean
```

Name:

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceReference_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource_of_chartPiece_subset_sourceImage
```

The exported constant is under:

```text
DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData
```

## Claim

After one local shrink, a supplied with-following raw-pushforward equality
implies original edge-family volume domination for every measurable chart piece
contained in the actual local source-chart image.  Unlike the previous
conditional theorem, the caller no longer supplies a separate
`chartPiece subset p13SourceSet` hypothesis.

The conclusion is:

```text
originalVolume.restrict chartPiece
  <= ((((cHaar^-1 : NNReal) : ENNReal) * 1) • sourceRef),
```

where:

```text
sourceRef = Measure.map sourceChart (thetaReference.restrict V).
```

## Proved

Lean first obtains a local support shrink `V0` with:

```text
sourceChart '' V0 subset p13SourceSet.
```

It then applies the existing with-following original-volume domination theorem
inside `V0`, producing a smaller open `V subset V0`.  For any
`chartPiece subset sourceChart '' V`, the p.13 support condition follows by
composition:

```text
chartPiece subset sourceChart '' V subset sourceChart '' V0 subset p13SourceSet.
```

The old domination theorem is then applied with this derived containment.

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
