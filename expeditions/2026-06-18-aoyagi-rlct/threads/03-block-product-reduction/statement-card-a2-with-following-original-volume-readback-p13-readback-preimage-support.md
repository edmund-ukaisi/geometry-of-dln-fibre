# Statement card - A2 with-following original-volume readback on p.13/readback-preimage support

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadback.lean
```

Name:

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource_of_chartPiece_subset_p13SourceSet_readback_preimage
```

The exported constant is under:

```text
DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData
```

## Claim

After a local shrink, the with-following original-volume readback domination
can consume chart pieces satisfying p.13 support and readback-preimage support:

```text
chartPiece subset p13SourceSet
chartPiece subset readback^{-1}(V).
```

The theorem exposes the local equality:

```text
sourceChart '' V = p13SourceSet inter readback^{-1}(V).
```

Thus the caller no longer needs to separately prove
`chartPiece subset sourceChart '' V`.

## Proved

Lean first obtains a local p.13/readback image equality on `W`, then applies
the existing original-volume readback bridge inside `W`, yielding `V subset W`.
The generic image-shrink lemma transfers the equality to `V`.  The support
conversion lemma then derives:

```text
chartPiece subset sourceChart '' V.
```

The existing readback bridge gives readback a.e. measurability and domination
over `thetaReference.restrict W`; restriction monotonicity upgrades the target
to `thetaReference.restrict G`.

## Assumed

The theorem still assumes:

- `MeasurableSet chartPiece`;
- `chartPiece subset p13SourceSet`;
- `chartPiece subset readback^{-1}(V)`;
- the raw-pushforward equality
  `Measure.map rawMap (thetaReference.restrict V) =
  rawHaar.restrict rawSourceSet`;
- the local det-sector and selected-pivot-nonzero hypotheses at the base point.

## Cited

None.

## Deferred

No raw Haar transport, no determinant-chart Haar transport, no source-image
coverage beyond the local chart image, no source-rank coverage, no source-prior
or original-prior transport, no density lower-bound removal, no normal
crossings, no pole order, and no RLCT extraction.

## Status

Implemented and proved.  Focused `lake env lean`, focused module build, no-sorry
audit, whitespace check, and direct axiom probe passed.  The declaration reports
only `[propext, Classical.choice, Quot.sound]`.  Xhigh reviewer
`Chandrasekhar the 2nd` passed after this status line was updated.
