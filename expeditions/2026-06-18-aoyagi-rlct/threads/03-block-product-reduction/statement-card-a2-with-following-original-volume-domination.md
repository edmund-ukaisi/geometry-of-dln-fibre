# Statement card - A2 with-following original-volume domination

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeBridge.lean
```

Name:

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceReference_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource
```

## Claim

After one local shrink in the enlarged Case 2 passive-theta chart, a supplied
raw-pushforward equality to raw Haar on the raw-order source-recursive chart
implies domination of the restricted original edge-family volume on any
measurable p.13 chart piece contained in the actual with-following source-chart
image.

The bound is the inverse tuple-side Haar scalar times the constant density
bound `1`:

```text
originalVolume.restrict chartPiece
  <= ((((cHaar^-1 : NNReal) : ENNReal) * 1) • sourceRef),
```

where

```text
sourceRef = Measure.map sourceChart (thetaReference.restrict V).
```

## Proved

Lean proves the above domination by composing:

- the with-following constant-density formal-product/source-reference handoff
  under the supplied raw-pushforward equality;
- the p.13 bounded-density original-volume bridge.

## Assumed

The local theorem keeps explicit:

- `MeasurableSet chartPiece`;
- `chartPiece subset sourceChart '' V`;
- `chartPiece subset p13SourceSet`;
- `Measure.map rawMap (thetaReference.restrict V) = rawHaar.restrict rawSourceSet`;
- the local det-sector and selected-pivot-nonzero hypotheses at the base
  point.

## Cited

None.

## Deferred

No raw Haar transport theorem, no determinant-chart Haar transport,
no source-image coverage, no original-prior/source-prior transport, no density
lower-bound removal, no normal crossings, no pole order, and no RLCT
extraction.

## Status

Focused elaboration, focused module build, full local `lake build DLNFibre`,
full no-sorry audit, whitespace check, targeted marker scan, and direct axiom
probe passed.  The theorem reports `[propext, Classical.choice, Quot.sound]`.
