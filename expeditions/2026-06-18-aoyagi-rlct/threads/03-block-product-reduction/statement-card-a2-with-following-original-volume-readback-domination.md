# Statement card - A2 with-following original-volume readback domination

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadback.lean
```

Name:

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource
```

## Claim

After one local shrink in the enlarged Case 2 passive-theta chart, a supplied
raw-pushforward equality to raw Haar on the raw-order source-recursive chart
implies readback a.e. measurability and readback domination for the restricted
original edge-family volume on every measurable p.13 chart piece contained in
the actual with-following source-chart image.

The conclusion is:

```text
AEMeasurable readback (originalVolume.restrict chartPiece)
Measure.map readback (originalVolume.restrict chartPiece)
  <= D • thetaReference.restrict G,
```

where

```text
D = ((cHaar^-1 : NNReal) : ENNReal) * 1.
```

## Proved

Lean proves this by composing:

- the with-following source-chart left-inverse/injectivity/continuity package;
- the with-following original-volume/source-reference domination theorem;
- the generic readback-domination handoff for a measure dominated by a source
  reference whose readback is dominated by the theta reference.

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
no p.13 source-image coverage theorem, no original-prior/source-prior
transport, no density lower-bound removal, no normal crossings, no pole order,
and no RLCT extraction.

## Status

Focused elaboration, focused module build, full local `lake build DLNFibre`,
no-sorry audit, whitespace check, touched-file marker scan, and direct axiom
probe passed.  The theorem reports `[propext, Classical.choice, Quot.sound]`.
Xhigh reviewer `Laplace the 2nd` passed after the reproduction wording was
sharpened to say image measurability is re-established on the smaller open
set.
