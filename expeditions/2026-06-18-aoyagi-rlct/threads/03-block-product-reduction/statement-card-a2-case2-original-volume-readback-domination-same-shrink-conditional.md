# Statement Card - A2 Case 2 original-volume readback domination same-shrink conditional

## Claim

The conditional original-volume/source-image bridge can be composed with the
source-chart inverse/readback domination lemma on the same local shrink.

Expected public Lean name:

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_case2PassiveTheta_rawMap_eq_restrict_rawSource
```

## Statement Shape

For an ambient open `G` with `z0 in G`, Lean returns `V subset G` such that:

- `readback (sourceChart z) = z` for `z in V`;
- `Set.InjOn sourceChart V`;
- `ContinuousOn sourceChart V`;
- `MeasurableSet (sourceChart '' V)`;
- `sourceChart '' V subset p13SourceSet`.

For any theta-reference measure, raw Haar measure, and measurable
`chartPiece subset sourceChart '' V`, the explicit hypothesis

```text
Measure.map rawMap (thetaReference.restrict V) =
  rawHaar.restrict rawSourceSet
```

implies:

```text
AEMeasurable readback (originalVolume.restrict chartPiece)
```

and

```text
Measure.map readback (originalVolume.restrict chartPiece)
  <= invHaarScalar • thetaReference.restrict G.
```

Here `invHaarScalar` is the inverse of the existing p.13 raw-order/original
volume Haar scalar.

## Inputs Used

- `exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_eq_withDensity_invHaar_sourceImageReference_same_shrink_of_case2PassiveTheta_rawMap_eq_restrict_rawSource`;
- `originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_coordinateSourceMeasure_restrict_of_sourceImageReference_eq_withDensity_of_continuousOn_injOn`.

## Nonclaims

No raw-Haar pushforward is proved.  No determinant-chart Haar transport,
full source-image coverage, source-rank coverage, original source-prior
transport, scalar normalization, normal crossings, pole order, or RLCT
extraction is claimed.

## Verification

Focused elaboration, focused module build, full local `lake build DLNFibre`,
`lean/scripts/sorries`, `git diff --check`, and direct axiom probe passed.
The direct axiom probe reported only
`[propext, Classical.choice, Quot.sound]`.
