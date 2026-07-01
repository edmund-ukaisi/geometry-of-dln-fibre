# Statement Card - A2 Case 2 original-volume finite integral raw-pushforward conditional

## Claim

The direct original-volume p.13 finite-integral socket can be discharged on a
same-shrink source-image chart piece from the explicit raw-Haar raw-source
pushforward hypothesis.

Expected public Lean name:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_originalVolume_readback_invHaar_of_case2PassiveTheta_rawMap_eq_restrict_rawSource_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

## Statement Shape

After the standard loss lower-bound and finite-mass hypotheses, Lean returns:

- an ambient theta neighborhood `W`;
- a source-side neighborhood `U`;
- a same-shrink theta neighborhood `V subset W` with source-chart readback,
  injectivity, continuity, measurable image, and p.13 source-set containment.

For every measurable `chartPiece` satisfying:

```text
chartPiece subset U inter sourceStratum
chartPiece subset sourceChart '' V
Measure.map rawMap (coordinateSourceMeasure.restrict V) =
  m.restrict rawSourceSet
```

and every original-prior density bounded above on that chart piece, the p.13
regular-coordinate negative-power integral is finite.

## Inputs Used

- `exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_originalVolume_readback_le_smul_coordinateSourceMeasure_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds`;
- `exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_case2PassiveTheta_rawMap_eq_restrict_rawSource`.

## Nonclaims

No raw-Haar pushforward is proved.  No determinant-chart Haar transport,
source-image coverage, source-rank coverage, original source-prior transport,
scalar normalization, normal crossings, pole order, or RLCT extraction is
claimed.

## Verification

Focused elaboration, focused module build, full local `lake build DLNFibre`,
`lean/scripts/sorries`, `git diff --check`, and direct axiom probe passed.
The direct axiom probe reported only
`[propext, Classical.choice, Quot.sound]`.
