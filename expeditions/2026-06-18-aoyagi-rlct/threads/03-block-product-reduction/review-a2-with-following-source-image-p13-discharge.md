# Review - A2 with-following source-image p.13 discharge

Date: 2026-07-02.

Reviewer: `Avicenna the 2nd`, xhigh read-only subagent.

## Scope

Reviewed the three new Lean declarations:

```text
exists_open_subset_measurableSet_case2PassiveThetaWithFollowingFactorEndpointSourceChart_image_subset_p13SourceEdgeFamilySet
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceReference_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource_of_chartPiece_subset_sourceImage
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource_of_chartPiece_subset_sourceImage
```

and the three reproduction notes:

```text
reproduction-a2-with-following-source-chart-p13-support.md
reproduction-a2-with-following-original-volume-domination-source-image-p13-discharge.md
reproduction-a2-with-following-original-volume-readback-source-image-p13-discharge.md
```

## Findings

None.

## PASS

The reviewer checked that the source-image support theorem is one-way only,
that the two downstream wrappers honestly shrink through `V0`, and that
`chartPiece subset p13SourceSet` is derived only from
`chartPiece subset sourceChart '' V` plus local image support.

The reviewer also checked the readback wrapper's final domination target:
`thetaReference.restrict G` is justified by composing the old
`thetaReference.restrict V0` bound with `V0 subset G`.

Boundary language was judged accurate: no p.13 coverage, Haar transport,
source-prior/original-prior transport, normal crossings, pole order, or RLCT is
claimed.
