# Review - A2 with-following original-volume source-image inverse-Haar density

Date: 2026-07-02.

Reviewer: Galileo the 2nd, xhigh read-only review.

## Result

No findings.

## Checks

The reviewer checked the p.13 bridge:

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_eq_withDensity_invHaar_sourceReference_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource
```

and the source-image wrapper:

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_eq_withDensity_invHaar_sourceImageReference_same_shrink_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource
```

The review confirmed that:

- the statements keep exact raw-pushforward as an explicit hypothesis;
- the proof mirrors the existing non-following inverse-Haar calculation;
- the with-following raw-order/source-chart bridge is used with the correct
  local hypotheses;
- the source-image wrapper shrinks through the existing with-following p.13
  source-image support theorem and re-derives readback, injectivity,
  continuity, measurable image, and p.13 support for the final shrink;
- the docs state the calculation and boundary accurately.

## Verification

The reviewer ran:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeBridge.lean
```

and it passed.  The controller additionally ran focused and full local builds,
the sorry gate, whitespace check, touched Lean-file forbidden-marker scan, and
direct axiom probes.

## Boundary

No determinant-Haar transport, raw-Haar transport, source-prior/original-prior
transport, arbitrary source-density positivity, global source-image coverage,
source-rank coverage, normal crossings, pole order, or RLCT extraction is
claimed.
