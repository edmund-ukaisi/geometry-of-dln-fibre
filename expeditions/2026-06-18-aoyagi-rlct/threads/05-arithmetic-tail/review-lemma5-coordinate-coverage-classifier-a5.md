# Review - Lemma 5 coordinate coverage classifier

Reviewers: Arendt, xhigh-effort subagent; James, xhigh-effort subagent.
Date: 2026-06-21.

## Verdict

No blocking mathematical or source-fidelity findings after the compile fixes
and classifier-map naming hardening.

## Checks

- The finite-set identity
  `finset_image_filter_value_ne_eq_erase_image` is correct and does not require
  injectivity of the value map.
- `AoyagiLemma5SuppliedNonbaseFamily.ofCoordinateValueCoverage` is supplied-data
  assembly: it assumes full coordinate image coverage, base-value membership,
  per-coordinate value injectivity, and cross-coordinate disjointness, then
  restricts to the nonbase subfamily by filtering out the supplied base value.
- `AoyagiLemma5SuppliedNonbaseFamily.countDatumClassifierOfBranchCoord` proves
  only the `mapsTo` field of `AoyagiLemma5CountDatumClassifier` from the
  supplied branch-coordinate equation and `F.value_image`.
- Injectivity of the tagged classifier is still explicit supplied data.  This
  avoids treating Aoyagi's Case 1(2) `J`-increase sentence as a proof of
  nonduplication or back-to-label coverage.

## Follow-Up Delta

James reviewed an earlier draft and found local Lean elaboration failures in
the image/erase helper, filtered `Set.InjOn` memberships, namespace placement,
and `Sigma.mk` inference.  Those were fixed before the focused and full builds.

Both reviewers recommended or accepted naming the classifier map to avoid
duplicating a dependent-pair lambda in the injectivity hypothesis.  The final
slice adds:

```text
AoyagiLemma5SuppliedNonbaseFamily.countDatumOfBranchCoord
```

and makes `countDatumClassifierOfBranchCoord` take injectivity of this named
map.

## Boundary

The slice does not construct Aoyagi's displayed source family, prove raw
coordinate coverage from equations `(3)`, `(4)`, `(5)`, prove branch-coordinate
uniqueness from the source, prove Case 1(2) classifier injectivity, prove
back-to-label coverage, identify pole order, prove normal crossings, or
extract RLCT data.

## Verification

Arendt ran the focused Lean file, the placeholder scanner, and `git diff
--check` on the Lean/reproduction files; all passed.  The controller then ran
the focused Lean file, module build, full `DLNFibre` build, placeholder scan,
and `git diff --check`.
