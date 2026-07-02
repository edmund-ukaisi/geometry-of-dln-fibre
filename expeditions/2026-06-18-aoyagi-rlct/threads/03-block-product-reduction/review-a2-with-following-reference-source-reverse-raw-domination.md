# Review - A2 with-following reference-source reverse raw domination

Date: 2026-07-02.

Reviewer: `Kant the 2nd`, xhigh read-only subagent.

## Scope

Reviewed the Lean declaration:

```text
exists_open_subset_rawHaar_restrict_rawSource_le_smul_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_coordinateSourceMeasure_restrict_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower
```

and the reproduction note:

```text
reproduction-a2-with-following-reference-source-reverse-raw-domination.md
```

## Findings

None.

## PASS

The reviewer checked that the theorem keeps determinant-side domination and
the `sourceDensity` lower bound explicit, specializes only the source measure
to `case2PassiveThetaWithFollowingFactorReferenceSourceMeasure`, and uses the
lower-density adapter without hiding endpoint-reference-image-to-Haar
transport or normalization.

The theorem target is the raw image of `coordinateSourceMeasure`, not the
unweighted reference raw-order image.  The lower bound is correctly measured
with respect to `baseJ.restrict V`, so no extra absolute-continuity conversion
is hidden.

Boundary language was judged accurate: no determinant-Haar transport, exact
raw-Haar pushforward, source-prior/original-prior transport, coverage, normal
crossings, pole order, or RLCT extraction is claimed.
