# Review - A2 Case 2 source-stratum-supported open restriction

Date: 2026-06-29.

Reviewer: xhigh `Ramanujan the 2nd`.

Status: PASS.

## Findings

No findings.

## Checks

The reviewer checked:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure_restrict_open_of_sourceRankSupport
```

The theorem is a downstream finite-integral corollary.  It first calls the
existing source-stratum-bound chart-produced finite-integral theorem, then only
rewrites the measure restriction.

The support hypotheses are explicit and not weakened:

```text
finrank range(paperTotalMap W2 B2) = r,
r + card tau = rEdge 0,
forall yNext,
  r + rank(case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext) = rEdge 1.
```

They are consumed by the banked support theorem
`measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_restrict_sourceRankStratum_eq_self`.
That support theorem is itself only chart-image support in the source stratum,
not coverage.

The measure rewrite is correct: `Measure.restrict_restrict` with the
measurable open set `U` gives

```text
(mu.restrict sourceStratum).restrict U = mu.restrict (U intersect sourceStratum),
```

and `mu.restrict sourceStratum = mu` replaces the right-hand measure by
`mu.restrict U`.

## Verification

The reviewer ran:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
```

It passed.

## Boundary

The theorem does not assert source-rank coverage, selected-entry image
equality, exact-rank openness, source-prior or Jacobian transport, analytic
atlas construction, normal crossings, pole order, RLCT, or a numerical
successor selected-entry matrix rank.
