# A2 Case 2 source-stratum-supported open-restriction finite integral

## Lean statement

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure_restrict_open_of_sourceRankSupport
```

## Claim

For the endpoint-transported continuing Case 2 selected-entry chart-produced
measure, the source-stratum-bound finite-integral theorem can be stated over
`mu.restrict U` instead of `mu.restrict (U ∩ sourceStratum)` when the explicit
source-rank support equations are supplied:

```text
finrank range(paperTotalMap W2 B2) = r,
r + card tau = rEdge 0,
forall yNext,
  r + rank(case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext) = rEdge 1.
```

## Source and reproduction

The finite-integral input is the previously formalized p.13
source-stratum-bound selected-entry handoff.  The new step is measure
bookkeeping from support on `sourceStratum`, reproduced in
`reproduction-a2-case2-source-stratum-supported-open-restriction-finite-integral.md`.

## Nonclaims

The result is a supported-measure finite-integral restatement.  It does not
prove source-rank coverage, selected-entry image equality, exact-rank openness,
source-prior or Jacobian transport, analytic atlas construction, normal
crossings, pole order, RLCT, or a numerical successor selected-entry matrix
rank.
