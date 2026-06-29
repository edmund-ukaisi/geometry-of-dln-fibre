# A2 Case 2 source-stratum-supported chart-produced measure

## Lean statements

```text
measure_map_restrict_sourceRankStratum_eq_self_of_ae_mem
PaperEndpointFixedBaseRegularCoordinateSourceData.measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_restrict_sourceRankStratum_eq_self
```

## Claim

If a chart-produced source family lands a.e. in Aoyagi's source-shaped rank
stratum, then its mapped measure is unchanged by restriction to that stratum.

For the endpoint-transported continuing Case 2 selected-entry source chart,
the selected-entry weighted signed-box pushforward measure is supported on the
source-shaped rank stratum when the caller supplies

```text
finrank range(paperTotalMap W2 B2) = r,
r + card tau = rEdge 0,
forall yNext,
  r + rank(case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext) = rEdge 1.
```

## Source and reproduction

The pointwise rank membership is Aoyagi p.13 retained-passive source-rank
bookkeeping plus pp.19-22 continuing Case 2 selected-entry algebra, already
recorded in `reproduction-a2-retained-passive-source-stratum-membership.md`.
This card adds the measure-support step reproduced in
`reproduction-a2-case2-source-stratum-supported-chart-produced-measure.md`.

## Nonclaims

The result is conditional support for a constructed chart-produced measure.  It
does not prove local source-rank coverage, selected-entry image equality,
exact-rank openness, source-prior or Jacobian transport, analytic atlas
construction, normal crossings, pole order, RLCT, or a numerical successor
selected-entry matrix rank.
