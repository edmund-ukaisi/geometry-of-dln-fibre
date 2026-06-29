# Review - A2 Case 2 source-stratum-supported chart-produced measure

Date: 2026-06-29.

Reviewer: xhigh `Banach the 2nd`.

Status: PASS.

## Findings

No findings.

## Checks

The reviewer checked:

- `measure_map_restrict_sourceRankStratum_eq_self_of_ae_mem`;
- `PaperEndpointFixedBaseRegularCoordinateSourceData.measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_restrict_sourceRankStratum_eq_self`.

The generic lemma is only support bookkeeping.  It assumes a.e. membership in
`paperEndpointFixedBaseSourceRankStratum`, proves the stratum measurable from
continuous `Cedge`, transfers membership through `ae_map_iff`, and applies
`Measure.restrict_eq_self_of_ae_mem`.

The Case 2 theorem states exactly

```text
mu.restrict sourceStratum = mu
```

for `mu := Measure.map sourceChart sourceMeasure`, where `sourceMeasure` is
the selected-entry signed-box measure with `withDensity`.  Its support
hypotheses are explicit:

```text
finrank range(paperTotalMap W2 B2) = r,
r + card tau = rEdge 0,
forall yNext,
  r + rank(case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext) = rEdge 1.
```

The measurable support proof uses chart continuity for a.e. measurability of
the unweighted signed-box measure, `withDensity_absolutelyContinuous` for the
weighted measure, pointwise rank membership for a.e. source-stratum membership,
and the generic support lemma for the restriction equality.

The theorem placement after
`continuous_retainedPassiveP13SourceEdgeFamilyOfData_of_case2EndpointTransport`
is non-circular: it consumes that continuity helper, and the helper does not
depend on the new support theorem.

## Verification

The reviewer ran:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
```

It passed with only unrelated replay warnings from
`ProductReductionStepRegularDensity.lean`.

## Boundary

The slice is conditional support for a constructed chart-produced measure.  It
does not prove source-rank coverage, selected-entry image equality,
exact-rank openness, source-prior or Jacobian transport, analytic atlas
construction, normal crossings, pole order, RLCT, or a numerical successor
selected-entry matrix rank.
