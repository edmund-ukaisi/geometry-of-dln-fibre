# Statement card - A2 selected-entry all-pivot transition regular data

Date: 2026-06-29.

## Statement

For the all-pivot selected-entry finite chart family over the shared
universal-domain context, the normalized selected-entry overlap formula supplies
`SelectedEntryAnalyticTransitionRegularData`.  The transition from source chart
`source` to target chart `target` is defined on the locus where the target
normalized coordinate in the source chart is nonzero; on that domain it is
continuous, lands in the target chart domain, and preserves the represented
center point.

Lean targets:

```text
selectedEntryAllPivotAnalyticTransitionRegularData
selectedEntryAllPivotAnalyticTransitionRegular
```

## Source Reference

Aoyagi PDF pp. 15-22 supplies the chosen-pivot selected-entry substitution.
The all-pivot transition and renormalization record is expedition-built finite
overlap bookkeeping over the existing selected-entry transition lemmas.

## Dependencies

- `selectedEntryAllPivotAnalyticAtlasContext`
- `sourceChartTransitionPoint`
- `chartMap_sourceChartTransitionPoint_eq_of_target_normalized_ne_zero`
- `sourceChartPoint_chartPointResidual_eq`
- continuity of constants, projections, multiplication, division on nonzero
  denominator domains, products, and finite pi types.

## Assumptions Kept Explicit

- a nonempty finite center;
- an enumeration `chartEquiv : Fin center.card ≃ center`;
- transition domains are nonzero-denominator overlaps, not all of the source
  chart unless the source and target pivots coincide.

## Nonclaims

This does not prove source production, branch termination, source-prior
transport, determinant-chart Haar transport, a full supplied analytic atlas
producer, normal-crossing extraction, pole order, or RLCT.

## Reproduction and Review

Reproduction:

```text
threads/03-block-product-reduction/reproduction-a2-selected-entry-all-pivot-transition-regular-data.md
```

Review:

```text
threads/03-block-product-reduction/review-a2-selected-entry-all-pivot-transition-regular-data.md
```

Verdict: PASS after documentation repair.  Xhigh source/scope reviewer
Erdos the 4th confirmed the source-attribution repair, and xhigh Lean/API
reviewer Confucius the 4th returned PASS.
