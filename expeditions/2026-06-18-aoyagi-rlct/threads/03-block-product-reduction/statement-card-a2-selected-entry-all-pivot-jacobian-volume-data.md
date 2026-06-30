# Statement card - A2 selected-entry all-pivot Jacobian/volume data

Date: 2026-06-29.

## Statement

For the all-pivot selected-entry finite chart family over the shared
universal-domain context, positive signed-box radii supply
`SelectedEntryAnalyticJacobianVolumeData` chart-by-chart.  At chart index `c`,
the data is exactly the one-pivot chart-point product-measure pushforward at
pivot `chartEquiv c`.

Lean targets:

```text
selectedEntryAllPivotAnalyticJacobianVolumeData
selectedEntryAllPivotAnalyticJacobianVolumeCompatible
```

## Source reference

Aoyagi PDF pp. 15-22 supplies the selected-entry substitution and Jacobian
density for a chosen pivot.  The all-pivot lift is expedition-built finite
bookkeeping over the finite pivot family.

## Dependencies

- `selectedEntryAllPivotAnalyticAtlasContext`
- `chartPointProductMeasure`
- `chartPointDensity`
- `map_formalChartMap_chartPointProductMeasure_withDensity_eq_restrict_image`
- `volume_restrict_chartMap_image_signedBoxSet_ne_zero`
- `chartMapTargetInnerBox_nonempty`

## Assumptions Kept Explicit

- a nonempty finite center;
- an enumeration `chartEquiv : Fin center.card ≃ center`;
- positive signed-box radii `hR : ∀ i, 0 < R i`.

## Nonclaims

This does not prove transition regularity between distinct selected-entry
pivots, source production, branch termination, source-prior transport,
determinant-chart Haar transport, a full supplied analytic atlas producer,
normal-crossing extraction, pole order, or RLCT.

## Reproduction and review

Reproduction:

```text
threads/03-block-product-reduction/reproduction-a2-selected-entry-all-pivot-jacobian-volume-data.md
```

Review:

```text
threads/03-block-product-reduction/review-a2-selected-entry-all-pivot-jacobian-volume-data.md
```

Verdict: PASS.  Xhigh source/scope reviewer Arendt the 4th and xhigh
Lean/API reviewer Mendel the 4th returned PASS.
