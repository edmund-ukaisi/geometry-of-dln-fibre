# Statement card: A2 retained-passive Case 2 canonical chart selected-entry square-sum

## Lean name

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

```text
aoyagiCoordinateSquareSum_retainedPassiveP13Canonical_chart_eq_selectedEntryCenter_residual_of_case2PostPivot_entrywise
```

## Content

For the retained-passive canonical p.13 chart with a two-edge suffix
(`M = 1`), if the two stored `C` factors of `(ofTopologyTuple z)` are Aoyagi's
displayed Case 2 post-pivot residual block and following factor after endpoint
equivalences, and the displayed product has the selected-entry readout
entrywise, then the canonical chart-side residual square-sum equals the
selected-entry center residual.

The proof composes:

```text
residualFactorProduct_ofTopologyTuple_eq_selectedEntryCenter_matrix_of_case2PostPivot_entrywise
aoyagiCoordinateSquareSum_retainedPassiveP13Canonical_chart_eq_selectedEntryCenter_residual_of_residualFactorProduct_eq_matrix
```

## Proved

The theorem

```text
aoyagiCoordinateSquareSum_retainedPassiveP13Canonical_chart_eq_selectedEntryCenter_residual_of_case2PostPivot_entrywise
```

is proved in `RetainedPassiveCase2LocalJacobianMeasure.lean`.

## Assumed

- `z` lies in the retained-passive topology-tuple determinant chart.
- The two stored factors match the displayed Case 2 post-pivot factors after
  the supplied endpoint equivalences.
- The displayed two-edge product has the selected-entry readout entrywise.

## Cited

None.  This is finite retained-passive/selected-entry chart bookkeeping.

## Deferred

Longer-suffix outside-factor removal, zero-locus/nullity analysis,
chart-side positivity, finite negative-power integrability, density
transport, normal crossings, pole order, and RLCT extraction.

## Review

Xhigh review by `Lorentz the 3rd` found no Lean/formal issue and one stale
documentation-status issue, corrected here.  The review is saved at
`review-a2-retained-passive-case2-canonical-chart-selected-entry-square-sum.md`.

## Verification

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure` passed.  Full
`DLNFibre` build passed with pre-existing warning noise.  `scripts/sorries`,
`git diff --check`, and the touched Lean file forbidden-marker search passed.
