# Statement card - A2 Case 2 determinant-chart selected-entry residual handoff

## Declaration

```text
DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData.
  retainedPassiveP13Canonical_detChart_residual_pos_ae_and_lintegral_rpow_neg_of_case2EndpointTransport_selectedEntrySignedBox_map
```

## File

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

## Statement

For the two-edge Case 2 endpoint-transported selected-entry data, let

```text
chart y =
  topologyTuple
    ((case2PostPivotSelectedEntryRetainedPassiveData
      n hS hcont hnext y eNext).endpointTransport e).
```

Assume the determinant-chart pushforward identity

```text
m.restrict topologyTupleDetChartSet =
  Measure.map chart
    (signedBox.withDensity
      (fun y => ofReal
        (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y)))
```

and target positive-set measurability.  Under positive signed-box radii,
`0 <= t`, and

```text
2 * t < ((center.erase pivotNext.1).card : R) + 1,
```

the retained-passive determinant-chart residual is positive a.e. over
`m.restrict topologyTupleDetChartSet` and has finite negative-power lower
integral there.

## Source / Proof Basis

Aoyagi PDF pp. 11-13 for the retained-passive p.13 determinant/source chart
and pp. 19-22 for the Case 2 selected-entry chart.  Lean dependencies:

```text
retainedPassiveP13Canonical_detChart_residual_pos_ae_and_lintegral_rpow_neg_of_selectedEntrySignedBox_map
continuous_case2PostPivotSelectedEntryRetainedPassiveData
RetainedPassiveNonredundantCoordinateData.continuous_endpointTransport
RetainedPassiveNonredundantCoordinateData.continuous_topologyTuple
aoyagiCoordinateSquareSum_paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_residual_of_case2EndpointTransport_sourceEdgeFamilyOfData
```

The residual readout reduces `directChart (chart y)` to the endpoint-
transported source edge family by unfolding and using
`ofTopologyTuple_topologyTuple`.

## Boundary

This discharges the Case 2 chart a.e. measurability and residual readout for
the generic selected-entry determinant-chart residual handoff.  It does not
prove the determinant-chart pushforward identity, chart coverage, original
external source-prior transport, local loss or density bounds, source-rank
coverage, normal crossings, pole order, or RLCT extraction.

## Verification Plan

Run focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure`, then
`scripts/sorries`, `git diff --check`, touched-file forbidden-marker search,
direct axiom probe, and xhigh review.

## Verification Result

Focused build of `DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure`
passed via the worktree-local `scripts/lb` command.  Xhigh read-only review by
Russell passed.  `scripts/sorries`, `git diff --check`, touched Lean-file
forbidden-marker search, and direct axiom probe passed; the new declaration
reports only `[propext, Classical.choice, Quot.sound]`.
