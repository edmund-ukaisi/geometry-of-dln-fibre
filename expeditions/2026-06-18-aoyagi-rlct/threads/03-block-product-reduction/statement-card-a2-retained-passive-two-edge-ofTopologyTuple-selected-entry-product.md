# Statement card: A2 retained-passive two-edge `ofTopologyTuple` selected-entry product adapter

## Lean name

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryChartBridge.lean
```

```text
residualFactorProduct_ofTopologyTuple_eq_selectedEntryCenter_matrix_of_case2PostPivot_entrywise
```

## Content

For a retained-passive topology tuple `z` with `M = 1`, if the two stored
factors of `(ofTopologyTuple z).C` are Aoyagi's displayed Case 2 post-pivot
residual block and following free factor after endpoint equivalences, and if
the displayed two-edge product has the selected-entry center-coordinate
readout entrywise, then

```text
residualFactorProduct (ofTopologyTuple z).C (Fin.last 2) 0
  = matrix (fun c => CenterCoord.chartMap pivot y (residualCoordEquiv c)).
```

## Proved inputs

```text
residualFactorProduct_retainedPassiveCoordinateData_eq_selectedEntryCenter_matrix_of_case2PostPivot_entrywise
```

and the definition of `ofTopologyTuple`.

## Supplied inputs

- Endpoint equivalences for the two displayed Case 2 factors.
- Factor identities for `(ofTopologyTuple z).C 1` and `(ofTopologyTuple z).C 0`.
- Entrywise selected-entry readout of the displayed two-edge product.

## Cited

None.  This is finite matrix and coordinate-record bookkeeping.

## Proved

The theorem is proved in `RetainedPassiveCase2SelectedEntryChartBridge.lean`.
The proof delegates directly to the retained-passive data-level theorem with
`data := ofTopologyTuple z`.

## Deferred

The selected-entry identity for an arbitrary full canonical suffix, outside
factor removal/absorption, zero-locus/nullity analysis, chart-side positivity,
finite negative-power integrability, density transport, normal crossings,
pole order, and RLCT extraction.

## Review

Xhigh review by `Noether the 3rd` passed.  The review is saved at
`review-a2-retained-passive-two-edge-ofTopologyTuple-selected-entry-product.md`.

## Verification

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2SelectedEntryChartBridge` passed.
`scripts/sorries`, `git diff --check`, and the touched Lean file
forbidden-marker search passed.
