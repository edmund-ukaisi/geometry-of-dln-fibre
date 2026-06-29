# Statement Card - A2 Case 2 coordinate residual readout

Date: 2026-06-29.

## Claim

The endpoint-transported retained-passive Case 2 selected-entry chart satisfies
the coordinate-level fixed-base residual readout matching the residual-readout
shape used by the selected-entry original-loss handoff.

## Lean Targets

Files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

Declarations:

```text
paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_sourceReadback_residualFactorProduct_eq_matrix
paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_case2EndpointTransport_sourceEdgeFamilyOfData
```

## Inputs Kept Explicit

- endpoint equivalence `eNext`;
- endpoint-family equivalences `e`;
- Case 2 continuation inequalities `hcont` and `hnext`;
- the retained-passive source-readback residual-factor matrix handoff;
- the finite residual-coordinate equivalence induced by the endpoint
  equivalences.

## Nonclaims

No selected-entry chart image equality, no source-rank coverage theorem, no
external/original source-prior transport, no determinant-chart pushforward
theorem, no Jacobian comparison, no analytic atlas, no normal crossings, no
pole order, and no RLCT statement is proved.

This does not prove the original-loss residual-readout socket with
`CedgeBase (SelectedEntrySignedBox.CenterCoord.chartMap pivot y)`.  The theorem
is for the constructed retained-passive Case 2 source chart; identifying that
ambient source point with a selected-entry `chartMap` image is separate.

## Verification

Focused build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
```

xhigh review passed:
`review-a2-case2-coordinate-residual-readout.md`.

Standard checks passed:

```text
cd lean
scripts/sorries

git diff --check
rg -n "\bsorry\b|#exit|native_decide|\baxiom\b" lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```
