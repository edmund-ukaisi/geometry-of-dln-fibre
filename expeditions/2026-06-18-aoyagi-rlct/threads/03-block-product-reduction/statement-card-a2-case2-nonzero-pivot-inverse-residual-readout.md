# Statement Card - A2 Case 2 nonzero-pivot inverse residual readout

Date: 2026-06-29.

## Claim

On the selected-pivot nonzero locus, the endpoint-transported retained-passive
Case 2 selected-entry source chart recovers ambient center coordinates after
pullback by `preimageOfPivotNeZero`.

## Lean Targets

Files:

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntrySignedBoxMeasure.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

Declarations:

```text
SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero_chartMap
paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_value_of_sourceReadback_residualFactorProduct_eq_matrix_preimageOfPivotNeZero
paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_value_of_case2EndpointTransport_sourceEdgeFamilyOfData_preimageOfPivotNeZero
```

## Inputs Kept Explicit

- nonzero selected-pivot coordinate;
- endpoint equivalence `eNext`;
- endpoint-family equivalences `e`;
- Case 2 continuation inequalities `hcont` and `hnext`;
- the retained-passive source-readback residual-factor matrix handoff;
- the finite residual-coordinate equivalence induced by the endpoint
  equivalences.

## Nonclaims

No continuity at the exceptional divisor, no selected-entry chart image
equality, no source-rank coverage theorem, no external/original source-prior
transport, no determinant-chart pushforward theorem, no Jacobian comparison, no
analytic atlas, no normal crossings, no pole order, and no RLCT statement is
proved.

## Verification

Focused build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
```

xhigh review passed:
`review-a2-case2-nonzero-pivot-inverse-residual-readout.md`.

Standard checks passed:

```text
cd lean
scripts/sorries

git diff --check
rg -n "\bsorry\b|#exit|native_decide|\baxiom\b" lean/DLNFibre/DLN/Aoyagi/SelectedEntrySignedBoxMeasure.lean lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```
