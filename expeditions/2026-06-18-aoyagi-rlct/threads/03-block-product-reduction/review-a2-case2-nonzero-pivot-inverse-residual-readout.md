# Review - A2 Case 2 nonzero-pivot inverse residual readout

Date: 2026-06-29.

Reviewer: xhigh `Turing the 2nd`.

Status: PASS.

## Findings

No blocking findings.

## Checks

The reviewer checked:

- `SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero_chartMap`;
- `paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_value_of_sourceReadback_residualFactorProduct_eq_matrix_preimageOfPivotNeZero`;
- `paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_value_of_case2EndpointTransport_sourceEdgeFamilyOfData_preimageOfPivotNeZero`.

The review confirmed:

- `preimageOfPivotNeZero_chartMap` is restricted to the nonzero-pivot locus;
- the generic retained-passive inverse readout only composes the existing
  coordinate readout with `chartMap_preimageOfPivotNeZero`;
- the Case 2 specialization keeps `eNext`, `e`, `hcont`, `hnext`, and
  `value pivotNext ≠ 0` explicit;
- no source-image, continuity, measure, Jacobian, normal-crossing, pole-order,
  or RLCT content is hidden in the theorems;
- the docs state the punctured-chart algebra boundary and explicitly deny
  continuity, source-image equality, source-rank coverage,
  source-prior/Jacobian transport, normal crossings, pole order, and RLCT.

## Verification

The reviewer ran:

```text
git status --short
git diff --stat
git diff --check
rg -n "\b(sorry|admit|axiom|unsafe)\b" ...

cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
```

The focused build passed.  It replayed unrelated existing linter warnings in
`ProductReductionStepRegularDensity.lean`; no touched-file build failures or
warnings blocked this slice.
