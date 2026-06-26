# Statement card - A2 retained-passive source-map factor readout

## Claim

For retained-passive coordinate data in the determinant chart, the Schur
residual block of the transformed source edge of `data.edgeMatrix` at edge
`p` is the stored residual factor `data.C p`.

For the synthetic Case 2 two-edge retained-passive datum, this gives the two
displayed factor identities:

```text
edge 1 -> case2DisplayedPostPivotResidualBlock
edge 0 -> case2DisplayedPostPivotFreeFollowingFactor
```

## Lean Artifacts

Files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryChartBridge.lean
```

Theorems:

```lean
schurResidualBlock_sourceReadbackTransformedEdge_edgeMatrix_eq_C

schurResidualBlock_sourceReadbackTransformedEdge_case2PostPivotRetainedPassiveData_edgeMatrix_one_eq_residualBlock

schurResidualBlock_sourceReadbackTransformedEdge_case2PostPivotRetainedPassiveData_edgeMatrix_zero_eq_freeFollowingFactor
```

## Inputs

- The retained-passive determinant-chart hypothesis `data.detChart`.
- The already proved readback inverse `sourceReadback_edgeMatrix_eq`.
- The per-factor source-readback identity
  `sourceReadback_C_eq_schurResidualBlock_sourceReadbackTransformedEdge`.
- For the Case 2 specialization, the synthetic datum
  `case2PostPivotRetainedPassiveData` and its determinant-chart proof.

## Nonclaims

No real Aoyagi source chart is produced.  No fixed-base endpoint equivalence,
full-suffix collapse, selected-entry entrywise readout, pivot nonzero proof,
source image, pushforward/Jacobian theorem, original-loss comparison, normal
crossing, pole order, or RLCT extraction is proved.

## Verification

Focused checks passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2SelectedEntryChartBridge
```

Review:

```text
threads/03-block-product-reduction/review-a2-retained-passive-source-map-factor-readout.md
```
