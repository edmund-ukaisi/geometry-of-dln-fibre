# Statement card - A2 retained-passive fixed-base pre-measure inputs

## Claim

If a selected-entry source chart is realized by fixed-base retained-passive
coordinate data, then the source chart lies in the fixed-base retained-passive
p.13 local source and its source-readback residual-factor product has the
selected-entry center-coordinate matrix form.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
```

Target name:

```lean
PaperEndpointFixedBaseRegularCoordinateSourceData.retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_retainedPassiveCoordinateData_edgeMatrix
```

## Proof Basis

For local-source membership, unfold
`paperEndpointFixedBaseRetainedPassiveP13LocalSource`, rewrite the fixed-base
edge matrix by the supplied realization hypothesis `hedge`, and apply
`sourceRecursiveDetChart_edgeMatrix_of_detChart`.

For the source-readback matrix identity, reuse
`sourceReadback_residualFactorProduct_eq_matrix_of_retainedPassiveCoordinateData_edgeMatrix`.

## Nonclaims

This theorem does not construct the retained-passive coordinate data, prove the
edge-matrix realization hypothesis `hedge`, transport `edgeMatrix` or
`sourceReadback` along endpoint equivalences, compare source priors or
Jacobians, prove normal crossings, pole order, or RLCT.
