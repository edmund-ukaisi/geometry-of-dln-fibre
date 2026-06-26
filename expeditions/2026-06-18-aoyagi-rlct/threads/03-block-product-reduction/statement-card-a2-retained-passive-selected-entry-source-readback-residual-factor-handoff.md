# Statement card - A2 retained-passive selected-entry source-readback residual-factor handoff

## Claim

Replace the raw selected-entry residual square-sum hypothesis in the
retained-passive selected-entry local-measure handoff by a concrete
retained-passive source-readback residual-factor product matrix identity.

## Lean artifacts

File:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean`

Expected theorems:

```lean
PaperEndpointFixedBaseRegularCoordinateSourceData.
  aoyagiCoordinateSquareSum_paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_residual_of_sourceReadback_residualFactorProduct_eq_matrix

PaperEndpointFixedBaseRegularCoordinateSourceData.
  exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_of_sourceReadback_residualFactorProduct_eq_matrix
```

## Proved inputs

- `paperEndpointFixedBaseResidualBlockCoordinateMap_eq_sourceReadback_residualFactorProduct`
  rewrites the fixed-base residual coordinate map through retained-passive
  `sourceReadback`.
- `AoyagiResidualBlockCoordinateIndex.value_matrix` converts the supplied
  matrix identity into coordinate readout.
- `aoyagiCoordinateSquareSum_comp_equiv` and
  `SelectedEntrySignedBox.CenterCoord.residual_eq_aoyagiCoordinateSquareSum_chartMap`
  identify the finite square-sum with the selected-entry residual.

## Supplied inputs

- source chart and weighted pushforward;
- residual-coordinate equivalence to the selected center;
- entrywise residual-factor product matrix identity;
- local loss lower bound and density bounds.

## Nonclaims

No retained-passive source chart is constructed.  No source image equality,
weighted pushforward proof, Jacobian/source-density theorem, original-loss
comparison, normal crossings, pole order, or RLCT extraction is proved.
