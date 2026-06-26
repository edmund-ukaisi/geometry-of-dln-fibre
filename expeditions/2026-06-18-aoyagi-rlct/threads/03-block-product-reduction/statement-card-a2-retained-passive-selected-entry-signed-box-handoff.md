# Statement card - A2 retained-passive selected-entry signed-box handoff

## Claim

Specialise the retained-passive monomial-unit local-measure handoff to the
selected-entry signed-box coordinate package.  Under a supplied retained-passive
source chart, weighted pushforward, residual readout, and local loss/density
bounds, obtain the same local finite-integral conclusion as the current
retained-passive handoff.

## Lean artifact

File:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean`

Expected theorem:

```lean
PaperEndpointFixedBaseRegularCoordinateSourceData.
  exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity
```

## Proved inputs

The selected-entry monomial-unit identities and unit bounds come from
`SelectedEntrySignedBox.CenterCoord`:

- `densityUnit_aemeasurable`
- `residual_eq_unit_mul_abs_monomial`
- `sourceDensity_eq_unit_mul_abs_monomial`
- `one_le_residualUnit`
- `densityUnit_nonneg`
- `densityUnit_le_one`

## Supplied inputs

- retained-passive source chart;
- weighted pushforward to the retained-passive local source;
- residual readout through that chart;
- local loss lower bound;
- local density nonnegativity and upper bound.

## Nonclaims

No retained-passive source chart is constructed.  No weighted pushforward,
Jacobian/source-density calculation, original-loss comparison, normal
crossings, pole order, or RLCT extraction is proved.
