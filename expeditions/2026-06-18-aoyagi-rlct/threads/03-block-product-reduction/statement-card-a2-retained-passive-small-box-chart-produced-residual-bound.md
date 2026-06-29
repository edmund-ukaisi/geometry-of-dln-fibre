# Statement Card: A2 retained-passive small-box chart-produced residual bound

## Status

Proved in Lean locally.  Focused build passed for
`DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure`.  Xhigh review passed.

## Statement

The retained-passive selected-entry chart-produced source measure satisfies
the local-source residual square-sum bound

```text
squareSum(residualBlockCoordinateMap x) <= Rreg^2
```

a.e. on `mu.restrict localSource`, provided the selected-entry signed-box
radii obey

```text
0 <= delta,
forall i, Rres i <= delta,
delta^2 * (1 + #(center.erase pivot) * delta^2) <= Rreg^2.
```

The fixed-radius source-edge-family two-sided handoff now has a small-box
wrapper that uses this a.e. bound in place of the former explicit
`hle_source` premise.

## Lean declarations

```text
residualSquareSum_le_sq_ae_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure_of_residual_eq_of_smallBox

residualSquareSum_le_sq_ae_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_of_sourceEdgeFamilyOfData_chartProducedMeasure_of_smallBox

exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_of_sourceEdgeFamilyOfData_chartProducedMeasure_of_smallBox
```

## Inputs Kept Explicit

- `delta` and the coordinate-radius bounds `Rres i <= delta`.
- The scalar smallness inequality at the same fixed radius `Rreg`.
- The retained-data a.e. measurability needed to make the concrete source
  chart a.e. measurable.
- The existing source-stratum loss and density comparison hypotheses.

## Nonclaims

No radius is chosen.  No result at `Rmax` is transported to a smaller radius.
No source-rank coverage, source/image equality, original source-prior
transport, Jacobian comparison, normal-crossing construction, pole-order
calculation, or RLCT extraction is proved.
