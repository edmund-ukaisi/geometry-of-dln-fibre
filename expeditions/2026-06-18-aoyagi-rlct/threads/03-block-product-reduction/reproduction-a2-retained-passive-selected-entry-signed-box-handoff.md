# A2 retained-passive selected-entry signed-box handoff

## Boundary

This slice is a retained-passive consumer of the already formalised
selected-entry signed-box calculation.  It does not construct the
retained-passive chart, prove a weighted pushforward/Jacobian formula, compare
the original DLN loss, prove normal crossings, compute pole order, or extract
an RLCT.

## Pen-and-paper reproduction

The current retained-passive monomial-unit handoff needs signed-box data

- a source chart `sourceChart : (iota -> R) -> alpha`;
- a weighted source-measure identity
  `mu.restrict localSource = map sourceChart (signedBox.withDensity sourceDensity)`;
- residual and source-density identities
  `residual = residualUnit * prod |y_i|^(2 k_i)` and
  `sourceDensity = densityUnit * prod |y_i|^(h_i)`;
- lower/upper bounds on the unit factors.

For a selected-entry centre `center` with pivot `p`, the existing
selected-entry calculation supplies the last four bullets on the coordinate
space `center -> R`:

- `k_p = 1`, `k_i = 0` for `i != p`;
- `h_p = #(center.erase p)`, `h_i = 0` for `i != p`;
- `residualUnit >= 1`;
- `0 <= densityUnit <= 1`.

Thus the retained-passive theorem can instantiate `cres = 1`, `Cres = 1`,
`kres = SelectedEntrySignedBox.CenterCoord.lossExp pivot`, and
`hres = SelectedEntrySignedBox.CenterCoord.densityExp pivot`.  The only
retained-passive-specific algebra still needed is the residual readout

```lean
aoyagiCoordinateSquareSum
  (paperEndpointFixedBaseResidualBlockCoordinateMap ... (sourceChart y))
  =
SelectedEntrySignedBox.CenterCoord.residual pivot y.
```

The integrability critical inequality is also the selected-entry one.  For the
pivot coordinate it is

```text
2 * t < #(center.erase pivot) + 1.
```

For every non-pivot coordinate it is `0 < 0 + 1`, since `k_i = h_i = 0`.

## Lean target

Add a theorem in
`RetainedPassiveLocalMeasure.lean`:

```lean
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity
```

The theorem should call the existing retained-passive monomial-unit handoff
after constructing the selected-entry monomial identities and bounds from
`SelectedEntrySignedBox.CenterCoord`.

## Nonclaims

The resulting theorem is not a chart construction theorem.  It still assumes
`sourceChart`, `hsourceChart`, and `hmap`.  It is not a Jacobian theorem and
does not identify the retained-passive source density from the open partial
homeomorphism.
