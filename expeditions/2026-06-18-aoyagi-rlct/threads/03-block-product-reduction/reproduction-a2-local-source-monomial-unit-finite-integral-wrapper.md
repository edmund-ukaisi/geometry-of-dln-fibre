# Reproduction - A2 local-source monomial-unit finite-integral wrapper

Date: 2026-06-25.

## Scope

This slice is a consumer for supplied local residual chart data.  It does not
construct the local chart or prove the measure pushforward.  It proves that the
local-source finite-integral theorem can take monomial-times-unit residual and
source-density data directly, instead of requiring the expanded monomial
inequalities as separate inputs.

## Pen-And-Paper Calculation

Let the signed box carry coordinates `y_i`, and write

```text
Q_k(y) = prod_i |y_i|^(2 k_i),
Q_h(y) = prod_i |y_i|^(h_i).
```

Assume the supplied residual and source density satisfy, almost everywhere on
the signed box,

```text
residual(sourceChart(y)) = u_res(y) Q_k(y),
sourceDensity(y) = u_den(y) Q_h(y).
```

If `c <= u_res(y)`, then all monomial factors are nonnegative, hence

```text
c Q_k(y) <= residual(sourceChart(y)).
```

If `0 <= u_den(y) <= C`, then similarly

```text
0 <= sourceDensity(y),
sourceDensity(y) <= C Q_h(y).
```

If `u_den` is a.e.-measurable, then `sourceDensity` is a.e.-measurable because
`Q_h` is a finite product of measurable functions `y |-> |y_i|^(h_i)`.

These are exactly the residual lower bound and source-density hypotheses
consumed by the local-source signed-box finite-integral theorem.

## Lean Landing

The landed theorem is in
`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean`:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_residualSource_signedBox_withDensity_monomialUnits_edgeMatrix
```

It composes

```text
signedBox_monomialLower_sourceDensityBounds_of_monomialUnits
```

with

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_residualSource_signedBox_withDensity_monomialLower_edgeMatrix
```

## Remaining Boundary

The local source set, signed-box chart, weighted pushforward identity,
residual monomial-unit identity, source-density monomial-unit identity,
density/Jacobian formula, normal-crossing extraction, pole order, and RLCT
extraction remain supplied or cited outside this slice.
