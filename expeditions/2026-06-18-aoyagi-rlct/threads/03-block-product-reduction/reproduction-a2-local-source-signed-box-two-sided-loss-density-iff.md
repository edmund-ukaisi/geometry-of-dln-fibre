# Reproduction - A2 local-source signed-box two-sided loss-density iff

Date: 2026-06-29.

Status: pen-and-paper checked; Lean formalised as a supplied-bound local
integrability equivalence.

## Source Anchor

Aoyagi p. 13 separates the regular-coordinate square variables from the
residual variables.  The existing local-source two-sided theorem already says
that, on a supplied local source, actual p.13 loss-density integrability is
equivalent to residual negative-power integrability once the residual
measurability, positivity, local boundedness, and two-sided loss/density bounds
are supplied.

The present step connects that theorem to the signed-box residual-source
socket.  The signed-box chart is still supplied by hypotheses:

```text
mu.restrict source =
  Measure.map sourceChart
    (signedBox.withDensity (fun y => ofReal (sourceDensity y))).
```

The chart-side monomial lower bound is

```text
cres * product_i |y_i|^(2*kres_i) <= residualSquareSum(sourceChart y),
```

where `0 < cres`.  The source density appears only as the supplied
with-density weight in the pushforward identity.  For this positivity-only
bridge, no source-density upper bound, nonnegativity hypothesis, positive
signed-box radius hypothesis, or critical integrability inequality is needed.

The new positivity-only helper transports the chart-side positivity through
the weighted pushforward and gives residual positivity a.e. on
`mu.restrict source`.  It is deliberately weaker than the older residual-source
constructor, because it does not prove residual negative-power integrability on
`source`.

## Calculation

Let

```text
a(x) =
  aoyagiCoordinateSquareSum
    (paperEndpointFixedBaseResidualBlockCoordinateMap ... Cedge x).
```

The measurable edge-matrix family gives measurability of the residual
coordinate map and hence

```text
AEMeasurable a (mu.restrict source).
```

The signed-box positivity helper gives

```text
a(x) > 0 for mu.restrict source-a.e. x.
```

The remaining reverse-Fubini hypothesis is deliberately not derived here:

```text
a(x) <= Rreg^2 for mu.restrict source-a.e. x.
```

It is an explicit input.

Assume four source-filter comparison bounds, uniform for
`u in ball(0, Rreg)`:

```text
cLreg * (a(x) + regularSquareSum(u)) <= loss(x,u),
loss(x,u) <= CLreg * (a(x) + regularSquareSum(u)),
dRho <= density(x,u),
density(x,u) <= DRho.
```

The local-source two-sided theorem shrinks to an open neighborhood `U` of
`x0` and proves

```text
integral over (mu.restrict (U inter source)).prod nu is finite
iff
residualNegPowerIntegrableOn Cedge (U inter source) mu t.
```

The statement is intentionally local.  It does not claim that `source` covers
the source-rank stratum, that the signed-box chart is Aoyagi's p.13 inverse
chart, or that `sourceDensity` is a Jacobian/source-prior density.

## Lean Shape

Lean formalises this in:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
```

Main theorem:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_localSource_residualSource_signedBox_withDensity_monomialLower_edgeMatrix
```

The proof:

1. derives residual-square-sum `AEMeasurable` from the measurable edge-matrix
   family using
   `measurable_paperEndpointFixedBaseResidualBlockCoordinateMap_of_measurable_edgeMatrix`
   and `measurable_aoyagiCoordinateSquareSum`;
2. calls
   `residualSquareSum_pos_ae_of_measure_map_signedBox_withDensity_monomialLower_of_measurable_edgeMatrix`
   to obtain residual positivity without proving residual integrability;
3. applies
   `exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_localSource_two_sided_bounds`
   with the explicit local boundedness hypothesis and the four supplied
   comparison bounds.

Focused build:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure
```

passed after the Lean change.

## Nonclaims

- No proof of the signed-box chart or the pushforward identity.
- No proof that the local source covers a source-rank stratum neighborhood.
- No proof of the four p.13 loss/density comparison bounds.
- No proof of the local residual boundedness `a <= Rreg^2`.
- No source-prior, Jacobian, density, or product-measure transport theorem.
- No original-loss identification.
- No normal-crossing theorem, pole-order theorem, or RLCT extraction.
