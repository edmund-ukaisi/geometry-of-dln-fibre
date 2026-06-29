# Reproduction - A2 source-stratum signed-box two-sided loss-density iff

Date: 2026-06-29.

Status: pen-and-paper checked; Lean formalised as a source-stratum
specialisation of the local-source signed-box two-sided iff.

## Source Anchor

Aoyagi p. 13 uses the source-rank stratum as the base set for the p.13
regular/residual square model.  The preceding local-source theorem already
proves a two-sided p.13 loss-density integrability equivalence for any supplied
local source represented by a weighted signed-box residual chart.

The present step is only the source-stratum wrapper.  It sets

```text
source = paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge
```

in the local-source theorem.

## Calculation

Let

```text
a(x) =
  aoyagiCoordinateSquareSum
    (paperEndpointFixedBaseResidualBlockCoordinateMap ... Cedge x).
```

Assume the weighted signed-box pushforward for the source stratum:

```text
mu.restrict sourceStratum =
  Measure.map sourceChart
    (signedBox.withDensity (fun y => ofReal (sourceDensity y))).
```

Assume the residual monomial lower bound

```text
cres * product_i |y_i|^(2*kres_i) <= a(sourceChart y)
```

with `0 < cres`.  This gives positivity of `a` a.e. on
`mu.restrict sourceStratum`, via the positivity-only signed-box helper.  It
does not use signed-box critical inequalities or source-density upper bounds,
so it does not prove residual negative-power integrability.

The reverse-Fubini side still requires the explicit local boundedness input:

```text
a(x) <= Rreg^2
```

for `mu.restrict sourceStratum`-a.e. `x`.

With four source-stratum-filter comparison bounds, uniform for
`u in ball(0, Rreg)`,

```text
cLreg * (a(x) + regularSquareSum(u)) <= loss(x,u),
loss(x,u) <= CLreg * (a(x) + regularSquareSum(u)),
dRho <= density(x,u),
density(x,u) <= DRho,
```

the local-source theorem returns an open neighborhood `U` of `x0` and proves

```text
actual loss-density integral over (mu.restrict (U inter sourceStratum)).prod nu < infinity
iff
residualNegPowerIntegrableOn Cedge (U inter sourceStratum) mu t.
```

No additional analytic statement is introduced in this wrapper.

## Lean Shape

Lean formalises this in:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
```

Main theorem:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix
```

The proof:

1. defines `sourceStratum`;
2. applies
   `exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_localSource_residualSource_signedBox_withDensity_monomialLower_edgeMatrix`
   with `source := sourceStratum`;
3. rewrites the conclusion back to the source-rank-stratum notation.

Focused build:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure
```

passed after the Lean change.

## Nonclaims

- No proof of the signed-box chart or the pushforward identity.
- No proof of local chart coverage or source-rank-stratum coverage.
- No proof of the residual boundedness `a <= Rreg^2`.
- No proof of the four p.13 loss/density comparison bounds.
- No signed-box critical-integrability theorem in this wrapper.
- No source-prior, Jacobian, density, or product-measure transport theorem.
- No original-loss identification.
- No normal-crossing theorem, pole-order theorem, or RLCT extraction.
