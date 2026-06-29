# Reproduction - A2 local-source two-sided loss-density iff

Date: 2026-06-29.

Status: pen-and-paper checked; Lean formalised as a supplied-bound local
integrability equivalence.

## Source Anchor

Aoyagi PDF p. 13 reduces the regular-coordinate layer to a square model

```text
model(x,u) = residualSquareSum(x) + regularSquareSum(u).
```

The previous checkpoints proved the square-model threshold shift, the supplied
two-sided loss-density comparison iff, and the local-source handoff that turns
source-filter comparison bounds into a.e. product-measure bounds.  The present
step composes these facts for an explicitly supplied local source.

It does not prove the comparison bounds or the residual hypotheses.  It only
says that, after shrinking to a source neighborhood where the supplied bounds
hold a.e. on the product measure, actual loss-density finiteness is equivalent
to the residual negative-power integral on the same restricted source.

## Calculation

Let

```text
a(x) = aoyagiCoordinateSquareSum
  (paperEndpointFixedBaseResidualBlockCoordinateMap ... Cedge x).
```

On a supplied source set, assume:

```text
AEMeasurable a (mu.restrict source),
a(x) > 0 a.e. on mu.restrict source,
a(x) <= R^2 a.e. on mu.restrict source,
0 < R, 0 < t,
0 < cL, 0 < CL, 0 < dRho, 0 <= DRho.
```

Also assume the four source-filter comparison bounds, uniform for
`u in ball(0,R)`:

```text
cL * (a(x) + regularSquareSum(u)) <= loss(x,u),
loss(x,u) <= CL * (a(x) + regularSquareSum(u)),
dRho <= density(x,u),
density(x,u) <= DRho.
```

The local-source two-sided handoff gives an open set `U` with `x0 in U` such
that the four bounds hold a.e. over

```text
(mu.restrict (U inter source)).prod nu.
```

Restricting the residual hypotheses from `source` to `U inter source` gives the
inputs for the p.13 two-sided comparison iff on the restricted base measure.
Therefore

```text
actual loss-density integral over (mu.restrict (U inter source)).prod nu < infinity
iff
residualNegPowerIntegrableOn Cedge (U inter source) mu t.
```

The lower density bound gives density nonnegativity for the imported comparison
iff; no separate density nonnegativity hypothesis is needed.  The lower loss
bound plus residual positivity and `cL > 0` gives the loss positivity used
internally by the reverse comparison; no separate loss positivity hypothesis is
needed.

## Lean Shape

Lean formalises this in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
```

with:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_localSource_two_sided_bounds
```

The proof:

1. obtains `U` and four product-measure a.e. bounds from
   `exists_open_ae_restrict_localSource_prod_p13RegularCoordinates_two_sided_loss_density_bounds`;
2. restricts residual `AEMeasurable`, positivity, and `<= R^2` hypotheses from
   `source` to `U inter source`;
3. applies
   `lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_two_sided_bounds`
   with `mu := mu.restrict (U inter source)`;
4. rewrites the right side as `residualNegPowerIntegrableOn`.

Focused build:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure
```

passed.

## Nonclaims

- No proof of the four supplied comparison bounds.
- No proof of residual measurability, positivity, boundedness, or
  negative-power integrability on any source.
- No construction or identification of Aoyagi's p.13 product chart.
- No source-prior, Jacobian, density, or product-measure transport theorem.
- No original-loss identification.
- No normal-crossing theorem, pole-order theorem, or RLCT extraction.
