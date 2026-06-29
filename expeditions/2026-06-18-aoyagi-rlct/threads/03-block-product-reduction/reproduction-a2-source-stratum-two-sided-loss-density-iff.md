# Reproduction - A2 source-stratum two-sided loss-density iff

Date: 2026-06-29.

Status: pen-and-paper checked; Lean formalised as a source-stratum
specialisation of the supplied-bound local integrability equivalence.

## Source Anchor

Aoyagi PDF p. 13 works over the source-rank stratum for the p.13
regular/residual square model.  The local-source iff already proved that, on
an arbitrary supplied measurable source, explicit residual hypotheses and four
source-filter two-sided loss/density bounds imply an open-neighborhood
integrability equivalence.  The present step specializes that statement to

```text
S = paperEndpointFixedBaseSourceRankStratum (K := R) W B Cedge r rEdge.
```

It does not construct the p.13 chart, prove comparison bounds, or prove
residual hypotheses.  It only packages the same equivalence over the
source-rank stratum.

## Calculation

Assume on `S`:

```text
AEMeasurable residualSquareSum (mu.restrict S),
residualSquareSum > 0 a.e.,
residualSquareSum <= R^2 a.e.,
0 < R, 0 < t,
0 < cL, 0 < CL, 0 < dRho, 0 <= DRho.
```

Also assume the four `nhdsWithin x0 S` comparison bounds, uniform for
`u in ball(0,R)`:

```text
cL * (residualSquareSum(x) + regularSquareSum(u)) <= loss(x,u),
loss(x,u) <= CL * (residualSquareSum(x) + regularSquareSum(u)),
dRho <= density(x,u),
density(x,u) <= DRho.
```

Applying the local-source theorem with `source := S` gives an open `U` with
`x0 in U` and

```text
actual loss-density integral over (mu.restrict (U inter S)).prod nu < infinity
iff
residualNegPowerIntegrableOn Cedge (U inter S) mu t.
```

The proof is definitional: introduce `sourceStratum := S`, invoke the
local-source theorem, and rewrite the abbreviation.

## Lean Shape

Lean formalises this in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
```

with:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_sourceStratum_two_sided_bounds
```

The proof calls

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_localSource_two_sided_bounds
```

with `source := sourceStratum`.

Focused build:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure
```

passed.

## Nonclaims

- No proof of the four supplied comparison bounds.
- No proof of residual measurability, positivity, boundedness, or
  negative-power integrability on the source-rank stratum.
- No construction, coverage, or image theorem for Aoyagi's p.13 chart.
- No source-prior, Jacobian, density, or product-measure transport theorem.
- No original-loss identification.
- No normal-crossing theorem, pole-order theorem, or RLCT extraction.
