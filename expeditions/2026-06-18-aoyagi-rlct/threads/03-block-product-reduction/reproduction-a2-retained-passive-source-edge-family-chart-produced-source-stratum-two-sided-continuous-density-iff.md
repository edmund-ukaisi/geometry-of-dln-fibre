# Reproduction - A2 retained-passive source-edge-family source-stratum two-sided iff with continuous density

Date: 2026-06-29.

Status: pen-and-paper checked; Lean formalised.

## Source Anchor

This is an elementary local-density strengthening of the retained-passive
source-edge-family chart-produced source-stratum two-sided p.13 loss-density
handoff.  It uses only continuity and positivity of the transported density at
the p.13 chart center.  It is not source-prior transport, residual
integrability, normal crossings, pole order, or RLCT extraction.

## Density Shrink

Let

```text
a := density(base, 0),
```

and assume `0 < a`.  Choose

```text
d_rho := a / 2,
D_rho := a + 1.
```

Then `0 < d_rho` and `0 <= D_rho`, and

```text
d_rho < a < D_rho.
```

By continuity of `density` at `(base,0)`,

```text
{z | d_rho < density z and density z < D_rho}
```

is a neighborhood of `(base,0)`.  The product-neighborhood basis gives a base
neighborhood `U` and a regular-coordinate neighborhood `V` with
`U x V` inside this set.  Since the regular-coordinate type is a pseudo-metric
space, choose `R0 > 0` with

```text
Metric.ball 0 R0 subset V.
```

For a prescribed `Rmax > 0`, set

```text
R := min R0 Rmax.
```

Then `0 < R` and `R <= Rmax`.  For all `x` in the base neighborhood and all
regular coordinates `u` with `u in Metric.ball 0 R`, we have

```text
d_rho <= density(x,u),
density(x,u) <= D_rho.
```

Restricting from `nhds base` to `nhdsWithin base sourceStratum` preserves these
eventual bounds.

## Handoff Calculation

For the retained-passive source-edge-family chart

```text
sourceChart y :=
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
    W B U0 hU0 (retainedData y),
```

the already banked chart-produced source-stratum theorem supplies the final
two-sided local handoff once the following hypotheses are present at the same
regular radius:

```text
residualSquareSum(x) <= R^2
```

for a.e. `x` with respect to the chart-produced measure restricted to the
retained-passive local source, the lower and upper source-stratum loss bounds,
and the lower and upper density bounds.

The loss bounds may be supplied at `Rmax`; since `R <= Rmax`, the ball
inclusion

```text
Metric.ball 0 R subset Metric.ball 0 Rmax
```

restricts both loss bounds to the produced radius `R`.

The residual bound cannot be shrunk from a bound at `Rmax`: the implication
`residual <= Rmax^2` does not imply `residual <= R^2` when `R <= Rmax`.
Therefore the theorem produces `R, d_rho, D_rho` first and keeps the residual
boundedness hypothesis explicit at that produced radius.

The conclusion is an open `U` around `base` such that

```text
actual loss-density integral over (mu.restrict (U inter sourceStratum)).prod nu < infinity
iff
residualNegPowerIntegrableOn (fun E => E) (U inter sourceStratum) mu t.
```

## Lean Shape

Lean formalises the local density shrink in:

```text
lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
```

Main helper:

```text
exists_pos_radius_le_eventually_nhdsWithin_density_two_sided_bounds_of_continuousAt_pos
```

The retained-passive wrapper is in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
```

Main theorem:

```text
exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_of_sourceEdgeFamilyOfData_chartProducedMeasure_continuousAt_pos_density
```

The proof:

1. uses the new local helper on `sourceStratum`;
2. restricts the two supplied loss comparison bounds from `Rmax` to the
   produced `R`;
3. applies the banked retained-passive source-edge-family chart-produced
   source-stratum two-sided iff with `Rreg := R`, `d_rho`, and `D_rho`;
4. leaves the residual boundedness premise explicit at the produced `R`.

Focused builds passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.LocalMeasureHandoff
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure
```

## Nonclaims

- No proof of residual boundedness at the produced radius.
- No proof of the lower or upper source-stratum loss comparison bounds.
- No selected-entry critical inequality or residual integrability theorem.
- No signed-box source/image equality, source-rank coverage, or chart atlas
  construction.
- No source-prior, Jacobian, density, or product-measure transport theorem.
- No original-loss identification.
- No normal-crossing theorem, pole-order theorem, or RLCT extraction.
