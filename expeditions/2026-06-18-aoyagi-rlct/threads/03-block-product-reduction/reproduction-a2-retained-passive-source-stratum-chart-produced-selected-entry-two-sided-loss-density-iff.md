# Reproduction - A2 retained-passive source-stratum chart-produced selected-entry two-sided loss-density iff

Date: 2026-06-29.

Status: pen-and-paper checked; Lean formalised.

## Source Anchor

This is the chart-produced version of the retained-passive source-stratum-bound
selected-entry two-sided p.13 loss-density iff.  It is only measure-support
bookkeeping for the selected-entry weighted signed-box pushforward; it adds no
new analytic or selected-entry critical-integrability content.

## Calculation

Let

```text
signedBox := product_i volume restricted to (-R_i, R_i),
sourceMeasure := signedBox.withDensity selectedEntrySourceDensity,
mu := Measure.map sourceChart sourceMeasure,
localSource := paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U0 hU0 Cedge,
sourceStratum := paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge.
```

Assume pointwise retained-passive chart landing:

```text
forall y, sourceChart y in localSource.
```

Since

```text
sourceMeasure = signedBox.withDensity selectedEntrySourceDensity
```

is absolutely continuous with respect to `signedBox`, a.e. measurability of
`sourceChart` for `signedBox` gives a.e. measurability for `sourceMeasure`.
Pointwise chart landing gives an a.e. support statement for the map measure,
and therefore

```text
mu.restrict localSource = Measure.map sourceChart sourceMeasure.
```

This is exactly the local-source restriction equality required by the already
formalised retained-passive source-stratum-bound selected-entry two-sided iff.
The wrapper then applies that theorem.

The residual readout remains supplied:

```text
residualSquareSum(sourceChart y)
  = SelectedEntrySignedBox.CenterCoord.residual pivot y.
```

Residual boundedness remains an explicit hypothesis on the chart-produced
measure restricted to the retained-passive local source:

```text
residualSquareSum x <= Rreg^2
```

for a.e. `x` with respect to `mu.restrict localSource`.

The four two-sided comparison bounds remain stated on the source-rank stratum:

```text
cLreg * (residualSquareSum(x) + regularSquareSum(u)) <= loss(x,u),
loss(x,u) <= CLreg * (residualSquareSum(x) + regularSquareSum(u)),
dRho <= density(x,u),
density(x,u) <= DRho
```

as eventual statements in `nhdsWithin x0 sourceStratum`.

The conclusion is an open `U` with

```text
actual loss-density integral over (mu.restrict (U inter sourceStratum)).prod nu < infinity
iff
residualNegPowerIntegrableOn Cedge (U inter sourceStratum) mu t.
```

The retained-passive self-base coverage and source-stratum transfer are not
proved in this wrapper; they are in the banked source-stratum-bound theorem
being called.

## Lean Shape

Lean formalises this in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
```

Main theorem:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure
```

The proof:

1. defines `signedBox`, `sourceMeasure`, `mu`, and `localSource`;
2. transfers a.e. measurability of `sourceChart` from `signedBox` to
   `sourceMeasure` using absolute continuity of `withDensity`;
3. derives `mu.restrict localSource = Measure.map sourceChart sourceMeasure`
   from pointwise chart landing;
4. applies the retained-passive source-stratum-bound selected-entry two-sided
   iff with the residual boundedness and source-stratum comparison bounds
   unchanged.

Focused build:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure
```

passed after the Lean change.

## Nonclaims

- No proof that the selected-entry chart lands in the retained-passive local
  source.
- No proof of the residual readout.
- No proof of residual boundedness or the four source-stratum comparison
  bounds.
- No selected-entry critical inequality, positive signed-box-radius, or
  residual integrability conclusion.
- No signed-box source/image equality, source-rank coverage, or chart atlas
  construction.
- No source-prior, Jacobian, density, or product-measure transport theorem
  beyond this chart-produced local-source restriction identity.
- No original-loss identification.
- No normal-crossing theorem, pole-order theorem, or RLCT extraction.
