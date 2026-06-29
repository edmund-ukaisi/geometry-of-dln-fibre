# Reproduction - A2 retained-passive source-stratum selected-entry two-sided loss-density iff

Date: 2026-06-29.

Status: pen-and-paper checked; Lean formalised.

## Source Anchor

This is a source-rank-stratum-bound version of the retained-passive
selected-entry two-sided p.13 loss-density iff.  The retained-passive local
source supplies the residual chart; the loss and density comparison bounds are
stated on Aoyagi's source-rank stratum.

This is not a source-coverage theorem for the signed-box chart.  The only
coverage used is the already-formalised retained-passive local-source
neighborhood around a self-base point.

## Calculation

Let

```text
localSource := paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U0 hU0 Cedge,
sourceStratum := paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge.
```

Continuity of `Cedge` gives measurability of `sourceStratum` and of the
fixed-basis edge matrix readout.  The latter gives measurability of the
residual square-sum on `localSource`.

The selected-entry residual-unit calculation gives

```text
1 * product_i |y_i|^(2 * lossExp(pivot,i))
  <= SelectedEntrySignedBox.CenterCoord.residual pivot y.
```

Using the supplied residual readout

```text
residualSquareSum(sourceChart y)
  = SelectedEntrySignedBox.CenterCoord.residual pivot y,
```

this becomes the monomial lower bound needed to show

```text
0 < residualSquareSum x
```

for `mu.restrict localSource`, via the supplied selected-entry signed-box
pushforward identity

```text
mu.restrict localSource
  = Measure.map sourceChart
      (signedBox.withDensity selectedEntrySourceDensity).
```

The theorem does not use the selected-entry critical inequality.  It also does
not use source-density upper or nonnegativity hypotheses, because it proves no
residual negative-power integrability on `localSource`; it only proves
residual positivity.

Residual boundedness stays explicit:

```text
residualSquareSum x <= Rreg^2
```

on `mu.restrict localSource`.

The self-base retained-passive coverage theorem gives an open `Ulocal`
containing `x0` such that

```text
Ulocal inter sourceStratum subset Ulocal inter localSource.
```

The source-stratum/local-source two-sided theorem then transfers the residual
hypotheses through this inclusion and combines them with the four supplied
source-stratum comparison bounds:

```text
cLreg * (residualSquareSum(x) + regularSquareSum(u)) <= loss(x,u),
loss(x,u) <= CLreg * (residualSquareSum(x) + regularSquareSum(u)),
dRho <= density(x,u),
density(x,u) <= DRho.
```

The conclusion is an open `U` with

```text
actual loss-density integral over (mu.restrict (U inter sourceStratum)).prod nu < infinity
iff
residualNegPowerIntegrableOn Cedge (U inter sourceStratum) mu t.
```

## Lean Shape

Lean formalises this in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
```

Main theorem:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds
```

The proof:

1. derives source-rank-stratum measurability from `Continuous Cedge`;
2. derives edge-matrix and residual-square-sum measurability from
   `Continuous Cedge`;
3. obtains selected-entry residual positivity on `localSource` from the
   selected-entry monomial lower bound and the supplied residual readout;
4. obtains the retained-passive local coverage neighborhood from the self-base
   hypothesis;
5. applies the source-stratum/local-source two-sided theorem.

Focused build:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure
```

passed after the Lean change.

## Nonclaims

- No proof of the signed-box pushforward identity.
- No proof of the residual readout.
- No proof of residual boundedness or the four source-stratum comparison
  bounds.
- No selected-entry critical inequality, positive signed-box-radius, or
  residual integrability conclusion.
- No signed-box chart construction, source/image equality, or source-rank
  coverage beyond the explicit retained-passive local coverage theorem.
- No source-prior, Jacobian, density, or product-measure transport theorem.
- No original-loss identification.
- No normal-crossing theorem, pole-order theorem, or RLCT extraction.
