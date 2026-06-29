# Reproduction - A2 retained-passive local-source selected-entry two-sided loss-density iff

Date: 2026-06-29.

Status: pen-and-paper checked; Lean formalised.

## Source Anchor

This is a retained-passive specialization of the selected-entry local-source
two-sided p.13 loss-density iff.  It is not a new selected-entry integrability
calculation and it is not a source-coverage theorem.

The retained-passive local source is

```text
paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U0 hU0 Cedge.
```

It is a concrete local source cut out by the retained-passive determinant-chart
setup.  For the two-sided local-source socket, the retained-passive layer only
has to provide the measurability of this source and the measurability of the
fixed-basis edge matrix readout.

## Calculation

Let

```text
localSource := paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U0 hU0 Cedge.
```

Continuity of `Cedge` gives

```text
MeasurableSet localSource
```

by the retained-passive local-source measurability theorem, and also gives

```text
Measurable
  (fun x =>
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges
      W B U0 hU0 (fun p => Cedge x p)).
```

These are exactly the two source-specific hypotheses required by the
selected-entry local-source two-sided theorem.

All analytic and chart-measure content remains supplied:

```text
mu.restrict localSource
  = Measure.map sourceChart
      (signedBox.withDensity
        (fun y => ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivot y))),
```

the residual readout

```text
residualSquareSum(sourceChart y)
  = SelectedEntrySignedBox.CenterCoord.residual pivot y,
```

the local residual boundedness

```text
residualSquareSum x <= Rreg^2
```

on `mu.restrict localSource`, and the four two-sided p.13 comparison bounds on
`nhdsWithin x0 localSource`:

```text
cLreg * (residualSquareSum(x) + regularSquareSum(u)) <= loss(x,u),
loss(x,u) <= CLreg * (residualSquareSum(x) + regularSquareSum(u)),
dRho <= density(x,u),
density(x,u) <= DRho.
```

After substituting `source := localSource`, the selected-entry local-source
theorem returns an open `U` with

```text
actual loss-density integral over (mu.restrict (U inter localSource)).prod nu < infinity
iff
residualNegPowerIntegrableOn Cedge (U inter localSource) mu t.
```

No selected-entry critical inequality enters this handoff.  No positive
signed-box radius, source-density nonnegativity/upper bound, residual
integrability, local coverage, or source-rank-stratum transport is derived.

## Lean Shape

Lean formalises this in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
```

Main theorem:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity
```

The proof:

1. defines `localSource` as the retained-passive p.13 local source;
2. derives `MeasurableSet localSource` from `hCedge`;
3. derives fixed-basis edge-matrix measurability from `hCedge`;
4. applies the selected-entry local-source two-sided iff with
   `source := localSource`.

Focused build:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure
```

passed after the Lean change.

## Nonclaims

- No proof of the signed-box pushforward identity.
- No proof of the residual readout.
- No proof of residual boundedness or the four two-sided comparison bounds.
- No selected-entry critical inequality, positive signed-box-radius, or
  residual integrability conclusion.
- No retained-passive source coverage, source-rank coverage, or source/image
  equality.
- No source-prior, Jacobian, density, or product-measure transport theorem.
- No original-loss identification.
- No normal-crossing theorem, pole-order theorem, or RLCT extraction.
