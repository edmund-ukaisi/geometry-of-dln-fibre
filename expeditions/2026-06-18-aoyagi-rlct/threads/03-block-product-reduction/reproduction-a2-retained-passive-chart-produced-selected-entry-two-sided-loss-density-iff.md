# Reproduction - A2 retained-passive chart-produced selected-entry two-sided loss-density iff

Date: 2026-06-29.

Status: pen-and-paper checked; Lean formalised.

## Source Anchor

This is a chart-produced specialization of the retained-passive local-source
selected-entry two-sided p.13 loss-density iff.  It is only measure-support
bookkeeping for a measure already defined as the selected-entry weighted
signed-box pushforward.

## Calculation

Let

```text
signedBox := product_i volume.restrict (-R_i, R_i),
sourceMeasure := signedBox.withDensity
  (fun y => ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivot y)),
mu := Measure.map sourceChart sourceMeasure,
localSource := paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U0 hU0 Cedge.
```

The theorem assumes pointwise chart landing:

```text
forall y, sourceChart y in localSource.
```

Since `sourceMeasure << signedBox`, a.e. measurability of `sourceChart` for
`signedBox` gives a.e. measurability for `sourceMeasure`.  The pointwise
landing hypothesis gives

```text
forall^ae x with respect to Measure.map sourceChart sourceMeasure,
  x in localSource.
```

Therefore

```text
mu.restrict localSource = Measure.map sourceChart sourceMeasure.
```

This is exactly the pushforward/restriction equality required by the
retained-passive local-source selected-entry two-sided theorem.

All analytic and comparison content remains supplied:

```text
residualSquareSum(sourceChart y)
  = SelectedEntrySignedBox.CenterCoord.residual pivot y,
```

the residual local boundedness on the chart-produced measure restricted to
`localSource`,

```text
residualSquareSum x <= Rreg^2,
```

and the four two-sided p.13 comparison bounds on `nhdsWithin x0 localSource`.
The conclusion is an open `U` with

```text
actual loss-density integral over (mu.restrict (U inter localSource)).prod nu < infinity
iff
residualNegPowerIntegrableOn Cedge (U inter localSource) mu t.
```

No selected-entry critical inequality, signed-box radius positivity, residual
integrability, source-rank coverage, source-prior transport, normal crossings,
pole order, or RLCT enters this handoff.

## Lean Shape

Lean formalises this in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
```

Main theorem:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure
```

The proof:

1. defines `signedBox`, `sourceMeasure`, `mu`, and `localSource`;
2. transfers a.e. measurability of `sourceChart` from `signedBox` to
   `sourceMeasure` using absolute continuity of `withDensity`;
3. derives the local-source restriction equality from pointwise chart landing;
4. applies the retained-passive local-source selected-entry two-sided iff.

Focused build:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure
```

passed after the Lean change.

## Nonclaims

- No proof that the selected-entry chart lands in the local source.
- No proof of the residual readout.
- No proof of residual boundedness or the four two-sided comparison bounds.
- No selected-entry critical inequality, positive signed-box-radius, or
  residual integrability conclusion.
- No retained-passive source coverage, source-rank coverage, or source/image
  equality.
- No source-prior, Jacobian, density, or product-measure transport theorem
  beyond this chart-produced restriction identity.
- No original-loss identification.
- No normal-crossing theorem, pole-order theorem, or RLCT extraction.
