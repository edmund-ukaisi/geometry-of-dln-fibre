# Reproduction - A2 local-source selected-entry signed-box two-sided loss-density iff

Date: 2026-06-29.

Status: pen-and-paper checked; Lean formalised.

## Source Anchor

The selected-entry chart is the elementary monomial chart used in the Aoyagi
p.13 residual block after a pivot entry has been selected.  This step is not a
new integrability computation.  It specializes the local-source signed-box
two-sided p.13 loss-density iff to the selected-entry residual model.

## Calculation

For a selected pivot `pivot : center`, the selected-entry residual model has

```text
residual(pivot, y)
  = residualUnit(pivot, y)
      * product_i |y_i|^(2 * lossExp(pivot, i)).
```

The elementary selected-entry unit estimate gives

```text
1 <= residualUnit(pivot, y).
```

Therefore

```text
1 * product_i |y_i|^(2 * lossExp(pivot, i))
  <= residual(pivot, y).
```

The theorem assumes the residual readout

```text
residualSquareSum(sourceChart y) = residual(pivot, y).
```

so the selected-entry calculation supplies the monomial lower bound required
by the positivity-only signed-box source theorem:

```text
1 * product_i |y_i|^(2 * lossExp(pivot, i))
  <= residualSquareSum(sourceChart y).
```

No selected-entry critical inequality is used here.  The critical inequality
would prove residual negative-power integrability for the whole signed box,
which would collapse the two-sided iff into a finite-side theorem.  Here
residual negative-power integrability stays on the right-hand side of the iff.

The reverse side of the Fubini equivalence still needs the explicit local
boundedness input

```text
residualSquareSum x <= Rreg^2
```

on `mu.restrict source`.

With four supplied two-sided p.13 bounds on `nhdsWithin x0 source`,

```text
cLreg * (residualSquareSum(x) + regularSquareSum(u)) <= loss(x,u),
loss(x,u) <= CLreg * (residualSquareSum(x) + regularSquareSum(u)),
dRho <= density(x,u),
density(x,u) <= DRho,
```

the local-source signed-box two-sided theorem gives an open `U` such that

```text
actual loss-density integral over (mu.restrict (U inter source)).prod nu < infinity
iff
residualNegPowerIntegrableOn Cedge (U inter source) mu t.
```

## Lean Shape

Lean formalises this in:

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntrySignedBoxLocalMeasure.lean
```

Main theorem:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_localSource_selectedEntryCenter_signedBox_withDensity_edgeMatrix
```

The proof:

1. extracts the selected-entry monomial lower bound from
   `SelectedEntrySignedBox.CenterCoord.monomialLower_sourceDensityBounds`;
2. rewrites that lower bound through the supplied `hresidual_eq`;
3. applies the local-source signed-box two-sided iff with `cres := 1` and
   `kres := SelectedEntrySignedBox.CenterCoord.lossExp pivot`.

Focused build:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntrySignedBoxLocalMeasure
```

passed after the Lean change.

## Nonclaims

- No proof of a selected-entry chart construction for an Aoyagi source stratum.
- No proof of source coverage or source/image equality.
- No proof of the signed-box pushforward identity.
- No proof of residual boundedness or the four p.13 loss/density comparison
  bounds.
- No use or proof of selected-entry critical integrability.
- No source-prior, Jacobian, density, or product-measure transport theorem.
- No original-loss identification.
- No normal-crossing theorem, pole-order theorem, or RLCT extraction.
