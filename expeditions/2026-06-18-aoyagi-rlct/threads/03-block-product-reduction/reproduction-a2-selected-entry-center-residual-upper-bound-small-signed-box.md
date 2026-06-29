# Reproduction - A2 selected-entry center residual upper bound on small signed boxes

Date: 2026-06-29.

Status: pen-and-paper checked; Lean formalised.

## Source Anchor

This is the elementary finite selected-entry calculation behind the residual
boundedness premise in the retained-passive p.13 handoff.  It is a bound on
the selected-entry chart residual on a sufficiently small signed box.  It does
not construct a retained-passive source chart, identify a source prior,
prove residual integrability, build normal crossings, or extract an RLCT.

## Calculation

Let `center` be finite and let `pivot : center`.  The center-indexed
selected-entry chart sends

```text
y_pivot |-> y_pivot,
y_i     |-> y_pivot * y_i       for i != pivot.
```

The selected-entry residual square-sum is

```text
residual(y)
  = y_pivot^2 * (1 + sum_{i in center.erase pivot} y_i^2).
```

Assume a nonnegative number `delta` bounds all center coordinates:

```text
|y_i| <= delta    for all i in center.
```

Then

```text
y_pivot^2 <= delta^2
sum_{i in center.erase pivot} y_i^2
  <= #(center.erase pivot) * delta^2.
```

Therefore

```text
residual(y)
  <= delta^2 * (1 + #(center.erase pivot) * delta^2).
```

If this last quantity is at most `R^2`, then `residual(y) <= R^2`.

For a signed box with radii `Rres`, membership in

```text
signedBoxSet Rres = {y | forall i, -Rres_i < y_i < Rres_i}
```

gives `|y_i| < Rres_i`.  Hence if `Rres_i <= delta` for every coordinate, the
pointwise bound applies.

The a.e. signed-box version follows because the product signed-box measure is
Lebesgue measure restricted to `signedBoxSet Rres`.  The weighted source-box
version follows from absolute continuity of

```text
signedBox.withDensity (ofReal (sourceDensity pivot))
```

with respect to the unweighted signed-box measure.

## Lean Shape

Lean formalises this in:

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntrySignedBoxMeasure.lean
```

Main lemmas:

```text
SelectedEntrySignedBox.CenterCoord.residual_le_sq_of_abs_le
SelectedEntrySignedBox.CenterCoord.residual_le_sq_of_mem_signedBoxSet
SelectedEntrySignedBox.CenterCoord.residual_le_sq_ae_signedBox_of_smallBox
SelectedEntrySignedBox.CenterCoord.residual_le_sq_ae_withDensity_sourceDensity_of_smallBox
```

The proof uses `selectedEntryCenterSq_selectedEntryChartMap` to factor the
residual, then bounds the non-pivot square-sum termwise.  The signed-box a.e.
statement uses `signedBoxMeasure_eq_volume_restrict`,
`measurableSet_signedBoxSet`, and `ae_restrict_mem`.  The weighted statement
uses `withDensity_absolutelyContinuous`.

Focused build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntrySignedBoxMeasure
```

## Nonclaims

- No selected-entry critical inequality or residual negative-power
  integrability theorem.
- No retained-passive source-chart construction or source-image theorem.
- No source-rank coverage theorem.
- No original source-prior, Jacobian, density, or product-measure transport.
- No original-loss identification.
- No normal-crossing theorem, pole-order theorem, or RLCT extraction.
