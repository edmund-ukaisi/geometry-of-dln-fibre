# Reproduction - A2 selected-entry chart-image characterization

Date: 2026-06-25.

Status: controller pen-and-paper reproduction for the Lean theorem.  This is
finite selected-entry chart algebra only.

## Source Anchor

Aoyagi PDF pp. 15-21 uses the selected-entry chart pattern in the residual
block:

```text
d_p = u_p,
d_i = u_p d'_i       for i != p.
```

The current Lean finite chart writes this as

```text
Phi_p(y)_p = y_p,
Phi_p(y)_i = y_p y_i     for i != p.
```

This reproduction characterizes the image of a finite signed box under this
map.  It does not assert that this image is the original source-rank stratum
or that the displayed pivot chart covers every local source branch.

## Pen-And-Paper Check

Let `R_i > 0` for every center coordinate and let

```text
B_R = { y : |y_i| < R_i for all i }.
```

If `x = Phi_p(y)` with `y in B_R`, then:

- If `y_p = 0`, then `x = 0`, because every off-pivot coordinate is
  `y_p y_i`.
- If `y_p != 0`, then `x_p = y_p`, so `x_p != 0` and `|x_p| < R_p`.
  For `i != p`,

```text
x_i / x_p = (y_p y_i) / y_p = y_i,
```

so

```text
|x_i / x_p| < R_i.
```

Conversely:

- If `x = 0`, choose `y = 0`; positivity of all `R_i` gives `y in B_R`,
  and `Phi_p(0)=0`.
- If `x_p != 0`, `|x_p| < R_p`, and

```text
|x_i / x_p| < R_i        for every i != p,
```

set

```text
y_p = x_p,
y_i = x_i / x_p          for i != p.
```

Then `y in B_R`, and `Phi_p(y)=x`.

Thus the signed-box chart image is exactly the origin together with the
nonzero-pivot horn:

```text
x in Phi_p(B_R)
iff
x = 0
or
(x_p != 0 and |x_p| < R_p and forall i != p, |x_i / x_p| < R_i).
```

## Lean Target

Add the finite chart-image theorem in
`SelectedEntrySignedBoxMeasure.lean`:

```text
SelectedEntrySignedBox.CenterCoord.mem_chartMap_image_signedBoxSet_iff
```

The theorem should assume `forall i, 0 < R i` and characterize membership in

```text
SelectedEntrySignedBox.CenterCoord.chartMap pivot ''
  SelectedEntrySignedBox.CenterCoord.signedBoxSet R
```

by the origin-or-horn formula above.

## Boundary

- No source-stratum equality or local source coverage.
- No all-pivot affine cover.
- No residual-product readout for fixed-base DLN coordinates.
- No Jacobian or measure transport beyond what is already proved for the
  finite selected-entry chart.
- No normal crossings, pole order, or RLCT.
