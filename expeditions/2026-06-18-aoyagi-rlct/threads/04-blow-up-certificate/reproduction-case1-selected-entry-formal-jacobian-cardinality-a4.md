# A4 Case 1 selected-entry formal Jacobian cardinality

Status: reproduced the finite determinant/cardinality calculation for the two
Case 1 displayed selected charts.

## Source Situation

Aoyagi's Case 1 center contains one old exceptional generator and the row
strip

```text
d_ij = 0,    J+1 <= i <= J+J1,    J+1 <= j <= M^(S+1),
u_(s,k) = 0.
```

The two displayed Case 1 charts are:

- Case 1(1), selecting the old exceptional variable `u_(s,k)`;
- Case 1(2), selecting the top-left row-strip pivot `d_(J+1,J+1)`.

Aoyagi prints the same numerator increment in both displayed branches:

```text
J1 * (M^(S+1) - J).
```

This note isolates only the finite selected-entry determinant contribution
behind that count.  It is not an analytic Jacobian or volume-form theorem.

## Pen-And-Paper Count

The row range has cardinality `J1`:

```text
J+1, ..., J+J1.
```

The column range has cardinality `M^(S+1)-J`:

```text
J+1, ..., M^(S+1).
```

Therefore the row-strip entries have cardinality

```text
r = J1 * (M^(S+1)-J).
```

The full finite Case 1 center has `1+r` generators: one old exceptional
generator plus the row-strip entries.

In the selected-entry chart at the old exceptional generator, the `r` row-strip
coordinates are multiplied by the selected variable.  The formal pivot-first
Jacobian determinant is therefore

```text
u_(s,k)^r.
```

In the selected-entry chart at the displayed row-strip pivot, the pivot is not
part of the residual coordinate list.  The other `r-1` row-strip entries and
the old exceptional generator are multiplied by the selected pivot.  The
formal pivot-first Jacobian determinant is therefore

```text
u_(S,J+1)^((r-1)+1) = u_(S,J+1)^r.
```

Thus both displayed Case 1 selected charts have finite formal determinant
exponent

```text
J1 * (M^(S+1)-J).
```

This matches the cardinal part of Aoyagi's printed Case 1 numerator increment.
The remaining numerator arithmetic is the already formalised lower-tail
terminal-exponent calculation.

## Lean Boundary

Lean records the finite cardinality facts:

```text
case1StripRows_card
case1StripCols_card
case1StripEntries_card
case1CenterGenerators_card
case1CenterGenerators_erase_card_of_mem
case1CenterGenerators_erase_selectedOld_card
case1CenterGenerators_erase_displayedPivot_card_of_bounds
```

It also specializes the local selected-entry finite normal-crossing
microcertificate to the two displayed Case 1 charts:

```text
case1SelectedOldCenterSqFormalJacobianChartCertificate
case1SelectedOldCenterSqFormalJacobianChartCertificate.jacobianPriorExp_zero_zero
case1SelectedOldCenterSqFormalJacobianChartCertificate.pivotFirstJacobian_det

case1DisplayedRowStripCenterSqFormalJacobianChartCertificate
case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.jacobianPriorExp_zero_zero
case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.pivotFirstJacobian_det
```

The determinant theorem used is the existing finite selected-entry matrix
calculation:

```text
selectedEntryPivotFirstJacobian_det
```

## Caveats

- No chart coverage is proved.
- No source construction of the hidden old selected label is proved.
- No chart-produced recurrence or exponent post-data is proved.
- No analytic Jacobian, derivative, or volume-form theorem is proved.
- No transition regularity, normal crossings, pole order, or RLCT extraction
  is proved.
