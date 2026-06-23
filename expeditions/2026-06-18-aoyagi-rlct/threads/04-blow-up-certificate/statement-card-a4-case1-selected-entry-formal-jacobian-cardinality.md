# Statement card - A4 Case 1 selected-entry formal Jacobian cardinality

## Lean Artifacts

Files:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`

Names:

- `DLNFibre.DLN.Aoyagi.case1StripRows_card`
- `DLNFibre.DLN.Aoyagi.case1StripCols_card`
- `DLNFibre.DLN.Aoyagi.case1StripEntries_card`
- `DLNFibre.DLN.Aoyagi.case1CenterGenerators_card`
- `DLNFibre.DLN.Aoyagi.case1CenterGenerators_erase_card_of_mem`
- `DLNFibre.DLN.Aoyagi.case1CenterGenerators_erase_selectedOld_card`
- `DLNFibre.DLN.Aoyagi.case1CenterGenerators_erase_displayedPivot_card_of_bounds`
- `DLNFibre.DLN.Aoyagi.case1SelectedOldCenterSqFormalJacobianChartCertificate`
- `DLNFibre.DLN.Aoyagi.case1SelectedOldCenterSqFormalJacobianChartCertificate.jacobianPriorExp_zero_zero`
- `DLNFibre.DLN.Aoyagi.case1SelectedOldCenterSqFormalJacobianChartCertificate.pivotFirstJacobian_det`
- `DLNFibre.DLN.Aoyagi.case1DisplayedRowStripCenterSqFormalJacobianChartCertificate`
- `DLNFibre.DLN.Aoyagi.case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.jacobianPriorExp_zero_zero`
- `DLNFibre.DLN.Aoyagi.case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.pivotFirstJacobian_det`

## Statement

Lean proves that the finite Case 1 row strip has cardinality

```text
J1 * (n(S+1)-J),
```

and that erasing any selected Case 1 center generator leaves exactly that many
non-pivot center generators.

For the two displayed Case 1 selected charts, the local finite
normal-crossing microcertificate has formal Jacobian/prior exponent

```text
J1 * (n(S+1)-J).
```

Equivalently, the formal pivot-first selected-entry determinant is the
selected chart variable raised to that exponent.

## Source Role

This is the finite determinant/cardinality component behind Aoyagi's printed
Case 1 increment on PDF pp. 16-17.  It complements the already formalised
lower-tail terminal-exponent increment.

## Proved

- Case 1 row-strip row, column, and entry cardinalities.
- Case 1 finite center cardinality.
- The erased-center cardinality for any selected Case 1 center generator.
- Old-exceptional and displayed row-strip pivot corollaries.
- Local one-chart selected-entry certificates for those two Case 1 charts.
- Formal pivot-first determinant exponent for those two finite charts.

## Assumed

- For the displayed row-strip pivot, the finite entry bounds
  `1 <= J1` and `J+1 <= n(S+1)`.

## Not Proved

- No chart coverage or affine atlas construction.
- No source construction of the hidden old selected label.
- No chart-produced recurrence or exponent post-data.
- No analytic Jacobian, derivative, or volume-form theorem.
- No transition regularity, normal crossings, pole order, or RLCT extraction.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case1-selected-entry-formal-jacobian-cardinality-a4.md`.
- Review artifact:
  `review-case1-selected-entry-formal-jacobian-cardinality-a4.md`.

## Verification

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
```
