# Reproduction - A4 Case 2 continuing reindexed source-chart unit certificate

Date: 2026-06-23.

Status: reproduced, formalised, and reviewed.

Review:
`review-case2-continuing-reindexed-source-chart-unit-certificate-a4.md`.

## Source Anchor

Aoyagi PDF p. 5 uses the sum of squares of analytic generators as the ideal
norm convention.  In Case 2 on PDF pp. 19-22, the displayed selected-entry
chart sends the pivot residual-block coordinate `(J+1,J+1)` to
`u_{S,J+1}` and every other residual-block coordinate to `u_{S,J+1}` times a
new residual coordinate.  The existing continuing reindexed source-chart
certificate packages the displayed chart formulas, the finite-center
principalization facts, corrected post-data, and the reindexed next
same-stage source-product equality.

This slice adds only the pointwise unit witness for the normalized
selected-entry center-square factor already isolated in the preceding
microcertificate.

## Pen-and-Paper Calculation

Let

```text
E = case2ResidualBlockPivotEntries n S J \ {(J+1,J+1)}.
```

Under the displayed Case 2 chart, the residual-block center square has the
finite factorization

```text
sum x_i^2 = u^2 * (1 + sum_{e in E} y_e^2).
```

The previous unit-factor slice proved, over an ordered field, that

```text
U(y) = 1 + sum_{e in E} y_e^2
```

is positive, nonzero, and therefore a field unit.  The continuing reindexed
source-chart certificate already supplies the displayed selected-entry chart
and the reindexed product data.  Therefore an ordered-field refinement of that
certificate may carry, in addition to its existing A4-local fields, the three
pointwise facts

```text
0 < U(y),
U(y) != 0,
IsUnit U(y).
```

No new source calculation is required beyond combining:

- the existing continuing reindexed source-chart certificate; and
- the selected-entry center unit-factor proof for the erased residual-block
  center.

## Boundary

This is an A4-local certificate refinement.  It does not prove:

- analytic chart coverage or transition regularity;
- analytic nonvanishing on a constructed neighbourhood beyond the pointwise
  ordered-field unit fact;
- unit control for Aoyagi's later regular `P` and `Q` changes;
- a total loss unit or full loss monomial identity;
- a differentiable Jacobian or volume-form theorem;
- an `AoyagiNormalCrossingChartCertificate`;
- pole order or RLCT extraction.

The result is useful as one input toward an A0 chart certificate, but it is
not the chart certificate itself.

## Lean Names

```text
Case2DisplayedContinuingReindexedSourceChartUnitCertificate
sourceChartMap_continuingReindexedSourceChartUnitCertificate
```

## Kill Conditions

- Do not state this over unordered or arbitrary fields.
- Do not read the carried unit witness as unit control for the later `P`/`Q`
  regular changes.
- Do not use this as chart coverage, normal crossings, pole order, or RLCT
  extraction.
