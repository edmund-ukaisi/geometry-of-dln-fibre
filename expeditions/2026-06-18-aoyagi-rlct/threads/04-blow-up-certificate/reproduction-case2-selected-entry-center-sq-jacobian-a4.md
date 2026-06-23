# Reproduction - A4 Case 2 selected-entry center square and formal Jacobian

Date: 2026-06-23.

Status: reproduced, formalised, and xhigh-reviewed.

Review: `review-case2-selected-entry-center-sq-jacobian-a4.md`.

## Source Anchor

Aoyagi PDF p. 5 defines the ideal attached to a matrix by its entries and uses
the sum of squares of generators for the RLCT convention.  In Case 2 on
PDF pp. 19-21, the blow-up center is the residual block

```text
d_ij = 0,  i = J+1..M(S),  j = J+1..M^(S+1),
```

and the displayed chart selects the top-left residual entry:

```text
d_{J+1,J+1} = u_{S,J+1},
d_{i,j} = u_{S,J+1} d'_{i,j}  for all other residual-block entries.
```

This slice records the elementary square-sum and formal determinant
calculation for that selected-entry chart.  It does not use the quiver paper
or any quiver Lean result.

## Pen-and-Paper Calculation

Let `E` be a finite center and `p in E` the selected pivot.  Write the original
center coordinates as `x_i`.  The selected-entry chart has coordinates
`u` and `y_i` for `i != p`, with

```text
x_p = u,
x_i = u y_i  for i != p.
```

The squared center norm used by Aoyagi's ideal convention pulls back as

```text
sum_{i in E} x_i^2
  = u^2 + sum_{i in E, i != p} (u y_i)^2
  = u^2 * (1 + sum_{i in E \ {p}} y_i^2).
```

Thus the selected coordinate has loss exponent `1` in the A0 convention where
the certificate writes the loss monomial as `coord ^ (2 * lossExp)`.  The
factor

```text
1 + sum y_i^2
```

is only a unit candidate at this finite algebra layer.  Proving that it is an
analytic unit on an actual real chart neighbourhood is a later chart/analytic
obligation, not part of this slice.

For the formal Jacobian matrix, order coordinates as `(u, y_i)_{i != p}` and
outputs as `(x_p, x_i)_{i != p}`.  The matrix is block lower triangular:

```text
[ 1   0 ]
[ y   u I ].
```

Its determinant is

```text
u^(|E|-1).
```

For Aoyagi's displayed Case 2 center, the non-pivot count is

```text
card(case2ResidualBlockPivotEntries n S J) - 1.
```

Earlier A4 work identifies the full center cardinality with

```text
(prefixMinNat n S - J) * (n (S+1) - J)
```

under the displayed continuation hypotheses, so this determinant exponent is
the corrected center count minus one.  This slice records the first equality
and the erase-cardinality equality; it does not repackage the product formula
as a new theorem.

## Lean Names

```text
selectedEntryCenterSq
selectedEntryCenterSq_selectedEntryChartMap
selectedEntryPivotFirstJacobian
selectedEntryPivotFirstJacobian_det
SelectedEntryChartFamilyData.centerSq_chartMap
case2DisplayedSourceChartMap_centerSq
case2DisplayedSourceChartMap_pivotFirstJacobian_det
case2DisplayedSourceChartMap_pivotFirstJacobian_exponent_eq_centerCard_sub_one
```

## Boundary

This is finite algebra only:

- no analytic norm theorem;
- no proof that the normalized square-sum factor is a unit on a neighbourhood;
- no actual `HasFDerivAt` or analytic Jacobian theorem;
- no chart coverage or transition regularity;
- no A0 normal-crossing chart certificate;
- no pole order or RLCT extraction.

## Kill Conditions

- If the selected-entry chart formula is changed so the non-pivot coordinates
  are not `u * residual`, the square-sum identity no longer applies.
- If a downstream theorem treats `1 + sum y_i^2` as a unit without a real local
  neighbourhood/unit witness, it overclaims this slice.
- If the determinant is interpreted as an analytic Jacobian before an actual
  coordinate map and differentiability statement are supplied, it overclaims
  this slice.
