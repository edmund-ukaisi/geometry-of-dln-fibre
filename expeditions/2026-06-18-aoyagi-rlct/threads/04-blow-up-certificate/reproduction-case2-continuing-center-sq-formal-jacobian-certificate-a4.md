# Reproduction - A4 Case 2 continuing center-square/formal-Jacobian certificate

Date: 2026-06-23.

Status: reproduced, formalised, and reviewed.

Review:
`review-case2-continuing-center-sq-formal-jacobian-certificate-a4.md`.

## Source Anchor

Aoyagi PDF p. 5 uses the sum of squares of the chosen generators as the
ideal-norm convention for RLCT bookkeeping.  In the displayed Case 2 chart on
PDF pp. 19-22, the residual-block center is

```text
d_ij = 0,  i = J+1..M(S),  j = J+1..M^(S+1),
```

and the top-left residual entry is selected:

```text
d_{J+1,J+1} = u_{S,J+1},
d_{i,j} = u_{S,J+1} d'_{i,j}  for all other residual-block entries.
```

The existing continuing reindexed source-chart certificate packages the
displayed chart formulas, finite-center principalization, corrected post-data,
and the reindexed next same-stage source-product equality.  The existing
ordered-field refinement adds the pointwise unit witness for the normalized
center-square factor.  This slice bundles those facts with the finite
center-square identity, the formal pivot-first determinant calculation, the
finite relation between the corrected numerator and the determinant exponent,
and determinant-unit bookkeeping for the displayed `Q/Q^-1` operations and the
certificate's supplied `P` row operation.

## Pen-and-Paper Calculation

Let

```text
E = case2ResidualBlockPivotEntries n S J,
p = (J+1,J+1),
E' = E \ {p}.
```

In the selected-entry chart, write the original center coordinates as

```text
x_p = u,
x_e = u y_e  for e in E'.
```

The finite square-sum attached to the residual-block center pulls back as

```text
sum_{e in E} x_e^2
  = u^2 + sum_{e in E'} (u y_e)^2
  = u^2 * (1 + sum_{e in E'} y_e^2).
```

Over an ordered field the factor

```text
U(y) = 1 + sum_{e in E'} y_e^2
```

is positive, hence nonzero, hence a field unit.  This is a pointwise finite
algebra fact; an analytic unit on a chart neighbourhood requires later chart
infrastructure.

For the formal pivot-first coordinate matrix, order input coordinates as
`(u, y_e)_{e in E'}` and output coordinates as `(x_p, x_e)_{e in E'}`.  The
finite matrix is

```text
[ 1   0  ]
[ y   uI ].
```

Therefore

```text
det = u^|E'|.
```

Since `p in E` under the displayed continuation hypothesis,

```text
|E'| = |E| - 1.
```

Equivalently,

```text
|E'| + 1 = |E|.
```

The corrected Case 2 new numerator already proved in the continuing
certificate is the integer cardinality `|E|`.  Thus the finite step
bookkeeping gives

```text
new numerator = formal determinant exponent + 1.
```

This is exactly the arithmetic shape used by the normal-crossing finite ratio
`(h+1)/(2k)` when the selected square factor contributes `k = 1` and the
formal determinant exponent is `h = |E'|`.  It is still not an analytic
Jacobian or volume-form theorem: no differentiability statement, chart
neighbourhood, transition regularity, or measure pullback is constructed here.

The displayed `Q` and `Q^-1` matrices on Aoyagi p. 20 are unitriangular finite
matrices, hence have unit determinants.  The continuing certificate's supplied
`P` row-operation witness is also a unitriangular finite matrix, hence has
unit determinant.  These facts do not prove that the full displayed p. 21
product equality has been source-produced as an analytic coordinate change.

## Source Caveat

Aoyagi pp. 20-21 should not be read as a literal polynomial identity with an
extra outside `u` unless the definitions of the primed row weights are fixed.
The p. 20 chart sets `b'_i = u b_i`, while the p. 21 display also shows an
outside factor `u diag(b'_...)`.  Taken together in a one-by-one test, this
would double-count `u`.  The Lean certificate here avoids that overclaim: it
records only the selected-entry square factor, the formal pivot-first
determinant exponent, and finite determinant-unit facts for `P/Q` operations.

## Lean Target

Bundle the existing continuing ordered-field local certificate with:

```text
selectedEntryCenterSq E (case2DisplayedSourceChartMap ... u residual)
  =
u^2 * selectedEntryCenterSqUnitFactor E' residual
```

and

```text
det (selectedEntryPivotFirstJacobian u residual) = u^|E'|,
|E'| = |E| - 1.
```

Expected Lean names:

```text
case2DisplayedPaperQ_isUnit
case2DisplayedPaperQ_det_isUnit
case2DisplayedPaperQinv_isUnit
case2DisplayedPaperQinv_det_isUnit
Case2DisplayedContinuingReindexedSourceChartCenterSqFormalJacobianCertificate
sourceChartMap_continuingReindexedSourceChartCenterSqFormalJacobianCertificate
Case2DisplayedContinuingReindexedSourceChartCertificate.exists_reindexedNextSourceProduct_with_PQ_det_units
```

## Boundary

This slice proves only finite algebra for the displayed continuing Case 2
local chart:

- no analytic chart neighbourhood;
- no chart coverage or transition regularity;
- no analytic nonvanishing beyond the pointwise ordered-field unit witness;
- no analytic unit control for the later `P` and `Q` changes;
- no total DLN loss monomial identity;
- no differentiable Jacobian or volume-form theorem;
- no A0 normal-crossing chart certificate;
- no pole order or RLCT extraction.

## Kill Conditions

- If the displayed selected-entry formula is not `x_p = u` and
  `x_e = u y_e`, the square-sum and determinant formulas do not apply.
- If downstream code interprets the formal determinant field as a proven
  analytic Jacobian/measure pullback, it overclaims this certificate.
- If downstream code treats the pointwise unit witness as chart-neighbourhood
  unit control for all Aoyagi `P`/`Q` changes, it overclaims this certificate.
- If downstream code uses this to prove the literal p. 21 displayed product
  with the apparent extra outside `u`, it overclaims this certificate.
