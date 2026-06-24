# Pen-and-paper reproduction - A4 Case 2 weighted source-residual successor following product

Status: reproduced and formalised.

## Source Anchor

Aoyagi PDF pp. 19-22, Case 2.  The relevant displayed calculation is the
local product after forming `C' = Q^-1 C` and clearing the pivot:

```text
diag(b') D''' C'.
```

This note only rewrites the lower-row, post-pivot part of that product in
source-coordinate notation.

## Reproduction

The existing weighted lower-row identity says that, after deleting the pivot
row and reindexing to the next same-stage residual rows,

```text
lowerRows(diag(b0,b) D''' C')
  =
diag(b_tail) *
  (displayedPostPivotResidualBlock * postPivotTail(C')).
```

For Aoyagi's paper transported factor `C' = Q^-1 C`, the post-pivot tail is
unchanged by replacing the pivot row:

```text
postPivotTail(C')
  =
case2SourceFollowingFactor(S,J+1,C).
```

The formula-level successor following factor `Csucc` differs from `C` only in
source row `J+1`.  The following-factor restriction at `(S,J+1)` starts after
that row, so

```text
case2SourceFollowingFactor(S,J+1,Csucc)
  =
case2SourceFollowingFactor(S,J+1,C).
```

The displayed post-pivot residual block is also the restriction of the
zero-extended source-coordinate representative:

```text
case2SourceResidualBlock(S,J+1,postPivotSourceResidual)
  =
displayedPostPivotResidualBlock.
```

Substituting these three equalities gives the source-pair weighted form:

```text
lowerRows(diag(b0,b) D''' C')
  =
diag(b_tail) *
  (case2SourceResidualBlock(S,J+1,postPivotSourceResidual)
    *
   case2SourceFollowingFactor(S,J+1,Csucc)).
```

For the source-chart handoff, the same rewrite is applied to the already
proved displayed `Q/P` lower-row identity carrying corrected exponent, level,
least-value-gap, and recurrence-gap post-data.

## Boundary Checks

- This is finite lower-row algebra only.
- The row diagonal remains explicit; the pivot row and old top rows are not
  included.
- `postPivotSourceResidual` and `Csucc` remain formula-level data, not
  chart-produced successor coordinates.
- No next-center nonemptiness, source suffix, full `C'^(S+1)`, transition
  invariant, Jacobian/volume theorem, normal-crossing certificate, pole order,
  termination, or RLCT extraction is proved.

## Kill Conditions

- Do not treat this as chart production or analytic atlas coverage.
- Do not infer the full source-ordered successor object from this lower-row
  identity.
- Do not use the Lehalleur-Rimanyi/quiver paper or quiver Lean as evidence.

## Lean Names

```text
case2WeightedDppp_mul_Cprime_postPivot_eq_sourceResidualBlock_succFollowing
sourceChartMap_weightedLowerRows_sourceResidualSucc_withCorrectedPostData
```
