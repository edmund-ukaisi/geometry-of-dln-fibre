# Pen-and-paper reproduction - Case 2 constructed source following factor with old top rows

Date: 2026-06-24.

Status: controller reproduction, pending independent check.

## Source Anchor

Aoyagi PDF pp. 19-22, Case 2, performs the displayed pivot chart calculation
with the finite column operation

```text
C'_J^(S+1) = Q^-1 C_J^(S+1).
```

In the continuing branch the induction proceeds with `J` increased.  The
source-current row presentation used in Lean stacks the already-carried source
rows `1,...,J` over the displayed pivot-first old residual block; the
successor row presentation stacks the same carried rows over the transported
block `C'`.

The previous constructed-source checkpoint handled only the residual-column
part.  Its zero extension sets rows outside the residual-column interval
`J+1,...,M^(S+1)` to zero, so it cannot represent arbitrary carried old-top
rows.

## Reproduction

Fix the displayed Case 2 chart at pivot column `J+1`.  Let

```text
Rcols = {J+1,...,M^(S+1)}
e : Unit + pivotComplement(J+1 in Rcols) ~= Rcols
```

be the pivot-first equivalence, so `e(*) = J+1` and the right summand lists the
other residual columns.

Take two independent pieces of finite coordinate data:

```text
Cold   : {1,...,J} -> tau -> R,
Cprime : (Unit + pivotComplement(J+1)) -> tau -> R.
```

The old residual-column factor corresponding to the free chart coordinate is

```text
Csrc = Q * Cprime.
```

Construct a total source-coordinate following factor by assigning rows in
source order:

```text
C(j,a) =
  Cold(j,a)              if 1 <= j <= J,
  Csrc(e^-1(j),a)        if J+1 <= j <= M^(S+1),
  0                      otherwise.
```

The two displayed domains are disjoint: a source row cannot satisfy both
`j <= J` and `J+1 <= j`.  Therefore the old-top restriction reads the first
case and the residual-column restriction reads the second case.

For an old-top index `i in {1,...,J}`,

```text
oldTopBlock(C)(i,a) = C(i,a) = Cold(i,a).
```

For a pivot-first residual-column index `r`,

```text
displayedSourceFollowingFactor(C)(r,a)
  = C(e(r),a)
  = Csrc(e^-1(e(r)),a)
  = Csrc(r,a).
```

Specializing `Csrc = Q*Cprime`, the displayed inverse operation recovers the
free chart coordinate:

```text
paperCprime(C)
  = Q^-1 * displayedSourceFollowingFactor(C)
  = Q^-1 * (Q*Cprime)
  = Cprime.
```

Now reindex the current source-row block by the equivalence

```text
{1,...,J} + (Unit + pivotComplement(J+1)) ~= {1,...,n(S+1)}.
```

The old current block becomes

```text
currentFollowingBlock(C) = [ Cold ; Q*Cprime ].
```

The formula-level successor following factor changes only the pivot row
`J+1`, replacing it by the top row of `paperCprime(C)`, and leaves every other
row unchanged.  Under the constructed `C`, the reindexed successor block is

```text
successorFollowingBlock(C) = [ Cold ; Cprime ].
```

This last identity should be proved through the whole recovery theorem
`paperCprime(C)=Cprime`: for arbitrary residual data `Csrc` the successor
block is only `[Cold ; Q^-1*Csrc]`; it becomes `[Cold ; Cprime]` specifically
when `Csrc=Q*Cprime`.

## Formalisation Targets

Generic constructor:

```text
case2DisplayedConstructedSourceFollowingFactorWithOldTop
case2DisplayedSourceOldTopBlock_constructedWithOldTop
case2DisplayedSourceFollowingFactor_constructedWithOldTop
case2DisplayedPaperCprime_of_constructedSourceFollowingFactorWithOldTop
case2SourceCurrentFollowingBlock_constructedWithOldTop_submatrix_oldTopPaperCprimeRowEquiv
```

Specialized free-chart-coordinate constructor:

```text
case2DisplayedConstructedSourceFollowingFactorWithOldTopFromCprime
case2DisplayedPaperCprime_of_constructedSourceFollowingFactorWithOldTopFromCprime
case2SourceCurrentFollowingBlock_constructedWithOldTopFromCprime_submatrix_oldTopPaperCprimeRowEquiv
case2SourceSuccessorFollowingBlock_constructedWithOldTopFromCprime_submatrix_oldTopPaperCprimeRowEquiv
```

## Kill Conditions

- If old-top rows and residual columns overlap, the piecewise construction is
  ambiguous.
- If `case2DisplayedSourceFollowingFactor` reads outside `Rcols`, the
  residual-column recovery is false.
- If `case2DisplayedPaperCprime` depends on old-top rows, the free `Cprime`
  recovery is false.
- If the successor formula changes rows other than `J+1`, the source-current
  row package would need a stronger calculation.

## Nonclaims

This is finite source-coordinate bookkeeping.  It does not construct a
`SourceProductionObligation`, a successor chart family, a source suffix,
recurrence post-data, exponent post-data, chart coverage, transition
regularity, analytic coordinate regularity, Jacobian/volume arithmetic,
normal crossings, pole order, termination, RLCT extraction, stopped-branch
terminal production, or repair of the printed Case 2 vector mismatch.
