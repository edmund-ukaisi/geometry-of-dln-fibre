# Reproduction - A4 Case 2 Continuing Weighted Source-Following Payload

Status: reproduced; Lean checked; xhigh review passed.

## Source Anchor

Aoyagi PDF pp. 19-22, Case 2.  After the displayed top-left pivot chart, the
paper applies the regular column operation `Q`, the row operation `P`, and the
transported following factor `C' = Q^-1 C`.  In the continuing branch

```text
J+1 <= M(S+1) = min{M(S),M^(S+1)}
```

the proof says that the inductive statement is obtained with `J` increased by
one.  In the local displayed calculation, the algebraic content available to
Lean is the lower-row weighted handoff

```text
P diag(b') D'' C' = diag(b') D''' C'
```

after projecting away the pivot row and reindexing the lower-right block to
the next same-stage state `(S,J+1)`.

## Calculation

The previous paper-`C'` handoff checkpoint proves the source-side lower-row
identity.  With

```text
upivot := case2DisplayedSourceChartMap(...)(J+1,J+1)
post := pre.case2Succ upivot
```

there is a row-operation witness `q` such that

```text
lowerRows(
  weightedPivotBlockRowOp q
    * (diag(pre row weights) * sourceSubstitutionBlock)^pivot-first
    * sourceFollowingFactor(C))
=
diag(successor lower-row weights)
  * (postPivotResidualBlock * sourceFollowingFactor at (S,J+1)).
```

This statement is lower-row only.  The pivot row is not part of the equality,
and the successor lower-row diagonal remains visible on the right.

The continuing branch also has the finite next-center guard

```text
J+2 <= prefixMinNat n (S+1).
```

This is exactly the nonemptiness condition for the next residual-block pivot
entry set:

```text
case2ResidualBlockPivotEntries n S (J+1) is nonempty.
```

Independently, the displayed source-coordinate chart map gives the same finite
principalization facts used in the stopped packages:

```text
u is one transformed center value,
every transformed center value is divisible by u,
the transformed center ideal is Ideal.span {u}.
```

The new payload is the conjunction of these four ingredients:

```text
next residual center nonempty,
paper-C' weighted lower-row source-following handoff with corrected post-data,
u in the transformed center,
center divisibility and Ideal.span {u}.
```

## Lean Target

The new Lean theorem is

```text
Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_continuingWeightedSourceFollowingPayload_withFiniteCenterIdeal
```

and the frontier package exports it through

```text
ContinuingWeightedSourceFollowingFrontierPayload
SourceChartFrontierBoundaryPackages.continuingWeighted
```

## Nonclaims

- No full successor product including the pivot row.
- No chart construction, chart coverage, or arbitrary-pivot coverage.
- No source production of `C'^(S+1)`.
- No chart-produced recurrence or exponent post-data; the corrected post-data
  fields remain supplied/concrete boundary data.
- No successor chart-family construction.
- No transition invariant, termination theorem, terminal relabeling, Jacobian
  arithmetic, normal crossings, pole order, or RLCT extraction.
- No repair of Aoyagi's printed Case 2 vector mismatch.
