# Pen-and-paper reproduction - A4 Case 2 paper-Cprime source-following weighted handoff

Status: reproduced; xhigh review pending.

## Source Anchor

Aoyagi PDF pp. 19-22, Case 2.  The displayed local calculation introduces
the column operation `Q`, the transported following factor `C' = Q^-1 C`, the
row operation `P`, and the cleared block `D'''`, then uses the displayed
weighted `Q/P` identity.  The source display also carries the common selected
chart factor `u_{S,J+1}`; the following formula is the isolated finite
row-operation identity after that common factor is accounted for in the
weight data:

```text
P diag(b') D'' C' = diag(b') D''' C'.
```

This checkpoint keeps the paper transported factor `C' = Q^-1 C`.  It is not
the full source-produced next matrix `C'^(S+1)`.

## Reproduction

Let

```text
Cpaper := Q^-1 Csrc
```

be Aoyagi's displayed pivot-first transported following factor, where `Csrc`
is the old source following factor restricted to the displayed residual
columns.  The already formalised source-chart `Q/P` package gives a witness
`q` and a full pivot-first equality

```text
Source(q,Csrc) = W_successor * D''' * Cpaper.
```

Here

```text
Source(q,Csrc)
  =
(P_q * (diag(pre weights) * D_source_chart)^pivot-first) * Csrc,
```

and `P_q` is the concrete weighted row operation
`weightedPivotBlockRowOp q`.

Project both sides to the lower rows, reindexed by deleting the displayed
pivot row:

```text
Source(q,Csrc)_lower,reindexed
  =
(W_successor * D''' * Cpaper)_lower,reindexed.
```

The weighted lower-row projection theorem rewrites the right side as

```text
diagonal(successor lower-row weights)
  *
(D_postpivot * freeTail(Cpaper)).
```

It remains to identify `freeTail(Cpaper)`.  Since

```text
Q^-1 = [1  y]
       [0  I],
```

only the pivot row of the following factor changes.  Thus the lower tail of
`Cpaper = Q^-1 Csrc` is the old lower tail of `Csrc`.  After reindexing the
pivot-column complement to the next same-stage column domain, this is exactly

```text
case2SourceFollowingFactor (S,J+1) C.
```

Combining the three finite equalities gives

```text
Source(q,Csrc)_lower,reindexed
  =
diagonal(successor lower-row weights)
  *
(case2DisplayedPostPivotResidualBlock
  * case2SourceFollowingFactor(S,J+1,C)).
```

The corrected exponent, level, least-value-gap, and recurrence `case2Gap`
fields are carried from the existing supplied/concrete post-data package.
They are not derived from the affine chart in this theorem.

## Boundary Checks

- The source-side product includes the row operation `P_q`.
- The theorem projects only lower rows; the pivot row is not included.
- The successor lower-row diagonal stays explicit.
- `Cpaper` is Aoyagi's displayed transported factor `Q^-1 C`, not a proof of
  the full successor matrix `C'^(S+1)`.
- The right side uses the next same-stage source following factor only after
  the lower-tail identity for `Q^-1 C`.
- No next residual-center nonemptiness is asserted.

## Formalisation Target

Lean should add the concrete theorem

```text
Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_paperCprimeWeightedLowerRows_withCorrectedPostData
```

in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

Expected proof ingredients:

1. use the concrete displayed source-chart boundary constructor;
2. obtain the source-chart paper `Q/P` equality
   `sourceDisplayedQP_sourceChartMap_paperQP`;
3. project it with `Matrix.submatrix`;
4. rewrite the weighted right side using
   `postPivotWeightedFreeCprimeNextSameStageProduct` specialized to
   `case2DisplayedPaperCprime`;
5. rewrite
   `case2DisplayedPostPivotFreeFollowingFactor ... (case2DisplayedPaperCprime ...)`
   to `case2SourceFollowingFactor (J := J+1)` via the lower-tail identity.

## Kill Conditions

- Do not call this a full successor product or transition step.
- Do not include the pivot row.
- Do not drop the successor lower-row diagonal.
- Do not claim source production of `C'^(S+1)`, chart coverage,
  arbitrary-pivot coverage, successor chart-family construction,
  chart-produced recurrence/exponent post-data, transition invariance,
  Jacobian arithmetic, normal crossings, pole order, or RLCT extraction.
- Do not use the Lehalleur-Rimanyi/quiver paper or quiver Lean as evidence.
