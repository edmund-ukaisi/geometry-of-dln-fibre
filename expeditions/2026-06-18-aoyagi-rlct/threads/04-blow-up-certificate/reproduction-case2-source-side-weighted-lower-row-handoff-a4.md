# Pen-and-paper reproduction - A4 Case 2 source-side weighted lower-row handoff

Status: reproduced as a finite projection of the displayed source-side `Q/P`
identity.

## Source Anchor

Aoyagi PDF pp. 19-22, Case 2.  The displayed computation after introducing
`Q`, `C'=Q^-1 C`, `P`, and `D'''` gives

```text
P diag(b') D'' C' = diag(b') D''' C'.
```

The previous local-product package formalises this equality with a free
pivot-first `Cprime`, by reconstructing the old following factor as
`Q*Cprime` and zero-extending it back to source residual columns.  The previous
weighted lower-row package formalises the lower-row projection of the right
side.

## Reproduction

Let

```text
Source(q,Cprime)
```

denote the old source-side weighted product

```text
(P_q * (diag(pre weights) * D_source_chart)^pivot-first) * C_old,
```

where `C_old` is the source residual following factor reconstructed from
`Q*Cprime`.  The local `Q/P` package gives a witness `q` and the equality

```text
Source(q,Cprime) = W_successor * D''' * Cprime.
```

Project both sides to the lower rows and reindex those rows to the next
same-stage domain `(S,J+1)`.  Equality is preserved by this projection:

```text
Source(q,Cprime)_lower,reindexed
  =
(W_successor * D''' * Cprime)_lower,reindexed.
```

The weighted lower-row projection already gives

```text
(W_successor * D''' * Cprime)_lower,reindexed
  =
diagonal(successor lower-row weights)
    * (D_postpivot * Cprime_tail,reindexed).
```

Combining the two equalities yields the desired handoff:

```text
Source(q,Cprime)_lower,reindexed
  =
diagonal(successor lower-row weights)
    *
  (case2DisplayedPostPivotResidualBlock
    * case2DisplayedPostPivotFreeFollowingFactor).
```

This is a projection of Aoyagi's displayed local product identity, not a
chart-production theorem.  It still only describes the lower rows after the
displayed pivot row has been removed.

## Boundary Checks

- The theorem depends on the supplied/concrete displayed boundary data that
  already provides the `Q/P` equality and corrected post-data package.
- The lower-row diagonal weights remain explicit.
- The pivot row is not included.
- The free `Cprime` remains a compatible pivot-first chart-coordinate matrix,
  not a source-produced successor matrix.
- No next residual-center nonemptiness is asserted.

## Formalisation Target

Lean should add one concrete source-chart theorem, likely named

```text
sourceChartMap_constructedSourceFreeCprime_weightedLowerRows_withCorrectedPostData
```

returning `∃ q`, the lower-row source-side handoff equality, and the existing
corrected exponent, level, least-value-gap, and `case2Gap` fields.

The proof should:

1. use
   `sourceChartMap_constructedSourceFreeCprimeLocalProduct_withCorrectedPostData`
   to obtain the full weighted `Q/P` equality and corrected post-data;
2. project the full equality with `Matrix.submatrix`;
3. rewrite the weighted right side with
   `Case2DisplayedSuppliedChartFamilyBoundary.postPivotWeightedFreeCprimeNextSameStageProduct`.

## Kill Conditions

- Do not call this a full successor product or induction step.
- Do not include the pivot row.
- Do not drop the successor lower-row diagonal.
- Do not claim source production of `Cprime`, chart coverage,
  arbitrary-pivot coverage, transition invariance, Jacobian arithmetic,
  normal crossings, pole order, or RLCT.
- Do not use the Lehalleur-Rimanyi/quiver paper or quiver Lean as evidence.
