# Pen-and-paper reproduction - A4 Case 2 next-state source-product reindex

Status: reproduced, formalised, and xhigh-reviewed.

Review: `review-case2-next-state-source-product-reindex-a4.md`.

## Source Anchor

Aoyagi PDF pp. 19-22, Case 2.  After selecting the displayed pivot
`(J+1,J+1)`, the paper forms `C' = Q^{-1} C` and

```text
D''' = [1 0; 0 D - x*y].
```

The displayed product has the form

```text
diag(b'_{J+1},...,b'_{M(S)}) D''' C'.
```

When continuing at the same stage, this is read as the next `(S,J+1)` source
product.  This note records only the finite reindexing behind that reading.

## Row And Column Partitions

Before the pivot, the pivot-first display uses:

```text
old top rows:        1..J
pivot row/column:    J+1
residual rows:       J+2..M(S)
residual columns:    J+2..M^(S+1)
```

After reindexing to the next same-stage source product:

```text
new old top rows:    1..J+1
next residual rows:  J+2..M(S)
next residual cols:  J+2..M^(S+1)
```

The old top plus pivot row is therefore the source interval `1..J+1`, and the
old row/column complements are the residual row/column types for `(S,J+1)`.
This is the content of the new finite equivalences.

The column equivalence is a following-factor row equivalence: its right-hand
residual type is the next residual column type because those columns of
`D'''` are rows of the following factor.

## Product Calculation

Let

```text
Csucc(j,a) =
  if j = J+1 then top row of Q^{-1}C at a
  else C(j,a).
```

Then the right factor reindexes as

```text
[ oldTop(C); C' ]
  =
[ oldTop_{1..J+1}(Csucc);
  residualFollowing_{S,J+1}(Csucc) ].
```

For the left factor, `D''' = [1 0; 0 Dpost]` and the diagonal weights split
as the pivot weight `post.weight(J+1)` and lower residual-row weights.  The
top old weights `pre.weight(i)` for `i <= J` agree with the concrete
`case2Succ` post-state weights, while the pivot weight is the new final entry
of the source top block.  Thus

```text
[ diag(pre.weight 1..J)    0
  0                         diag(post lower weights) * D''' ]
```

reindexes to

```text
[ diag(post.weight 1..J+1)  0
  0                         diag(post residual weights) * Dpost ].
```

The zero-extended source residual representative restricts back to `Dpost` on
the next residual block.  Multiplying the two reindexed factors gives the
next-state source product shape.

## Lean Names

```text
case2SourceOldTopSuccResidualRowEquiv
case2SourceOldTopSuccResidualColEquiv
case2DisplayedSuccessorFollowingFactor_reindex_nextSource
case2DisplayedWeightedDppp_reindex_nextSource
case2DisplayedPivotFirstRHS_reindex_nextSourceProduct
case2DisplayedPivotFirstRHS_reindex_nextSourceProduct_mul
```

## Boundary Checks

- No `hnext` is needed: the row/column/product equalities are valid even if
  one residual side is empty.
- The theorem does not assert that `Csucc` is chart-produced; it is the
  formula-level successor following factor.
- The theorem does not construct a successor chart family, source suffix,
  transition invariant, Jacobian exponent, normal-crossing certificate, pole
  order, termination argument, or RLCT extraction.
- It stays at the continuing `(S,J+1)` state and does not relabel to
  `(S+1,0)`.

## Kill Conditions

- Do not use this as source production of full `C'^(S+1)`.
- Do not infer chart coverage or transition regularity from the finite
  reindexing.
- Do not conflate the row complement `J+2..M(S)` with the column complement
  `J+2..M^(S+1)`.
- Do not replace the formula-level transported pivot row by the original row
  without the actual-width column-exhausted hypothesis.
