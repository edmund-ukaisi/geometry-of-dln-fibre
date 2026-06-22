# Pen-and-paper reproduction - A4 Case 2 continuing weighted following product

Status: reproduced, reviewed, and formalised.

## Source Anchor

Aoyagi PDF pp. 19-22, Case 2.  The displayed pivot chart introduces the
source chart variable `u_(S,J+1)`, the column operation `Q`, the transported
following factor `C' = Q^-1 C`, the row operation `P`, and the cleared block
`D'''`.  The already formalised lower-row handoff isolates the finite
source-chart identity after the common chart factor has been absorbed into
the recurrence weights.

This checkpoint only right-multiplies that continuing lower-row identity by a
supplied following product `F`.

## Reproduction

The existing paper-`C'` lower-row handoff gives a row-operation witness `q`
such that

```text
LowerRows(P_q * diag(pre) * D_chart_source * C)
  =
diag(post lower weights)
  *
(D_postpivot * case2SourceFollowingFactor(S,J+1,C)).
```

Here `LowerRows` deletes the displayed pivot row and reindexes the remaining
rows to the next same-stage residual row domain.  The right side keeps the
successor lower-row diagonal explicit.  The product

```text
D_postpivot * case2SourceFollowingFactor(S,J+1,C)
```

is the continuing lower-row block product; it is not the full successor
matrix `C'^(S+1)`.

Let

```text
F : Matrix tau upsilon R
```

be any supplied following product.  Matrix multiplication is compatible with
equality, so right-multiplying both sides gives

```text
LowerRows(P_q * diag(pre) * D_chart_source * C) * F
  =
(diag(post lower weights)
  *
  (D_postpivot * case2SourceFollowingFactor(S,J+1,C))) * F.
```

The same theorem also carries the existing corrected post-data projections:
the exponent certificates over `(S,J+1)`, the level invariant, the Case 2
least-value gap, and the successor recurrence state's `case2Gap`.

## Boundary Checks

- `F` is supplied.  No source production of the suffix/following product is
  asserted.
- The pivot row is still absent; this is a lower-row continuing statement.
- The successor lower-row diagonal remains explicit.
- The theorem does not require `J+2 <= prefixMinNat n (S+1)`.  That branch
  hypothesis is only needed when one also wants next-center nonemptiness.
- No terminal relabeling, actual-width exhaustion, row-exhaustion, or
  `SuppliedTerminalCprimeBridge` is used.

## Formalisation Target

Lean should add:

```text
Case2DisplayedSuppliedChartFamilyBoundary.
  sourceChartMap_paperCprimeWeightedLowerRows_mul_followingProduct_withCorrectedPostData
```

in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

Expected proof:

1. invoke
   `sourceChartMap_paperCprimeWeightedLowerRows_withCorrectedPostData`;
2. keep its witness `q` and corrected post-data projections;
3. apply congruence by right multiplication with `F`.

## Kill Conditions

- Do not call this source production of the suffix or of the full successor
  `C'^(S+1)`.
- Do not add the pivot row.
- Do not drop the successor lower-row diagonal.
- Do not infer chart coverage, successor chart-family construction,
  chart-produced recurrence/exponent data, transition invariance, Jacobian
  arithmetic, normal crossings, pole order, or RLCT.
- Do not use the Lehalleur-Rimanyi/quiver paper or quiver Lean as evidence.
