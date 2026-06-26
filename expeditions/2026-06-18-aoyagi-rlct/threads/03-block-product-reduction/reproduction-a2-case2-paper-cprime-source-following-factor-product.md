# Reproduction - A2 Case 2 paper-Cprime source-following factor product

Date: 2026-06-26.

Status: Lean target implemented.

## Source Boundary

Aoyagi pp. 19-22 support the formula-level Case 2 transformation

```text
C' = Q^-1 C
```

and the lower-row product identity for `D''' * C'`.  Earlier A4 notes already
reproduced the two elementary components:

- the lower rows of `D''' * C'` are the post-pivot residual block times the
  reindexed tail of `C'`;
- the lower tail of Aoyagi's paper `C' = Q^-1 C` is the source following
  factor on the next same-stage residual columns.

This A2 note records only the product-reduction API consequence after the
concrete two-edge residual-factor family has been introduced.

## Calculation

For the concrete displayed two-edge chain

```text
tau -> Case2ResidualColIndex n S (J+1) -> Case2ResidualRowIndex n S (J+1),
```

the residual-factor product is

```text
case2DisplayedPostPivotResidualBlock n hS hcont residual
  * case2DisplayedPostPivotFreeFollowingFactor n hS hcont Cprime.
```

Specialize to Aoyagi's paper following factor

```text
Cprime = case2DisplayedPaperCprime n hS hcont residual C.
```

The finite tail identity gives

```text
case2DisplayedPostPivotFreeFollowingFactor n hS hcont Cprime
  = case2SourceFollowingFactor (n := n) (S := S) (J := J+1) C.
```

The formula-level successor following factor has the same next same-stage
restriction:

```text
case2SourceFollowingFactor (J := J+1)
  (case2DisplayedSourceSuccessorFollowingFactor n hS hcont residual C)
 =
case2SourceFollowingFactor (J := J+1) C.
```

The zero-extended source residual representative restricts back to the
post-pivot residual block:

```text
case2SourceResidualBlock (J := J+1)
  (case2DisplayedPostPivotSourceResidual n hS hcont residual)
 =
case2DisplayedPostPivotResidualBlock n hS hcont residual.
```

Combining these gives the desired source-residual/source-following form of the
concrete residual-factor product.

## Lean Target

Implemented in `lean/DLNFibre/DLN/Aoyagi/Case2ResidualFactorProduct.lean`:

```text
residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_paperCprime_eq_sourceResidualBlock_successorFollowingFactor
```

## Nonclaims

- No successor `yNext` or selected-entry readout is constructed.
- No source production of `Csucc`, terminal source rows, suffixes, or full
  successor chart data is proved.
- No source/image equality, chart coverage, transition regularity, normal
  crossings, pole order, or RLCT theorem is proved.
