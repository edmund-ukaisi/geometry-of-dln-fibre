# A4 Case 2 Source-Block Tail Lift

Status: checked finite block-matrix reproduction for reattaching a displayed
Case 2 residual-tail identity to unchanged top rows.

## Scope

Aoyagi's displayed Case 2 calculation on PDF pp. 20-21 acts on the residual
block

```text
I = {i | J+1 <= i <= mu_S},
K = {j | J+1 <= j <= n_(S+1)}
```

with selected pivot `(J+1,J+1)`. The previous Lean checkpoints proved the
tail `Q/P` identity in pivot-first coordinates. This note records only the
finite block-matrix step that puts that already-proved residual-tail identity
under unchanged top rows.

It does not construct the full source chart, prove arbitrary-pivot coverage,
prove a Jacobian or regular coordinate-change statement, update exponents, or
prove a transition invariant.

## Reproduction

Let `T` be the index type for the following columns after the current source
block. Split a full following factor into top and residual-tail row blocks:

```text
C_full = verticalBlock C_top C_tail,

C_top  : Matrix Top T R,
C_tail : Matrix Tail T R.
```

The top block is not changed by the displayed residual `Q/P` operations. If
the top-left action is some fixed matrix

```text
A_top : Matrix Top Top R,
```

and the residual tail identity has the form

```text
L_tail * C_tail = R_tail * C_tail',
```

then block-diagonal multiplication gives

```text
fromBlocks A_top 0 0 L_tail * verticalBlock C_top C_tail
  = verticalBlock (A_top * C_top) (L_tail * C_tail)
  = verticalBlock (A_top * C_top) (R_tail * C_tail')
  = fromBlocks A_top 0 0 R_tail * verticalBlock C_top C_tail'.
```

Entrywise, on a top row `a` only the upper-left block contributes, so the
entry is `(A_top*C_top)_(a,t)` on both sides. On a residual row `i` only the
lower-right block contributes, so the entry is exactly the residual-tail
identity at `(i,t)`.

## Displayed Case 2 Instances

For the source-substituted displayed pivot theorem, `C_tail` is

```text
case2DisplayedFollowingFactor n hS hcont C
```

and `C_tail'` is

```text
case2DisplayedTransportedFollowingFactor n hS hcont residual C.
```

The residual identity is supplied by

```text
exists_case2DisplayedQP_mul_sourceSubstitution_of_flat_weights.
```

For the row-index monomial recurrence theorem, the same `C_tail` and
`C_tail'` are used, while the residual identity is supplied by

```text
exists_case2DisplayedQP_mul_transportedFollowingFactor_of_rowIndex_monomialRec.
```

In both cases, the following-factor replacement is only the displayed
pivot-coordinate update `Q^-1 * C_tail`.

## Normalisation and Boundary Checks

- The selected variable is counted once, through the displayed row weights
  `u * oldWeight` or `u * monomialRec step rowLevel`.
- The row range remains `J+1..mu_S`, while the column range remains the actual
  source width `J+1..n_(S+1)`.
- The displayed pivot validity hypothesis is still explicit:
  `J+1 <= prefixMinNat n (S+1)`.
- Rectangular residual blocks are allowed by the matrix types.
- Continuation versus advance after the displayed pivot is not settled here.

## Lean Shape

Generic finite block algebra:

```text
verticalBlock
fromBlocks_mul_verticalBlock
fromBlocks_mul_verticalBlock_eq_of_tail
```

Displayed Case 2 lifted wrappers:

```text
exists_case2DisplayedQP_verticalBlock_sourceSubstitution_of_flat_weights
exists_case2DisplayedQP_verticalBlock_transportedFollowingFactor_of_rowIndex_monomialRec
```

## Kill Conditions

- If the top rows are changed by a source coordinate operation not represented
  by the same `A_top` on both sides, this theorem is not the intended full
  source identity.
- If the residual-tail identity is not already established in the displayed
  pivot coordinates, this lift proves nothing about the source chart.
- If the selected variable is counted both in row weights and as an additional
  outside factor, the normalization is wrong.
- This theorem does not prove Aoyagi's recursive row weights, arbitrary
  selected pivots, chart coverage, exponent updates, transition invariants,
  normal crossings, or RLCT extraction.
