# A4 Case 2 Pivot-First Following-Factor Package

Status: checked finite algebra reproduction for the source-displayed Case 2
top-left pivot.

## Scope

The previous displayed Case 2 `Q/P` theorem assumed the following factor was
already supplied in pivot-first column coordinates. This note packages that
transport for the source-displayed top-left Case 2 pivot `d_(J+1,J+1)`.

This remains local finite matrix algebra. It does not construct source
coordinates, prove regularity of the blow-up chart, prove chart coverage,
update exponent vectors, or prove a transition invariant.

## Reproduction

Let the displayed Case 2 residual block after selected-entry normalisation be

```text
A : Matrix I K R,
```

where

```text
I = {i | J+1 <= i <= mu_S},
K = {j | J+1 <= j <= n_(S+1)}.
```

Let the residual following factor before pivot-first reindexing be

```text
C0 : Matrix K T R.
```

The displayed pivot is the row/column `J+1`. Put the displayed pivot first
using `pivotFirstIndexEquiv`. The following factor in the coordinates required
by the pivot-first `Q/P` theorem is

```text
C = C0.submatrix (pivotFirstIndexEquiv displayedCol) id.
```

Thus the existing product-preservation theorem should be read with this
reindexed following factor. The replacement of the following factor by
`Q^{-1} C` is therefore:

```text
Q^{-1} * C0_pivot_first.
```

The finite reindexing theorem also records that

```text
A_pivot_first * C0_pivot_first
  =
(A * C0).submatrix (pivotFirstIndexEquiv displayedRow) id.
```

This is the elementary matrix transport behind Aoyagi's displayed following
factor update inside the displayed residual-block coordinates. It is not a theorem that the full source product has already
been placed into these residual-block coordinates.

## Lean Shape

Lean introduces aliases:

```text
case2DisplayedNormalizedMatrix
case2DisplayedFollowingFactor
```

and proves:

```text
case2DisplayedNormalizedMatrix_mul_followingFactor
exists_case2DisplayedQP_mul_pivotFirstFollowingFactor_of_flat_weights
```

The second theorem is the previous displayed Case 2 `Q/P` identity with
`C := case2DisplayedFollowingFactor ... C0`.

## Kill Conditions

- If the source residual block has not been identified with the normalised
  matrix `A`, this theorem does not apply to the source coordinates.
- If the displayed pivot row/column `J+1` is not valid, the pivot-first
  coordinate split is invalid.
- If row weights are not flat in the displayed residual-row coordinates, the
  trivial quotient witnesses used by the theorem are unavailable.
- This theorem does not cover arbitrary selected residual-block pivots.
- This theorem does not update exponent vectors or prove the corrected Case 2
  transition invariant.
