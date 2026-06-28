# Reproduction - A2 Case 2 displayed product nonzero source production

Date: 2026-06-28.

Status: reproduced, Lean-formalised, and xhigh-reviewed PASS.

## Target

This note isolates a finite constructed-data theorem for the continuing Case 2
branch.  It is not a theorem about an arbitrary retained-passive
`sourceReadback` point.

Given a successor selected-entry coordinate vector

```text
yNext : case2ResidualBlockPivotEntries n S (J+1) -> ℝ
```

with nonzero displayed successor pivot coordinate at `(J+2,J+2)`, construct
old displayed residual data and a free displayed following factor `Cprime` so
that

```text
case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime
```

is exactly the successor selected-entry chart matrix.  Consequently this
displayed two-edge product is nonzero.

Lean separates the coefficient domains: the product-side construction is
generic over a commutative ring `R`, while the selected-entry chart layer here
is specialised to `ℝ` because the existing Aoyagi coordinate APIs are
real-valued.

The branch hypotheses are:

```text
hS    : 1 <= S
hcont : J+1 <= prefixMinNat n (S+1)
hnext : J+2 <= prefixMinNat n (S+1)
```

The condition `hnext` supplies the successor center and its displayed pivot

```text
pivotNext = (J+2,J+2).
```

## Successor Selected-Entry Matrix

Fix an endpoint equivalence

```text
eNext : tau ~= Case2ResidualColIndex n S (J+1).
```

Define the target matrix

```text
T : Matrix (Case2ResidualRowIndex n S (J+1)) tau ℝ
```

by reading the successor selected-entry chart map through the residual
coordinate equivalence:

```text
T =
  AoyagiResidualBlockCoordinateIndex.matrix
    (fun c =>
      SelectedEntrySignedBox.CenterCoord.chartMap
        pivotNext yNext
        (case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
          n S (J+1) (Equiv.refl _) eNext c)).
```

At the coordinate corresponding to `pivotNext`, the selected-entry chart map is
the pivot coordinate itself:

```text
T (coordEquiv.symm pivotNext).1 (coordEquiv.symm pivotNext).2
  = yNext pivotNext.
```

Thus `yNext pivotNext != 0` implies `T != 0`.

## Constructing the Old Residual

Set

```text
D := T.submatrix id eNext.symm
```

as a matrix on the successor row and successor column domains.  Construct an
old source residual function `residualD : ℕ x ℕ -> ℝ` by zero extension from
the successor residual block:

```text
residualD (a,b) =
  D <a as Case2ResidualRowIndex n S (J+1)>
    <b as Case2ResidualColIndex n S (J+1)>
```

when both subtype memberships exist, and `0` otherwise.

Now inspect the old displayed normalized block

```text
A = case2DisplayedPaperDchart n hS hcont residualD.
```

By definition, `A` is `case2DisplayedSourceNormalizedBlock`, so its entries
are the selected-entry normalized map for the old pivot `(J+1,J+1)`: the old
pivot entry is `1`, and every non-pivot entry is the corresponding value of
`residualD`.

For a lower-right complement row `i` and column `j`, the row and column are
identified with successor row and successor column indices by

```text
case2DisplayedPivotRowComplementEquivResidualRowSucc n hS hcont
case2DisplayedPivotColComplementEquivResidualColSucc n hS hcont.
```

Hence

```text
A i.1 j.1 = D i' j'
```

after this reindexing.  On the old pivot column and old pivot row,
zero-extension gives

```text
A i.1 (J+1) = 0,
A (J+1) j.1 = 0,
```

because `(J+1)` is not a successor row or successor column index.

The displayed post-pivot residual block is the lower-right Schur complement

```text
pivotFirstD A - pivotFirstX A * pivotFirstY A
```

reindexed to the successor domains.  Entrywise,

```text
(pivotFirstD A - pivotFirstX A * pivotFirstY A) i j
  = A i.1 j.1 - A i.1 (J+1) * A (J+1) j.1
  = D i' j' - 0 * 0
  = D i' j'.
```

This is exactly the Lean lemma `pivotFirstSchurComplement_apply` plus the
zero-extension facts.  Therefore

```text
case2DisplayedPostPivotResidualBlock n hS hcont residualD = D.
```

## Constructing the Free Following Factor

Let

```text
F := (1 : Matrix
        (Case2ResidualColIndex n S (J+1))
        (Case2ResidualColIndex n S (J+1)) ℝ).submatrix id eNext.
```

This is the identity following factor with its right endpoint reindexed from
successor columns to `tau`.

Choose a free pivot-first matrix

```text
Cprime : Matrix
  (Unit + pivotComplement (case2DisplayedPivotCol n hS hcont)) tau ℝ
```

with arbitrary top row, say zero, and lower tail determined by

```text
Cprime (inr oldComplementCol) t =
  F (case2DisplayedPivotColComplementEquivResidualColSucc n hS hcont
      oldComplementCol) t.
```

Then, by the definition of `case2DisplayedPostPivotFreeFollowingFactor`,

```text
case2DisplayedPostPivotFreeFollowingFactor n hS hcont Cprime = F.
```

The displayed product is therefore

```text
D * F.
```

Since `F` is the identity matrix with the target endpoint reindexed by
`eNext`, finite matrix algebra gives

```text
D * F = D.submatrix id eNext.
```

Using `D = T.submatrix id eNext.symm`, the right-hand side is `T`.

Therefore

```text
case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residualD Cprime = T.
```

Together with `T != 0`, this constructs the desired nonzero displayed
post-pivot product.

## Source-Following Variant

The free `Cprime` can also be produced by an old source-coordinate following
factor, using the existing reverse construction

```text
case2DisplayedConstructedSourceFollowingFactorWithOldTopFromCprime
```

and recovery theorem

```text
case2DisplayedPaperCprime_of_constructedSourceFollowingFactorWithOldTopFromCprime.
```

This source-following variant still constructs data.  It does not say that a
previously given retained-passive source/readback point has these factors.

## Proved / Assumed / Cited / Deferred

**Proved by this reproduction.** Finite constructed-data source production:
from a nonzero successor selected-entry pivot coordinate, one can construct an
old residual and a displayed free following factor whose Case 2 post-pivot
two-edge product is the successor selected-entry matrix and is nonzero.

**Assumed.** The successor selected-entry coordinate vector `yNext`, endpoint
equivalence `eNext`, and nonzero successor pivot coordinate.

**Cited.** Aoyagi pp. 19-22 only for the displayed Case 2 selected-entry
chart algebra and the displayed post-pivot Schur-complement product shape.

**Deferred.** Factor alignment for an arbitrary retained-passive
`sourceReadback` point; nonzeroness of the displayed product for such a point;
retained-passive-to-selected-entry measure transport; original source-prior
transport; normal crossings; pole order; RLCT extraction.

## Lean Shape

The first Lean target should live near the finite displayed product API, likely
in `Case2ResidualFactorProduct.lean` or a small imported helper module.  It
should expose:

```text
case2SuccessorSelectedEntryMatrix
exists_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_successorSelectedEntryMatrix_of_yNext_pivot_ne_zero
```

The theorem should name its constructed witnesses and state the nonclaim
boundary in its docstring.  A later source-following corollary can use the
existing `case2DisplayedPaperCprime_of_constructedSourceFollowingFactor...`
API once the free version is stable.

The product-side theorem is deliberately more general:

```text
exists_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_matrix_of_colEquiv
```

works over `[CommRing R]`.  The successor selected-entry production theorem is
the `ℝ`-specialisation that plugs in the real-valued selected-entry chart map.
