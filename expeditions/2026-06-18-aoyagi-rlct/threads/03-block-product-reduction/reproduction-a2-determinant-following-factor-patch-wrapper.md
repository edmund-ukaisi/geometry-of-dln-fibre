# A2 determinant following-factor patch wrapper

Date: 2026-07-02.

## Pen-and-paper reproduction

In Case 2 the independent following factor has type

```text
F : Matrix (Case2ResidualColIndex n S (J+1)) τ R.
```

The equivalence

```text
eNext : τ ≃ Case2ResidualColIndex n S (J+1)
```

turns it into the square matrix

```text
A(F) = F.submatrix id eNext.symm.
```

If `det A(F)` is a unit, then the nonsingular matrix inverse satisfies

```text
A(F) * A(F)^(-1) = I.
```

Define the candidate right inverse of the original following factor by
reindexing the columns of `A(F)^(-1)` back along `eNext`:

```text
G(F) = A(F)^(-1).submatrix eNext id.
```

Then `G(F)` has type

```text
Matrix τ (Case2ResidualColIndex n S (J+1)) R.
```

The product reindexing identity says

```text
(F * G(F)).submatrix id id
  = F.submatrix id eNext.symm * G(F).submatrix eNext.symm id.
```

The second factor on the right is definitionally `A(F)^(-1)`, so the right
side is `I`.  Since submatrixing by `id,id` is identity, this gives

```text
F * G(F) = I.
```

Therefore a patch on which every `A(F)` has unit determinant and the reindexed
inverse has uniformly bounded coordinate square-sum supplies the exact
right-inverse socket needed by the finite following-factor patch theorem.

## Lean target

The generic matrix theorem is:

```text
exists_rightInverse_squareSum_le_of_reindexed_det_isUnit_inverse_squareSum_le
```

It consumes:

```text
IsUnit ((F.submatrix id e.symm).det)
square_sum (((F.submatrix id e.symm)^(-1)).submatrix e id) <= K
```

and produces:

```text
exists G, F * G = I and square_sum G <= K.
```

The Case 2 endpoint theorem is:

```text
case2PassiveThetaWithFollowingFactor_productResidual_pos_ae_and_lintegral_rpow_neg_prod_restrict_followingPatch_of_forall_mem_reindexed_det_isUnit_inverse_squareSum_le
```

It composes the generic matrix theorem with the finite following-factor patch
wrapper, giving p.13 product-residual a.e. positivity and finite
negative-power integrability over

```text
(passiveMeasure.prod weightedBox).prod
  (followingMeasure.restrict followingPatch).
```

## Boundary

This is not yet the open-neighborhood theorem.  It assumes the measurable
finite patch, the determinant-unit condition on the reindexed square following
factor throughout the patch, and the uniform inverse square-sum bound
throughout the patch.  It does not construct an open patch around a base
right-invertible factor, prove finite `matrixEntryReferenceMeasure` mass for a
metric ball or box, perform source-prior/original-prior transport, prove
normal crossings, compute pole order, or extract RLCT.
