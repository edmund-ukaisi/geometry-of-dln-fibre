# A4 Pivot-First Following-Factor Transport

Status: checked finite matrix reindexing reproduction.

## Scope

The displayed `Q/P` calculation replaces the following factor by `Q^{-1} C`.
All pivot-first `Q/P` theorems already assume that this following factor is
expressed in pivot-first column coordinates. This note isolates the elementary
matrix reindexing that transports a pre-reindexed following factor into those
coordinates.

This is finite matrix algebra only. It does not construct source coordinates,
prove a blow-up chart, prove chart coverage, or update exponent data.

## Reproduction

Let

```text
A : Matrix I K R,
C : Matrix K T R.
```

Choose a pivot row `i0 : I` and pivot column `j0 : K`. The pivot-first residual
matrix is

```text
A_pivot = A.submatrix (pivotFirstIndexEquiv i0) (pivotFirstIndexEquiv j0).
```

The following factor in the same pivot-first column coordinates is

```text
C_pivot = C.submatrix (pivotFirstIndexEquiv j0) id.
```

Then multiplication commutes with this reindexing:

```text
A_pivot * C_pivot
  =
(A * C).submatrix (pivotFirstIndexEquiv i0) id.
```

This is the precise finite algebra behind using the following factor `C` in
the pivot-first `Q/P` identity: the theorem's `C` should be the reindexed
following factor `C_pivot`.

## Lean Shape

Lean names the reindexed following factor:

```text
pivotFirstFollowingFactor colPivot C
```

and proves

```text
pivotFirstMatrix rowPivot colPivot A * pivotFirstFollowingFactor colPivot C
  =
(A * C).submatrix (pivotFirstIndexEquiv rowPivot) id.
```

The proof is the Mathlib `submatrix_mul_equiv` theorem applied to the pivot
column equivalence.

## Kill Conditions

- This theorem only transports multiplication under reindexing. It does not
  prove that Aoyagi's source variables have already been arranged into the
  residual block `A` and following factor `C`.
- It does not prove the `Q` operation is regular, has unit Jacobian, or gives
  a full coordinate chart.
- It does not prove arbitrary pivot coverage or a transition invariant.
