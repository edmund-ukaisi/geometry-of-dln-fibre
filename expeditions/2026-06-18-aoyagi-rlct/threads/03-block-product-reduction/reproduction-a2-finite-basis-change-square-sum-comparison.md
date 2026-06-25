# Reproduction - A2 finite basis-change square-sum comparison

Date: 2026-06-25.

Status: pen-and-paper reproduction, Lean implementation, and xhigh review.

## Source Anchor

This is finite linear algebra needed after the fixed adapted endpoint
Frobenius identity.  It is not a new source theorem from Aoyagi: it is the
ordinary comparison between coordinate square-sums in two fixed finite bases.

## Derivation

Let `M` be a finite real matrix and let fixed matrices `L` and `R` encode a
change of target and source coordinates.  The existing finite matrix estimate
gives

```text
squareSum(L * M * R)
  <= squareSum(L) * squareSum(R) * squareSum(M).
```

If `T = L * M * R`, set

```text
K = max(1, squareSum(L) * squareSum(R)),
c = K^{-1}.
```

Then `K > 0`, `c > 0`, and `c*K = 1`, so

```text
c * squareSum(T)
  <= c * K * squareSum(M)
  = squareSum(M).
```

For two fixed bases `bE,bF` and `bE',bF'` of finite-dimensional real spaces,
the matrix of a linear map in the first bases is obtained from the matrix in
the second bases by fixed left and right multiplication:

```text
[f]_{bE,bF}
  = [id_F]_{bF',bF} * [f]_{bE',bF'} * [id_E]_{bE,bE'}.
```

Applying the preceding matrix estimate gives a positive constant `c` such that

```text
c * squareSum([f]_{bE,bF}) <= squareSum([f]_{bE',bF'}).
```

The constant depends only on the two basis-change matrices, not on `f`.

## Lean Shape

Lean implements this in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean
```

with names

```text
exists_pos_const_matrixCoordinateSquareSum_le_of_mul_eq
exists_pos_const_forall_matrixCoordinateSquareSum_le_mul
exists_pos_const_linearMap_toMatrix_squareSum_le_of_basis_change
exists_pos_const_forall_linearMap_toMatrix_squareSum_le_of_basis_change
```

The first theorem is the pointwise bare matrix statement.  The second is the
uniform bare matrix statement where the constant depends only on `L` and
`Rmat`.  The third packages the basis-change identity through
`LinearMap.toMatrix_comp`, and the fourth records the uniform basis-change
form where the constant depends only on the two fixed source/target basis
pairs, not on `f`.

## Boundary

This is global finite-dimensional coordinate algebra.  It needs no continuity,
source-rank hypothesis, product chart, density/Jacobian transport, covariance
lower bound, normal-crossing construction, pole order, or RLCT extraction.

It also does not yet compare with `lossDLN`: the missing separate bridge is a
formal map from a p. 13 reversed-edge family to the `Tuple d` consumed by
`lossDLN`, plus the theorem that `mult` of that tuple is the endpoint chain-map
matrix in chosen original bases.
