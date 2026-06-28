# Reproduction - A2 Case 2 explicit selected-entry source chart

Date: 2026-06-28.

Status: reproduced; Lean target selected.

## Target

The previous source-readback theorem was existential:

```text
given yNext with yNext_pivot != 0,
exists residual, Cprime, E = edgeMatrix(residual,Cprime) ...
```

That is enough for pointwise source production, but it is not an explicit
parametrized family.  A later source/pushforward or chart-certificate theorem
needs this explicit function before regularity and measure properties can be
proved.

The target here is to define, for every successor selected-entry coordinate
vector `yNext`,

```text
residual(yNext),
Cprime(yNext),
data(yNext) = case2PostPivotRetainedPassiveData residual(yNext) Cprime(yNext),
E(yNext) = data(yNext).edgeMatrix,
```

and prove

```text
sourceRecursiveDetChart E(yNext),
residualFactorProduct (sourceReadback E(yNext)).C (Fin.last 2) 0
  = T(yNext),
```

where `T(yNext)` is the successor selected-entry matrix.

The product equality is valid for all `yNext`.  The additional nonzero
conclusion requires only the extra hypothesis that the displayed successor
pivot coordinate `yNext_(J+2,J+2)` is nonzero.

## Explicit Construction

Fix an endpoint equivalence

```text
eNext : tau ~= Case2ResidualColIndex n S (J+1).
```

Let

```text
T(yNext) =
  AoyagiResidualBlockCoordinateIndex.matrix
    (c |-> selectedEntryChartMap_pivot(yNext, eNext(c))).
```

This is the existing Lean object

```text
case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext.
```

Choose the old post-pivot residual data by zero extension of the right-reindexed
target matrix:

```text
D(yNext) = T(yNext).submatrix id eNext.symm,
residual(yNext)(a,b) =
  if (a,b) lies in the successor residual block then D(yNext)(a,b) else 0.
```

This is exactly `case2SourceResidualBlockExtension` applied to `D(yNext)`.
The already reproduced zero-extension calculation gives

```text
case2DisplayedPostPivotResidualBlock residual(yNext)
  = D(yNext).
```

Choose the free following factor to be the reindexed identity

```text
F(yNext) = (1 : Matrix successorCols successorCols).submatrix id eNext,
```

and choose `Cprime(yNext)` by putting this matrix into the lower tail of the
pivot-first `Cprime` matrix, with zero top row.  Then

```text
case2DisplayedPostPivotFreeFollowingFactor Cprime(yNext)
  = F(yNext).
```

Therefore the displayed two-edge product is

```text
case2DisplayedPostPivotFreeTwoEdgeFactorProduct residual(yNext) Cprime(yNext)
  = D(yNext) * F(yNext)
  = T(yNext).submatrix id eNext.symm
      * (1).submatrix id eNext
  = T(yNext).
```

The last equality is the finite reindexed-identity multiplication lemma.

## Readback Through Retained-Passive Source

Package the two factors as

```text
data(yNext) =
  case2PostPivotRetainedPassiveData residual(yNext) Cprime(yNext).
```

The synthetic datum always lies in the retained-passive determinant chart:
`Ctop = 1` and the only passive `A1` block is `1`.  Hence the retained-passive
source-map theorem gives

```text
sourceRecursiveDetChart data(yNext).edgeMatrix.
```

The readback-after-source inverse gives

```text
sourceReadback data(yNext).edgeMatrix = data(yNext).
```

Consequently

```text
residualFactorProduct (sourceReadback data(yNext).edgeMatrix).C (Fin.last 2) 0
  = residualFactorProduct data(yNext).C (Fin.last 2) 0
  = case2DisplayedPostPivotFreeTwoEdgeFactorProduct residual(yNext) Cprime(yNext)
  = T(yNext).
```

This is the desired explicit selected-entry-to-retained-passive source family.

## Nonzero Boundary

For the selected-entry chart, the displayed successor pivot coordinate of
`T(yNext)` is `yNext_(J+2,J+2)`.  Hence if this coordinate is nonzero, then
`T(yNext) != 0`, and the source-readback residual-factor product is nonzero by
the equality above.

No division by this coordinate is used in the construction.  The pivot-nonzero
condition is only a nonzero-output condition.

## Proved / Assumed / Cited / Deferred

**Proved by this reproduction.** An explicit finite selected-entry-coordinate
map `yNext |-> E(yNext)` into the retained-passive source-recursive determinant
chart, with actual `sourceReadback` residual-factor product equal to the
successor selected-entry matrix for all `yNext`.

**Assumed.** Branch hypotheses `hS`, `hcont`, `hnext`, the endpoint equivalence
`eNext`, and finite typeclass data for the matrix endpoints.

**Cited.** Aoyagi pp. 19-22 for the Case 2 selected-pivot clearing algebra.
The source/readback inverse is local retained-passive infrastructure already
formalised in this expedition.

**Deferred.** Continuity/measurability of `yNext |-> E(yNext)`;
Jacobian/pushforward density comparison with retained-passive product density;
original source-rank coverage; global normal-crossing chart production; pole
order; RLCT.

## Lean Shape

Expected new public names:

```text
case2DisplayedPostPivotSourceResidualOfMatrix
case2DisplayedPostPivotFreeCprimeOfMatrix
case2DisplayedPostPivotFreeTwoEdgeFactorProduct_sourceResidualOfMatrix_freeCprimeOfMatrix
case2SuccessorSelectedEntrySourceResidual
case2SuccessorSelectedEntrySourceCprime
case2DisplayedPostPivotFreeTwoEdgeFactorProduct_successorSelectedEntrySource_eq
case2PostPivotSelectedEntryRetainedPassiveData
case2PostPivotSelectedEntrySourceEdgeFamily
case2PostPivotSelectedEntrySourceEdgeFamily_sourceRecursiveDetChart
case2PostPivotSelectedEntrySourceReadback_residualFactorProduct_eq_successorSelectedEntryMatrix
```
