# A2 retained-passive Case 2 edge-rank bridge

## Question

The current Case 2 selected-entry source construction gives a retained-passive
local-source point and a residual-factor product readout.  It does not yet give
membership in Aoyagi's source-rank stratum.  The next useful elementary step is
to compute the ranks of the constructed source edges themselves.

## Generic retained-passive rank calculation

For one retained-passive fixed-base edge, write

```text
T_p =
  [ A1_p        -A1_p F2_p ]
  [ A3_p   C_p - A3_p F2_p]
```

and

```text
E_p =
  [ I  F2_{p+1} ] T_p.
  [ 0      I    ]
```

The left factor is block unitriangular, hence invertible, so
`rank(E_p) = rank(T_p)`.

Assume `det(A1_p)` is a unit.  Schur elimination for `T_p` gives

```text
rank(T_p)
  = card rho + rank((C_p - A3_p F2_p)
      - A3_p A1_p^{-1} (-A1_p F2_p)).
```

The displayed Schur complement is exactly `C_p`, since
`A1_p^{-1} A1_p = I` on the determinant chart.  Therefore

```text
rank(E_p) = card rho + rank(C_p).
```

For nonredundant retained-passive data, the determinant-chart predicate gives
unit determinant for every solved `A1_p`, so the same formula applies to
`data.edgeMatrix p`:

```text
rank(data.edgeMatrix p) = card rho + rank(data.C p).
```

This is source-map algebra only.  It does not assert source-rank membership:
Aoyagi's source-rank stratum additionally fixes the base-product rank, fixes
the exact external `rEdge p`, and records `r <= rEdge p`.

## Case 2 selected-entry specialization

For the explicit continuing Case 2 selected-entry data,

```text
case2PostPivotSelectedEntryRetainedPassiveData.C 0
```

is the post-pivot free following factor built from
`case2SuccessorSelectedEntrySourceCprime`.  By definition this `Cprime` is
`case2DisplayedPostPivotFreeCprimeOfMatrix`, whose following-factor tail is
the reindexed identity

```text
(1 : Matrix (Case2ResidualColIndex n S (J+1))
            (Case2ResidualColIndex n S (J+1)) R).submatrix id eNext.
```

Because `eNext : tau ~= Case2ResidualColIndex n S (J+1)`, reindexing preserves
rank and the identity matrix has full rank.  Thus

```text
rank(C_0) = card tau.
```

Consequently the first constructed Case 2 edge should satisfy

```text
rank(case2PostPivotSelectedEntrySourceEdgeFamily ... 0)
  = card rho + card tau.
```

For the second edge,

```text
case2PostPivotSelectedEntryRetainedPassiveData.C 1
```

is the displayed post-pivot residual block, reindexed from the successor
selected-entry matrix.  Reindexing the right endpoint by `eNext.symm` preserves
rank, so the honest expected formula is

```text
rank(case2PostPivotSelectedEntrySourceEdgeFamily ... 1)
  = card rho + rank(case2SuccessorSelectedEntryMatrix ...).
```

## Boundary

These rank formulas are non-tautological and useful, but they still do not
prove membership in `paperEndpointFixedBaseSourceRankStratum`.  To get that
membership one must additionally identify the intended `rEdge` values with
these computed ranks and provide the fixed base-rank and inequality fields.
