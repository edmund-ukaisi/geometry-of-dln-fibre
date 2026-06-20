# Pen-and-paper reproduction - Case 2 post-pivot source-following product

Status: checked adapter from Aoyagi's displayed lower-row product to the next
same-stage source following factor.

This note combines two already isolated elementary facts:

- the lower rows of `D''' * C'` are the post-pivot lower-right cleared block
  times the reindexed tail of `C'`;
- for Aoyagi's displayed `C' = Q^-1 C` with
  `Q^-1 = [1 y; 0 I]`, the tail of `C'` is the corresponding tail of `C`.

The result is still a continuing-branch adapter.  It does not construct a
successor chart family, derive recurrence or exponent post-data from chart
coordinates, prove a transition invariant, handle terminal relabeling, or
repair Aoyagi's printed Case 2 vector mismatch.

## Source

Aoyagi PDF pp. 19-22, displayed Case 2:

- the selected chart uses pivot `(J+1,J+1)`;
- after the row and column operations one has `D'''` and `C' = Q^-1 C`;
- `Q^-1` has block form `[1 y; 0 I]`;
- in the continuing branch the induction is asserted with the same stage `S`
  and the index increased from `J` to `J+1`.

The PDF supports this local block algebra.  It does not supply a Lean-level
construction of the next chart family or a global transition invariant.

## Reproduction

Write the pivot-first following factor as

```text
C = [C_0]
    [C_tail].
```

Since

```text
Q^-1 = [1  y]
       [0  I],
```

we have

```text
C' = Q^-1 C
   = [C_0 + y C_tail]
     [C_tail].
```

Thus the lower tail of `C'` is `C_tail`.

The post-pivot lower-right cleared block is

```text
D_next = D - x*y,
```

with rows and columns reindexed from the displayed pivot complements to
`Case2ResidualRowIndex(n,S,J+1)` and
`Case2ResidualColIndex(n,S,J+1)`.  The lower rows of the product are therefore

```text
(D''' * C')_tail = D_next * C_tail.
```

After the post-pivot column-domain handoff, `C_tail` is exactly

```text
case2SourceFollowingFactor (n := n) (S := S) (J := J+1) C.
```

Therefore the reindexed lower-row product can be stated directly as

```text
(D''' * C')_tail =
  case2DisplayedPostPivotResidualBlock n hS hcont residual *
    case2SourceFollowingFactor (n := n) (S := S) (J := J+1) C.
```

## Lean target

Add:

```text
case2DisplayedPaperDppp_mul_Cprime_postPivot_eq_nextSameStageProduct_sourceFollowingFactor
Case2DisplayedSuppliedChartFamilyBoundary.postPivotNextSameStageProduct_sourceFollowingFactor
Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_postPivotNextSameStageProduct_withSourceFollowingFactorAndCorrectedPostData
```

The first theorem is the raw matrix adapter.  The second is the supplied
boundary projection.  The third packages the same product identity with the
already-proved corrected post-data projections.

## Kill conditions

- Do not call the theorem chart production.
- Do not claim a successor chart-family construction.
- Do not identify the tail with a full source-produced next `C'^(S+1)`.
- Do not derive recurrence or exponent data from coordinates; the concrete
  package still uses the corrected supplied post-data constructor.
- Do not attach transition invariance, chart coverage, Jacobian arithmetic,
  normal crossings, RLCT extraction, terminal relabeling, arbitrary pivot
  coverage, or printed-vector repair.
