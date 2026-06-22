# Reproduction - Case 2 Source Current Stack

Date: 2026-06-22.

Scope: a source-current-row restatement of the continuing Case 2
old-top/source-suffix stack identity.  This consumes the finite row-reindexing
adapter and does not add chart-production content.

## Existing Stack Identity

The previous continuing old-top/source-suffix theorem proves an equality of
stacked matrices:

```text
((fromBlocks Wold 0 0 L) *
  [oldTop(C); displayedSourceFollowingFactor(C)] * suffix)
=
((fromBlocks Wold 0 0 R) *
  [oldTop(C); paperCprime(C)] * suffix).
```

It also carries the next-center nonemptiness, corrected post exponent data,
post level/gap data, and finite current-center principalization facts.

## Source-Current Rewrite

The source-current row reindexing adapter identifies the stacked row type

```text
old top rows 1..J,
pivot row J+1,
post-pivot rows J+2..n(S+1)
```

with the single source-row interval `1..n(S+1)`.

Under this equivalence:

```text
case2SourceCurrentFollowingBlock(C).submatrix e id
  = [oldTop(C); displayedSourceFollowingFactor(C)]
```

and

```text
case2SourceSuccessorFollowingBlock(Csucc).submatrix e id
  = [oldTop(C); paperCprime(C)].
```

Substituting these two equalities into the existing stack identity gives the
new source-current-row statement:

```text
((fromBlocks Wold 0 0 L) *
  currentFollowingBlock(C).submatrix e id * suffix)
=
((fromBlocks Wold 0 0 R) *
  successorFollowingBlock(Csucc).submatrix e id * suffix).
```

No new algebraic calculation is introduced; this is a row-index presentation
adapter.

## Lean Target

```text
Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_continuingOldTopSourceSuffixSuccFollowingBlock_withCorrectedPostData
```

## Nonclaims

- No chart production of `Csucc`.
- No source production of `C'^(S+1)`.
- No source-suffix production.
- No recurrence or exponent post-data production beyond the already supplied
  fields carried by the previous theorem.
- No transition invariant.
- No Jacobian arithmetic.
- No normal crossings, pole order, termination, or RLCT extraction.
