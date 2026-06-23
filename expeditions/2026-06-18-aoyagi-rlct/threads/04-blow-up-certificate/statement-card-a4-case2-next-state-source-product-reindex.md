# Statement Card - A4 Case 2 Next-State Source-Product Reindex

## Lean Names

```text
case2SourceOldTopSuccResidualRowEquiv
case2SourceOldTopSuccResidualColEquiv
case2DisplayedSuccessorFollowingFactor_reindex_nextSource
case2DisplayedWeightedDppp_reindex_nextSource
case2DisplayedPivotFirstRHS_reindex_nextSourceProduct
case2DisplayedPivotFirstRHS_reindex_nextSourceProduct_mul
```

## Claim

Aoyagi's displayed Case 2 pivot-first right-hand side can be reindexed into
the next same-stage source-product shape.  The old top rows plus the
surviving pivot row become source rows `1..J+1`, and the pivot-complement
lower block becomes the `(S,J+1)` residual block.

No `hnext` or nonempty next-center hypothesis is assumed; the residual tail
may be empty.

## Inputs Kept Explicit

- stage hypotheses `1 <= S`, `S <= L`;
- displayed continuation bound `J+1 <= prefixMinNat n (S+1)`;
- the pre-recurrence state and the selected chart variable;
- source residual data and source following factor `C`;
- the formula-level successor following factor, not a chart-produced object.

## Proved

Finite reindexing and matrix multiplication only:

```text
[oldTop pre weights; weighted D'''] * [oldTop(C); Q^{-1}C]
```

reindexes to

```text
[post weights 1..J+1; weighted post-pivot residual]
  * [oldTop(Csucc); residualFollowing(Csucc)].
```

The right-multiplied corollary permits a supplied final factor such as the
remaining source suffix.

## Not Proved

No construction of `Csucc`, source production of full `C'^(S+1)`, source
suffix production, successor chart family, chart coverage, transition
regularity, coordinate post-data, Jacobian arithmetic, normal crossings, pole
order, termination, RLCT, or repair of the printed Case 2 vector mismatch.

## Verification

Focused Lean check:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean
```

## Review

xhigh reviewer `McClintock the 2nd` found no blocking source-fidelity or
statement-shape issues.  The reviewer checked that the declarations are finite
index/product reindexing statements only, and recommended clarifying the
following-factor-row meaning of the column equivalence plus the absence of an
`hnext`/nonempty next-center hypothesis.

Durable review artifact:
`review-case2-next-state-source-product-reindex-a4.md`.
