# Pen-and-paper reproduction - A4 source-current stack without chart family

Status: reproduced; xhigh review pending.

## Source Anchor

Aoyagi PDF pp. 19-22, Case 2.  In the continuing branch, the displayed
top-left pivot chart carries the old top source rows, the displayed
pivot-first following block, the transported paper factor `C' = Q^-1 C`, and
the raw right source suffix.  The source-current stack theorem is a row-index
presentation of that finite stack identity over the source row interval
`1,...,n(S+1)`.

This note records only the row-presentation wrapper.  It does not produce the
successor following matrix, source suffix, successor chart family, or
transition data.

## Existing Row Presentation

The existing source-current theorem rewrites the old-top/source-suffix
paper-`C'` stack through the finite row equivalence

```text
case2SourceOldTopPaperCprimeRowEquiv n hS hcont
```

which identifies the disjoint stack

```text
old top rows 1..J,
pivot row J+1,
post-pivot rows J+2..n(S+1)
```

with the single current source-row interval `1..n(S+1)`.

The two row-reindex identities are

```text
case2SourceCurrentFollowingBlock_submatrix_oldTopPaperCprimeRowEquiv
case2SourceSuccessorFollowingBlock_submatrix_oldTopPaperCprimeRowEquiv
```

They state respectively that the old source-current following block reindexes
to

```text
[oldTop(C); displayedSourceFollowingFactor(C)]
```

and that the formula-level successor source-current block reindexes to

```text
[oldTop(C); paperCprime(C)].
```

Substituting these two identities into the old-top/source-suffix stack
identity gives the source-current-row equality.  No new matrix calculation is
introduced after the old-top/source-suffix paper-`C'` stack theorem.

## Direct Finite Proof

The old proof routed through

```text
sourceChartMap_continuingOldTopSourceSuffixPaperCprimeStack_withCorrectedPostData
```

and therefore carried a `Case2ResidualBlockChartFamilyBoundary` argument.
After the old-top/source-suffix stack directification, the same finite stack
identity is available from

```text
sourceChartMap_continuingOldTopSourceSuffixPaperCprimeStack_withoutChartFamily
```

with no `ChartRegular`, `TransitionRegular`, or
`Case2ResidualBlockChartFamilyBoundary` inputs.

The chart-family-free source-current proof should therefore:

1. destruct
   `sourceChartMap_continuingOldTopSourceSuffixPaperCprimeStack_withoutChartFamily`;
2. preserve next-center nonemptiness, corrected exponent data, level/gap data,
   recurrence `case2Gap`, and finite center principalization fields;
3. rewrite only the two following-factor stacks by the row-reindex identities;
4. leave the raw source suffix as the same supplied `sourceSuffixProduct`.

The older chart-family-bearing source-current API should remain as a
compatibility wrapper that ignores `chartFamily` and delegates to the direct
constructor.

## Lean Targets

```text
sourceChartMap_continuingOldTopSourceSuffixSuccFollowingBlock_withoutChartFamily
sourceChartMap_continuingOldTopSourceSuffixSuccFollowingBlock_withCorrectedPostData
```

The second name is the existing API; after this slice it should delegate to
the first.

## Boundary Checks

- This is formula-level source-current row bookkeeping only.
- The formula-level successor block is `case2SourceSuccessorFollowingBlock`;
  the theorem does not prove it is chart-produced.
- The raw source suffix remains supplied.
- The corrected exponent and recurrence post-data are inherited from the
  finite old-top/source-suffix stack proof; they are not derived from
  polynomial-coordinate chart construction.
- No source production of `Csucc` or `C'^(S+1)`, suffix production, successor
  chart-family construction, coverage or transition regularity, analytic
  Jacobian or volume-form theorem, normal crossings, pole order, RLCT, or
  repair of the printed Case 2 vector mismatch is claimed.

## Kill Conditions

- Kill the direct theorem if it takes `ChartRegular`, `TransitionRegular`, or
  `Case2ResidualBlockChartFamilyBoundary`.
- Kill the direct proof if it calls
  `sourceChartMap_continuingOldTopSourceSuffixPaperCprimeStack_withCorrectedPostData`
  instead of the chart-family-free old-top/source-suffix stack theorem.
- Do not rename this as source production, transition invariance, or a
  normal-crossing certificate.
