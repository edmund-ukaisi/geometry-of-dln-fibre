# Review - Definition 3 source-rank final handoff

Date: 2026-06-24.

Reviewer: Feynman the 2nd, xhigh independent checker.

Verdict: PASS, narrowly.

## Scope

Reviewed the proposed source-rank-stratum variants of the existing
Definition 3 final-boundary and Eq5 terminal-order source-data wrappers.

The target is only to replace the explicit source-range rank-width hypothesis

```text
forall s, 1 <= s -> s <= N+1 -> r <= H s
```

by:

```text
x in paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge
forall k : Fin(N+1), H(k+1) = finrank K (W k).
```

## Findings

The target is legitimate source movement if limited to the four existing
source-data handoffs:

```text
AoyagiDefinition3SourceData.exists_theorem2SuppliedFinalBoundary_of_sourceRankStratum
AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_sourceRankStratum
AoyagiDefinition3SourceData.exists_theorem2SuppliedFinalBoundary_of_sourceRankStratum_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload
AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_sourceRankStratum_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload
```

The proof should be pure composition:

```text
paperEndpointFixedBaseSourceRankStratum_sourceRangeRankWidth W B hx hH
```

followed by the existing `_of_rankWidth` wrappers.

## Limits

The review explicitly warns against adding projection, pair-form, or duplicate
convenience variants.  The slice is worthwhile only because the old rank-width
input was repeated at final theorem sockets and the new source-rank bridge
already proves it from A2 data.

## Nonclaims

The handoff does not construct selected cutpoints or prove
`AoyagiDefinition3SourceData`.

It does not prove exact-rank openness, neighborhood membership in a rank
stratum, or the dimension convention.

It does not construct Eq5 endpoint families, prove Lemma 5 exactness, prove
active-ratio or chart-count facts, produce charts, prove normal crossings,
prove pole order, or prove RLCT.
