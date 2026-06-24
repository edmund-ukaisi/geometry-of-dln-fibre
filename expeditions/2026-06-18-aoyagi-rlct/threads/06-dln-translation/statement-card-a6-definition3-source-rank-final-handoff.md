# Statement card - A6 Definition 3 source-rank final handoff

Status: Lean bridge landed.

Reproduction:
`reproduction-definition3-source-rank-final-handoff-a6.md`.

Independent review:
`review-definition3-source-rank-final-handoff-a6.md`.

## Target

Replace a repeated final-socket hypothesis

```text
forall s, 1 <= s -> s <= L+1 -> r <= H s
```

by the source-rank stratum plus the explicit dimension convention, with
`L = N`.

## Intended Lean Slice

Final-boundary bridge:

```text
DLNFibre.DLN.Aoyagi.Theorem2SourceRankFinalBridge
```

with:

```text
AoyagiDefinition3SourceData.exists_theorem2SuppliedFinalBoundary_of_sourceRankStratum
AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_sourceRankStratum
```

Eq5 bridge:

```text
DLNFibre.DLN.Aoyagi.Theorem2SourceRankEq5Bridge
```

with:

```text
AoyagiDefinition3SourceData.exists_theorem2SuppliedFinalBoundary_of_sourceRankStratum_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload
AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_sourceRankStratum_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload
```

## Boundary

The new bridge should only compose the existing source-rank rank-width theorem
with existing final-boundary/Eq5 wrappers.  It should keep selected cutpoints,
Definition 3 source data, extraction, finite formula, active-ratio,
chart-count, and Eq5 payload obligations explicit.

No selected-cutpoint construction, no exact-rank openness, no chart
production, no normal-crossing proof, no pole-order proof, and no RLCT proof.

## Verification

Focused verification:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.Theorem2SourceRankFinalBridge
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.Theorem2SourceRankEq5Bridge
```

passed on 2026-06-24.
