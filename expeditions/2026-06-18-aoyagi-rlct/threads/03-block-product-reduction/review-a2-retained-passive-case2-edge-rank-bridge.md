# Review - A2 retained-passive Case 2 edge-rank bridge

Date: 2026-06-29.

Reviewer: xhigh `Hegel the 2nd`.

Status: PASS.

## Findings

No mathematical-fidelity findings.

## Checks

The reviewer checked:

- `rank_fromBlocks_eq_card_add_rank_schurComplement_of_isUnit_det_indexed`;
- `ChartLocalSuffixState.rank_retainedPassiveTransformedEdge`;
- `ChartLocalSuffixState.rank_retainedPassiveFixedBaseEdgeMatrix`;
- `ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.rank_edgeMatrix`;
- `rank_case2DisplayedPostPivotResidualBlock_sourceResidualOfMatrix`;
- `rank_case2DisplayedPostPivotFreeFollowingFactor_freeCprimeOfMatrix`;
- `rank_case2PostPivotSelectedEntrySourceEdgeFamily_zero`;
- `rank_case2PostPivotSelectedEntrySourceEdgeFamily_one`;
- `rank_C_of_retainedPassiveP13SourceEdgeFamilyOfData_mem_sourceRankStratum`.

The Schur-complement formula uses the indexed complement

```text
A4 - A3 * A1^{-1} * A2.
```

In the retained-passive edge, `A2 = -(A1 * F2)` and
`A4 = C - A3 * F2`, so the Schur complement reduces to `C`.  The fixed-base
edge differs by a block unitriangular left factor, hence has the same rank.

For the explicit continuing Case 2 selected-entry family, edge `0` reads the
reindexed identity following factor and edge `1` reads the reindexed successor
residual matrix.  The proved ranks are therefore

```text
rank(E 0) = card rho + card tau,
rank(E 1) = card rho + rank(successor selected-entry matrix).
```

The source-stratum consumer keeps membership in
`paperEndpointFixedBaseSourceRankStratum` as an explicit hypothesis.  It derives
`rank(data.C p) = rEdge p - r`; it does not prove that the retained-passive
family lies in the stratum.

## Boundary

No hidden quiver-paper dependency was found.  No exact numerical rank for the
successor selected-entry matrix is inferred.  This slice does not prove
source-rank coverage, selected-entry image equality, source-prior or Jacobian
transport, analytic atlas construction, normal crossings, pole order, or RLCT.

## Verification Gap

The reviewer was read-only and did not run Lean.  Controller-focused builds and
hygiene checks are tracked in `synthesis.md` for this slice.
