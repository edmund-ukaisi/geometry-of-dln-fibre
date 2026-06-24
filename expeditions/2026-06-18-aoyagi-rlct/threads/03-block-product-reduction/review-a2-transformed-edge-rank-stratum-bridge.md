# Review - A2 transformed-edge rank-stratum bridge

Date: 2026-06-24.

Reviewer: Linnaeus, xhigh read-only review.

Status: pass, no blocking or correctness findings.

## Scope Reviewed

- Lean theorem
  `paperEndpointFixedBase_transformedEdgeRanks_iff_edgeRankStratum` in
  `lean/DLNFibre/DLN/Aoyagi/ProductReductionBoundary.lean`.
- Source reproduction note
  `reproduction-a2-transformed-edge-rank-stratum-bridge.md`.
- Statement card
  `statement-card-a2-transformed-edge-rank-stratum-bridge.md`.

The review checked only the transformed-edge rank-predicate bridge.  It did
not audit exact-rank openness, source chart production, analytic ideal
transport, normal crossings, pole order, or RLCT, because the checkpoint does
not claim those results.

## Findings

No blocking findings.

The Lean bridge is narrowly scoped.  It proves a pointwise equivalence between
the transformed-edge rank equalities used by the recursive suffix state and
`paperEndpointFixedBaseEdgeRankStratum`, whose definition is exact source edge
rank.  It does not assert openness, chart production, analytic transport,
normal crossings, pole order, or RLCT.

The determinant-unit rank-preservation principle is the right proof principle.
`ChartLocalSuffixState.transformedEdge` is exactly left multiplication by
`[I S.B; 0 I]`, and the proof constructs that same block-unitriangular
multiplier before applying `Matrix.rank_mul_eq_right_of_isUnit_det`.  This
matches Aoyagi pp. 10-13: Lemma 2 uses block-unitriangular reductions, and
Theorem 3 applies the next step to the transformed next matrix.

The documentation stays appropriately nonclaiming.  The reproduction note
states that the bridge is only a finite rank-predicate equality, and its
"Not Claimed" and "Kill Conditions" sections exclude the risky conclusions.
The statement card likewise defers exact-rank openness, source-stratum
nonemptiness, source chart production, analytic ideal transport,
regular-suspension/RLCT additivity, normal-crossing production, pole order,
and RLCT extraction.

## Reviewer Caveat

The reviewer did not rerun Lean.  The review was intentionally read-only to
avoid writing build artifacts.  Mechanical verification is recorded separately
in the statement card.
