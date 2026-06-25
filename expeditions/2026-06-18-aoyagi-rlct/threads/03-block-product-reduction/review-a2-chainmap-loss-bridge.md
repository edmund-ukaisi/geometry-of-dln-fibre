# Review - A2 chain-map loss bridge

Date: 2026-06-25.

Reviewer: Laplace the 5th, xhigh, read-only.

Status: passed.

## Findings

No blockers.

The module boundary is correct: `ChainMapLossBridge` is a separate real-valued
module importing `ChainMapTupleBridge` and `RlctPayoff`, rather than extending
the generic field-valued tuple bridge.

The theorem family has the right scope:

```text
chainMapMatrixFrobeniusLossAgainst
lossDLN_chainMapMatrixTuple_eq_trace
lossDLN_chainMapMatrixTuple_eq_chainMapFrobenius
lossDLN_reverseVertex_chainMapMatrixTuple_eq_baseFrobenius
```

The first theorem rewrites `lossDLN d B (chainMapMatrixTuple b A)` by using
`mult_chainMapMatrixTuple`.  The target-chain version and the reverse-vertex
base-chain wrapper are appropriate specializations.

No extra hypotheses are needed beyond real vector spaces and fixed bases.  No
finite-dimensional, topology, rank, `0 < N`, target-rank, or Aoyagi chart
hypotheses belong in this finite rewrite.

## Boundary

This review only certifies the definitional Frobenius rewrite of `lossDLN`.
It does not certify an adapted-coordinate comparison, statistical loss
comparison, normal-crossing construction, pole-order computation, or RLCT
extraction.
