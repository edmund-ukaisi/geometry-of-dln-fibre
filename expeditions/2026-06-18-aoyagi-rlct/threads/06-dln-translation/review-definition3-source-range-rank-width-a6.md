# Review - Definition 3 source-range rank-width

Date: 2026-06-24.

Reviewer: Singer the 2nd, xhigh independent checker.

Verdict: PASS, with wording and theorem-shape fixes applied.

## Scope

Reviewed
`reproduction-definition3-source-range-rank-width-a6.md` against the Lean
interfaces in `ThroughLayerBasis.lean`, `ProductReductionBoundary.lean`,
`BasepointCertificate.lean`, and `Definition3Bridge.lean`.

## Findings

The rank-width argument is mathematically correct.  The total paper product
has a through-subspace of dimension equal to the product rank at every layer;
therefore the product rank is bounded by every layer dimension.

The Lean ingredients already exist:

```text
exists_chain_throughSubspaces
paperTotalMap
reverseVertex
reverseEdge
paperEndpointFixedBaseSourceRankStratum
AoyagiDefinition3SourceData.exists_selectedReducedWidthCeilData_of_rankWidth
```

## Fixes Applied

- The reproduction now explicitly says the through-subspace for paper layer
  `W k` is indexed by `k.rev`, since `reverseVertex W j = W (j.rev)`.
- The direct Definition 3 consumer is specialized to
  `S : AoyagiDefinition3SourceData N ell H r C`; the bridge proves the source
  range `1 <= s <= N+1`.
- The source-rank stratum discussion now says the edge-rank data are carried
  by the boundary but are not needed for this rank-width proof.  Only the
  total product rank equality is used.
- The Lean theorem shape includes the finite-dimensional hypotheses, and the
  source-stratum theorem inherits the topological/normed hypotheses required
  by `paperEndpointFixedBaseSourceRankStratum`.

## Nonclaims

The bridge does not construct selected cutpoints or Definition 3 source data.
It does not prove exact-rank strata are open, chart coverage, source
production, finite exponent formulas, normal crossings, pole order, or RLCT.
