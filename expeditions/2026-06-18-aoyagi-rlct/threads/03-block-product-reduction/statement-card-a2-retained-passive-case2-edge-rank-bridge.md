# A2 retained-passive Case 2 edge-rank bridge

## Lean statements

Generic rank API:

```text
rank_fromBlocks_eq_card_add_rank_schurComplement_of_isUnit_det_indexed
ChartLocalSuffixState.rank_retainedPassiveTransformedEdge
ChartLocalSuffixState.rank_retainedPassiveFixedBaseEdgeMatrix
ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.rank_edgeMatrix
```

Case 2 selected-entry API:

```text
rank_case2DisplayedPostPivotResidualBlock_sourceResidualOfMatrix
rank_case2DisplayedPostPivotFreeFollowingFactor_freeCprimeOfMatrix
rank_case2PostPivotSelectedEntrySourceEdgeFamily_zero
rank_case2PostPivotSelectedEntrySourceEdgeFamily_one
```

## Claim

For a retained-passive nonredundant datum in the determinant chart, every
fixed-base source edge has rank

```text
card rho + rank(stored residual block C_p).
```

For the explicit continuing Case 2 selected-entry source family, this gives

```text
rank(E 0) = card rho + card tau,
rank(E 1) = card rho + rank(successor selected-entry matrix).
```

## Source and reproduction

This is Aoyagi p.13 block Schur algebra plus the pp.19-22 Case 2 selected-entry
construction of the post-pivot residual block and following factor.  The
pen-and-paper reproduction is
`reproduction-a2-retained-passive-case2-edge-rank-bridge.md`.

## Nonclaims

These theorems do not assert membership in `paperEndpointFixedBaseSourceRankStratum`.
They do not choose numerical `rEdge`, prove exact successor-matrix rank, prove
source-rank coverage, prove exact-rank openness, transport source priors or
Jacobians, construct an analytic atlas, prove normal crossings, pole order, or
RLCT.
