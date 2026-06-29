# A2 retained-passive source-stratum membership

## Lean statements

```text
ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.rank_endpointTransport_C
paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData_mem_sourceRankStratum_of_edgeMatrix_rank
paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData_mem_sourceRankStratum_of_C_rank
paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData_mem_sourceRankStratum_of_C_rank_add_eq
PaperEndpointFixedBaseRegularCoordinateSourceData.case2EndpointTransport_sourceEdgeFamilyOfData_mem_sourceRankStratum
```

## Claim

The retained-passive realised p.13 source family is in Aoyagi's
source-shaped rank stratum when the product rank, exact edge ranks, and
source inequalities are supplied.

On the determinant chart, it is enough to supply residual-block rank data:

```text
rank(C_p) = rEdge p - r
```

plus `r <= rEdge p`, or equivalently

```text
r + rank(C_p) = rEdge p.
```

For the endpoint-transported continuing Case 2 selected-entry source family,
the specialized edge-rank input is

```text
r + card tau = rEdge 0,
r + rank(successor selected-entry matrix) = rEdge 1.
```

## Source and reproduction

This is Aoyagi p.13 retained-passive source-rank bookkeeping plus pp.19-22
Case 2 post-pivot residual/following-factor algebra.  The pen-and-paper
reproduction is
`reproduction-a2-retained-passive-source-stratum-membership.md`.

## Nonclaims

These theorems prove pointwise source-stratum membership under explicit rank
data.  They do not prove local source-rank coverage, exact-rank openness,
selected-entry image equality, source-prior or Jacobian transport, analytic
atlas construction, normal crossings, pole order, or RLCT.  The Case 2 wrapper
does not compute a numerical rank for the successor selected-entry matrix.
