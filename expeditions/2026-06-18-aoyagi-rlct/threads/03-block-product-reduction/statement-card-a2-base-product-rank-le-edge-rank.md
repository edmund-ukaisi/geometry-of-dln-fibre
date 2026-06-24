# Statement Card - A2 base product rank bounded by edge ranks

Date: 2026-06-24.

Lean files:

- `lean/DLNFibre/DLN/Aoyagi/ProductReductionBoundary.lean`
- `lean/DLNFibre/DLN/Aoyagi/ProductReductionEntryIdealBoundary.lean`
- `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionAlgebraicSource.lean`

## Lean Names

```text
paperTotalMap_finrank_range_le_reverseEdge_finrank_range
paperEndpointFixedBaseSourceRankStratum_selfBase_mem_of_rank_eq
paperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate_of_isCompl_of_rank_eq
exists_paperEndpointCanonicalProductDifferenceLocalSourceCertificate_of_rank_eq
exists_aoyagiCanonicalProductDifferenceRegularCoordinateIdealSource_of_rank_eq
```

## Statement Shape

For every base edge `p`, Lean proves

```text
finrank(range(paperTotalMap W B))
  <= finrank(range(reverseEdge W B p)).
```

The proof factors the full reversed chain through the single edge `p` and
uses the rank bound for a composite.  The basepoint source-rank-stratum
constructor can therefore derive `r <= rEdge p` from the supplied rank
equalities `hprod` and `hedge`.

The `_of_rank_eq` constructors thread this derived base inequality into the
canonical product-difference local source certificate and the stronger
regular-coordinate ideal source predicate.

## Scope

Base-chain finite-dimensional linear algebra and source-side predicate
packaging.

## Nonclaims

No exact-rank or source-rank openness, no nearby-point rank theorem beyond the
existing guarded source stratum, no analytic germ-ideal transport, no `Cfull`
construction, no regular ideal transport, coverage, Jacobian compatibility,
exponent shift, normal crossings, pole order, or RLCT.
