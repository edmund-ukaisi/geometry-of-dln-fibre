# Statement card - A2 canonical product-difference local source certificate

## Files

- `lean/DLNFibre/DLN/Aoyagi/ProductReductionEntryIdealBoundary.lean`

## Claim

The canonical product-difference local certificate can be paired with
basepoint membership in Aoyagi's source-shaped rank stratum, provided the base
total product rank, base edge ranks, and rank inequalities are supplied.

## Lean Names

```text
PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate
paperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate_of_isCompl
PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate.exists_source_neighborhood
PaperEndpointCanonicalProductDifferenceLocalSourceCertificate
exists_paperEndpointCanonicalProductDifferenceLocalSourceCertificate
```

## Inputs

- a continuous reversed-edge family `Cedge`;
- base equality `Cedge x0 = reverseEdge B`;
- a chosen total-kernel complement for the fixed-base theorem, or the
  existential complement package;
- supplied source ranks:
  `rank(paperTotalMap B)=r`,
  `rank(reverseEdge B p)=rEdge p`,
  and `r<=rEdge p`.

## Output

The fixed-base package contains the existing canonical product-difference
local certificate and the proof

```text
x0 ∈ paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge.
```

It also exposes an ordinary neighborhood `U ∈ nhds x0` with `x0 ∈ U` such
that every `x ∈ U` satisfying the source-shaped rank-stratum predicate has the
canonical product-difference/source-rank conclusion.

## Nonclaims

No exact-rank openness, no ordinary source-neighborhood theorem, no analytic
regularity, no analytic ideal or germ transport, no regular-suspension
certificate, no normal crossings, no pole-order theorem, and no RLCT theorem.
