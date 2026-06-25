# Reproduction - A2 local-source product-family adapted lower bound

Date: 2026-06-25.

## Source Target

Aoyagi p.13 introduces regular variables by replacing the source-side chain
with a product-coordinate family.  The Lean development already has the
self-base multi-edge product-coordinate family and proves, on the full
source-rank stratum, a local lower bound of the form

```text
c * (residualSquare(x) + regularSquare(u))
  <= adaptedProductDifferenceSquareSum(CedgeProd(x,u)).
```

The previous local-source package extracts a measurable local source

```text
source = U inter sourceRankStratum
```

from the fixed-base source certificate and proves

```text
nhdsWithin x0 source = nhdsWithin x0 sourceRankStratum.
```

The present step should combine these two facts, so future chart work can use
the explicit local source rather than restating bounds over the full
source-rank stratum.

## Calculation

Let

```text
S = paperEndpointFixedBaseSourceRankStratum V Bv CedgeBase r rEdge.
```

The source-data local-source theorem gives

```text
source = U inter S,
MeasurableSet source,
x0 in source,
source subset S,
nhdsWithin x0 source = nhdsWithin x0 S.
```

The existing explicit product-family theorem gives positive constants
`R` and `c`, with `R <= Rmax`, such that

```text
eventually x in nhdsWithin x0 S,
  for all u in ball(0,R),
    c * (residualSquareBase(x) + squareSum(u))
      <= adaptedProductDifferenceSquareSum(CedgeProd(x,u)).
```

Using the filter equality above, the same eventual statement holds in
`nhdsWithin x0 source`.  No analytic measure argument is needed: this is only a
filter transport of an already-proved p.13 product-coordinate lower bound.

The local source still carries the certificate's source-rank conclusion:

```text
for all x in source,
  PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks ...
```

This keeps the source-rank data available for later chart construction.

## Lean Statement Shape

The Lean theorem is:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_measurable_localSource_pos_radius_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase
```

It returns:

- the local source `source` and open neighborhood `sourceU`;
- the radius `R` and lower-bound constant `c`;
- measurability, basepoint membership, and inclusion in the source-rank
  stratum;
- source-rank conclusions on `source`;
- the equality `nhdsWithin x0 source = nhdsWithin x0 sourceRankStratum`;
- the p.13 adapted product-difference lower bound on `nhdsWithin x0 source`.

## Nonclaims

This theorem does not construct a signed-box residual chart, prove source
coverage or a chart image theorem, prove weighted pushforward, compute a
Jacobian/source-density formula, produce residual or source-density
monomial-unit identities, prove normal crossings, compute pole order, or
extract RLCT.
