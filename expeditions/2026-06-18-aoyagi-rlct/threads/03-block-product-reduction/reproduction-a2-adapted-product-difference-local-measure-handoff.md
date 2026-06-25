# Reproduction - A2 adapted product-difference local-measure handoff

Date: 2026-06-25.

Status: pen-and-paper reproduction for converting the fixed-base adapted
product-difference source-filter comparison into restricted-measure a.e.
statements.

## Source Anchor

Aoyagi p. 13 rewrites the product-difference generators after the triangular
block reduction.  The preceding fixed-base slice proved that, at a continuous
self-base paper chain, there is a positive constant `c` such that

```text
(c/2) * (regularSquareSum(x) + residualSquareSum(x))
  <= adaptedProductDifferenceSquareSum(x)
```

eventually on the fixed-base source-rank filter.

This note only moves that already-proved source-filter inequality into the
measure-theoretic form used by the local p. 13 integrability adapters.

## Derivation

Let

```text
S = paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge.
```

Assume `S` is measurable for the base measure wrapper.  The existing
source-filter theorem gives

```text
exists c > 0,
  forall eventually x in nhdsWithin x0 S,
    (c/2) * (regularSquareSum(x) + residualSquareSum(x))
      <= adaptedProductDifferenceSquareSum(x).
```

The local-measure handoff lemma says that any predicate eventually true in
`nhdsWithin x0 S` is true almost everywhere after restricting an arbitrary base
measure `mu` to `U inter S`, for some open neighborhood `U` of `x0`.

Therefore there exist `c > 0` and an open neighborhood `U` of `x0` such that

```text
for mu.restrict (U inter S)-almost every x,
  (c/2) * (regularSquareSum(x) + residualSquareSum(x))
    <= adaptedProductDifferenceSquareSum(x).
```

The product-measure first-projection form is identical: after restricting the
base factor to `U inter S`, the same predicate holds for almost every
`z : alpha x beta`, applied to `z.1`.

## Lean Shape

The Lean theorem should live in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
```

inside `PaperEndpointFixedBaseRegularCoordinateSourceData`, next to the
existing local-measure wrappers for the literal and supplied-loss p. 13
comparisons.

Expected names:

```text
exists_pos_const_open_ae_restrict_source_half_regular_add_residual_squareSum_le_adaptedProductDifferenceSquareSum_selfBase
exists_pos_const_open_ae_restrict_source_prod_fst_half_regular_add_residual_squareSum_le_adaptedProductDifferenceSquareSum_selfBase
```

Both consume:

```text
sourceData
hCedge : ContinuousAt Cedge x0
hbase  : Cedge x0 = fun p => reverseEdge W B p as a continuous linear map
hsource_meas : MeasurableSet S
```

The proof destructs

```text
sourceData.exists_pos_const_half_regular_add_residual_squareSum_eventually_le_adaptedProductDifferenceSquareSum_selfBase_nhdsWithin_source
```

and then applies either

```text
exists_open_ae_restrict_inter_of_eventually_nhdsWithin
exists_open_ae_restrict_inter_prod_fst_of_eventually_nhdsWithin
```

to the eventual inequality.

## Boundary

The right-hand side is the adapted fixed-base product-difference square-sum.
It is not the original DLN/statistical loss.  The theorem does not construct
the p. 13 product chart, compare basis-dependent Frobenius norms, prove a
covariance lower bound, transport a Jacobian or prior density, prove residual
zero-locus nullity, prove residual negative-power integrability, produce
normal crossings, determine pole order, or extract an RLCT.
