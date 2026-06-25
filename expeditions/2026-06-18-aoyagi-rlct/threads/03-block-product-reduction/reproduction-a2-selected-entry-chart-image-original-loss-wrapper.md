# Reproduction - A2 selected-entry chart-image original-loss wrapper

Date: 2026-06-25.

## Scope

This slice composes two already isolated finite statements:

1. the selected-entry finite chart-image local-measure handoff, whose source is
   `Phi_p(signedBox)`;
2. the finite endpoint-basis comparison between the adapted endpoint
   product-difference square-sum and the original `lossDLN` written in fixed
   endpoint bases.

It does not construct the original p.13 DLN source chart and does not identify
the finite chart image with a source-rank stratum.

## Pen-And-Paper Composition Check

Let

```text
source = Phi_p(signedBox),
Phi_p(y)_p = y_p,
Phi_p(y)_i = y_p * y_i  for i != p.
```

The finite selected-entry handoff needs a local lower bound of the form

```text
creg * (residualBase(x) + |u|^2) <= loss(x,u)
```

on `nhdsWithin x0 source`, plus density bounds on the same source.  We keep as
an explicit hypothesis the adapted-product lower bound

```text
c * (residualBase(x) + |u|^2)
  <= adaptedProductDifferenceSquareSum(x,u).
```

The endpoint basis comparison supplies a positive constant `c0` with

```text
c0 * adaptedProductDifferenceFrobeniusLoss(x,u)
  <= lossDLN(target, chainMapTuple(CedgeProd(x,u))).
```

The already proved finite endpoint identity rewrites
`adaptedProductDifferenceFrobeniusLoss` as
`adaptedProductDifferenceSquareSum`.  Hence

```text
(c0 * c) * (residualBase(x) + |u|^2)
  <= lossDLN(target, chainMapTuple(CedgeProd(x,u))).
```

Because `c0 > 0` and `c > 0`, the product constant is positive.  The
selected-entry chart-image handoff then applies with the original loss
function

```text
loss(x,u) = lossDLN(target, chainMapTuple(CedgeProd(x,u))).
```

The chart transport and monomial integrability data are supplied by the
selected-entry chart-image theorem.  The adapted-product lower bound and
regular-fiber density bounds remain explicit assumptions over the finite chart
image.

## Lean Landing

Implemented in
`lean/DLNFibre/DLN/Aoyagi/SelectedEntryOriginalLossLocalMeasure.lean` as

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_chartMap_selectedEntryCenter_signedBox_withDensity_edgeMatrix_adaptedProductDifferenceSquareSum_lower
```

The proof calls:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_chartMap_selectedEntryCenter_signedBox_withDensity_edgeMatrix
exists_pos_const_forall_adaptedProductDifferenceFrobeniusLoss_le_lossDLN_chainMapMatrixTuple
paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss_eq_squareSum
```

The same file also contains a stronger conditional specialization whose
hypothesis explicitly states

```text
paperEndpointFixedBaseSourceRankStratum = Phi_p(signedBox).
```

That theorem is a supplied-source-stratum wrapper, not a proof of p.13 source
coverage.

## Remaining Boundary

Still not proved:

- construction of an original DLN p.13 source chart;
- source image/coverage of the source-rank stratum;
- original-source measure identity;
- derivation of the adapted-product lower bound from an original source chart;
- normal crossings, pole order, or RLCT extraction.
