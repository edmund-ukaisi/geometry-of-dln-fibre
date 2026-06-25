# Reproduction - A2 edge-matrix signed-box adapted-loss finite integral

Date: 2026-06-25.

Status: pen-and-paper reproduction for a measurability-weakened finite-integral
front end.

## Source Boundary

This is not a new product-chart theorem.  It keeps the signed-box source chart,
weighted pushforward, residual monomial lower bound, product-coordinate adapted
lower bound, adapted-to-loss comparison, and positive continuous product density
as explicit hypotheses.

The only change from the continuous-edge adapted-loss front end is the entry
hypothesis used for measurable bookkeeping.  Instead of assuming global
`Continuous Cedge`, assume directly that the fixed-base edge matrix family used
by the deterministic p.13 suffix recursion is measurable:

```text
x |-> paperEndpointFixedBaseEdgeMatrixOfReverseEdges(..., Cedge x)
```

This is the finite matrix object from which the source edge-rank stratum and the
residual coordinate map are read.

## Calculation

Let

```text
S = paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge.
```

The source-rank stratum is the conjunction of constant source conditions and the
exact rank equalities

```text
finrank(range(Cedge x p)) = rEdge p.
```

For each edge `p`, the fixed-base edge matrix has the same rank as the edge map:

```text
rank(edgeMatrix(x,p)) = finrank(range(Cedge x p)).
```

Exact finite matrix rank loci are measurable because `rank <= q` is a closed
determinantal condition and `rank = q` is the difference of two such loci.  Thus
measurability of the full fixed-base edge-matrix family gives `MeasurableSet S`.

The residual signed-box constructor already consumes the same edge-matrix
measurability and returns

```text
forall^ae x d(mu.restrict S), 0 < residualSquareSum(x),
int^- ofReal(residualSquareSum(x)^(-t)) d(mu.restrict S) < infinity.
```

The adapted-loss hypotheses on the source filter and regular ball are

```text
c  * (residualSquareSum(x) + squareSum(u)) <= adaptedSquareSum(x,u),
c0 * adaptedSquareSum(x,u) <= loss(x,u).
```

The existing adapted-loss finite-integral theorem multiplies these constants
and then applies the p.13 regular-square finite-side estimate after shrinking
the regular radius using the positive continuous density at `(x0,0)`.

## Lean Shape

The intended theorem is

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.
exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_const_mul_adaptedProductDifferenceSquareSum_le_loss_continuousAt_pos_density
```

in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
```

with a supporting source-stratum measurability theorem from edge-matrix
measurability.

The concrete original square-Frobenius consumer is

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.
exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_adaptedProductDifferenceSquareSum_lower_continuousAt_pos_density
```

in

```text
lean/DLNFibre/DLN/Aoyagi/OriginalLossLocalMeasure.lean
```

It proves the adapted-to-original comparison from the existing finite endpoint
basis comparison and still consumes the same product-coordinate adapted lower
bound.

## Boundaries

This theorem is conditional measure/integrability plumbing.  It does not
construct the product chart, prove source coverage, prove the weighted
pushforward identity, transport Jacobian/prior density, derive the
product-coordinate adapted lower bound, compare original `lossDLN`, produce a
normal-crossing certificate, compute pole order, or extract an RLCT.
