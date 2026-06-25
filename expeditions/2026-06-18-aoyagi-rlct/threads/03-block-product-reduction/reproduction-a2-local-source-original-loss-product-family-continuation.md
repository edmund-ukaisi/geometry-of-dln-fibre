# Reproduction - A2 local-source original-loss product-family continuation

Date: 2026-06-25.

## Source Target

Aoyagi pp.10-13 reduce the local product-difference calculation to regular
variables plus a residual product after the block/product-coordinate
construction.  The already-formalised local-source product-family theorem gives
the local source and the p.13 adapted lower bound for the explicit self-base
multi-edge product-coordinate family.  The already-formalised original-loss
local-source socket turns such an adapted lower bound into a finite local
integral for the concrete endpoint square-Frobenius `lossDLN`.

The present step is not a new source theorem.  It is the composition of those
two packages, exposing the remaining analytic/chart inputs as a continuation
on the returned local source.

## Calculation

Let

```text
S = paperEndpointFixedBaseSourceRankStratum V Bv CedgeBase r rEdge
rho = AoyagiRegularBlockCoordinateIndex ...
CedgeProd =
  paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
    V Bv U0 hU0 CedgeBase
```

The local-source product-family package returns

```text
source = sourceU inter S,
MeasurableSet source,
x0 in source,
source subset S,
source-rank facts on source,
nhdsWithin x0 source = nhdsWithin x0 S,
0 < R,
R <= Rmax,
0 < c,
eventually on nhdsWithin x0 source:
  for all u in ball(0,R),
    c * (residualSquare(x) + squareSum(u))
      <= adaptedProductDifferenceSquareSum(CedgeProd(x,u)).
```

The local-source original-loss socket consumes exactly this adapted lower bound
and the remaining hypotheses:

```text
nu is an additive Haar measure,
0 <= C,
0 < t,
residualSquare(x) > 0 for mu.restrict source-a.e. x,
residualNegPowerIntegrableOn CedgeBase source mu t,
density nonnegative on nhdsWithin x0 source times ball(0,R),
density <= C on nhdsWithin x0 source times ball(0,R).
```

It concludes the existence of an open neighborhood `U` of `x0` such that the
ball-supported lower integral of

```text
lossDLN(target, chainMapMatrixTuple(CedgeProd(x,u)))
  ^ (-(t + regularVariableCount / 2))
  * density(x,u)
```

over `(mu.restrict (U inter source)).prod nu` is finite.

Thus the new theorem packages the source construction and the explicit p.13
product-family adapted lower bound, but deliberately leaves residual
positivity, residual negative-power integrability, and density bounds as
inputs on the returned `source`.

## Lean Statement Shape

The Lean theorem is:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_measurable_localSource_forall_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_multiEdgeProductCoordinateEdgeFamily_selfBase
```

It returns:

- the local source `source` and open neighborhood `sourceU`;
- positive `R` and `c`, with `R <= Rmax`;
- measurability, basepoint membership, source-stratum inclusion, source-rank
  conclusions, and the `nhdsWithin` equality;
- a continuation which, for any supplied `mu`, additive Haar `nu`, density,
  `t`, and density bound `C`, proves the finite `lossDLN` local integral from
  the remaining residual and density hypotheses on `source`.

## Nonclaims

No signed-box chart, source image/coverage theorem, weighted pushforward,
Jacobian/source-density identity, prior-density construction, residual
positivity proof, residual negative-power integrability proof,
residual/source-density monomial-unit identity, normal-crossing theorem,
pole-order computation, or RLCT statement is proved.
