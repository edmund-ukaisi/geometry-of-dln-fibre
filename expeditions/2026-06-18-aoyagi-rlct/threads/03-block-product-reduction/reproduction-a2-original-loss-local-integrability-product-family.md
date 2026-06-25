# Reproduction - A2 original-loss local integrability for the product family

Date: 2026-06-25.

Status: pen-and-paper reproduction before Lean implementation.

## Source Boundary

This slice composes two already reproduced elementary p.13 ingredients:

- the explicit self-base multi-edge product-coordinate family gives a local
  adapted product-difference lower bound;
- the original square-Frobenius `lossDLN` dominates the adapted endpoint
  square-sum up to a positive basis-dependent constant.

It is still local finite-integral plumbing.  The signed-box source chart,
weighted pushforward identity, residual monomial lower bound, source-density
monomial bound, and transported density positivity remain supplied.

## Calculation

Fix a multi-edge chain `N = M + 2`.  Let

```text
CedgeProd(x,u)
  = paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
      V Bv U0 hU0 CedgeBase (x,u).
```

For a continuous self-based source family

```text
CedgeBase x0 = reverseEdge Bv,
```

the product-family lower-bound theorem gives a radius `Rprod <= Rmax` and a
constant `cprod > 0` such that eventually on the source-rank stratum and
uniformly for `u in ball(0,Rprod)`,

```text
cprod * (squareSum(residual(CedgeBase x)) + squareSum(u))
  <= adaptedProductDifferenceSquareSum(CedgeProd(x,u)).
```

The endpoint basis comparison gives a second positive constant `c0 > 0` with

```text
c0 * adaptedProductDifferenceSquareSum(CedgeProd(x,u))
  <= lossDLN d target (chainMapMatrixTuple b (CedgeProd(x,u))).
```

Multiplying the two inequalities gives the loss lower bound required by the
existing p.13 local finite-integral theorem.  Since the product-family theorem
has already shrunk the radius under `Rmax`, the local-integrability theorem is
called with outer radius `Rprod`; its output radius `R` then satisfies

```text
R <= Rprod <= Rmax.
```

## Resulting Integrability Shape

Under the supplied signed-box residual source hypotheses and a positive
continuous transported density factor at `(x0,0)`, there are `R,C,U` with

```text
0 < R,  R <= Rmax,  0 <= C,  U open,  x0 in U
```

such that

```text
integral over (mu.restrict (U inter sourceStratum)).prod nu of
  indicator_ball_R(u)
  * ofReal((lossDLN(CedgeProd(x,u)))^(-(t + regularCount/2)) * density(x,u))
is finite.
```

## Boundary

This removes only the explicit product-coordinate adapted-lower-bound
hypothesis from the original-loss local finite-integral front end.  It does
not construct the signed-box source chart, prove the pushforward identity,
derive the residual monomial lower bound, compute a Jacobian/density factor,
produce normal crossings, compute pole order, or extract an RLCT.
