# Reproduction - A2 original-loss local integrability for the product family, edge-matrix form

Date: 2026-06-25.

Status: pen-and-paper reproduction before Lean implementation.

## Purpose

The previous product-family original-loss handoff uses global continuity of the
base edge family `CedgeBase`.  The local product-family adapted lower bound
only needs `ContinuousAt CedgeBase x0`; the global continuity was used by the
downstream source-measure theorem to obtain source-stratum and residual
measurability.

This slice keeps those measurability facts explicit by assuming the fixed-base
edge-matrix map is measurable.  It is useful for future chart maps where the
source chart/pushforward theorem may provide measurable coordinates without a
global topological statement.

## Calculation

Let

```text
CedgeProd(x,u)
  = paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
      V Bv U0 hU0 CedgeBase (x,u).
```

Assume:

```text
ContinuousAt CedgeBase x0
CedgeBase x0 = reverseEdge Bv
Measurable (edgeMatrix(CedgeBase x)).
```

The local product-family theorem gives

```text
exists Rprod cprod,
  0 < Rprod, Rprod <= Rmax, 0 < cprod,
  eventually x in sourceStratum,
    forall u in ball(0,Rprod),
      cprod * (residualSquareSum(CedgeBase x) + squareSum(u))
        <= adaptedProductDifferenceSquareSum(CedgeProd(x,u)).
```

The existing measurable-edge original-loss finite-integral theorem consumes
exactly this `hadapted_lower`, the fixed-base edge-matrix measurability, and
the supplied signed-box residual source hypotheses.  Calling it with
`Rmax := Rprod` returns a smaller radius `R <= Rprod`, hence

```text
R <= Rprod <= Rmax.
```

No new estimate is proved; the theorem removes the unnecessary global
continuity hypothesis from the product-family original-loss front end.

## Boundary

This is still not a signed-box chart construction, not a pushforward theorem,
not a residual monomial lower-bound proof, not a density/Jacobian computation,
not a normal-crossing certificate, not a pole-order theorem, and not an RLCT
extraction.
