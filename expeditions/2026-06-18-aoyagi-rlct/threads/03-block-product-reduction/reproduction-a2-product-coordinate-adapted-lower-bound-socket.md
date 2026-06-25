# Reproduction - A2 product-coordinate adapted lower-bound socket

Date: 2026-06-25.

Status: pen-and-paper reproduction for a conditional finite/topological socket.

## Source Boundary

Aoyagi p.13 displays the product-difference block

```text
[ Ctop - I      -F2
  -F3        D - F3 F2 ]
```

and treats `Ctop-I`, `F2`, and `F3` as regular variables added to the reduced
residual product `D`.  The analytic construction of a product chart whose
independent fiber coordinate is exactly those regular variables is not printed
there.  This socket therefore assumes the product-coordinate shape explicitly.

## Calculation

Fix a base source family `CedgeBase : alpha -> edgeFamily` and an independent
product family

```text
CedgeProd : alpha x EuclideanSpace rho -> edgeFamily.
```

Let

```text
S(x,u) = productDifferenceCoordinateSquareSum(CedgeProd(x,u)),
L(x,u) = literalProductDifferenceCoordinateSquareSum(CedgeProd(x,u)),
A(x,u) = adaptedProductDifferenceSquareSum(CedgeProd(x,u)).
```

The supplied product-coordinate shape is the square-sum identity

```text
S(x,u) = residualSquareSumBase(x) + squareSum(u).
```

The socket assumes the cleaned-to-literal p.13 comparison directly:

```text
S(x,u) <= 2 * L(x,u).
```

In a later product-family constructor this comparison should be proved from
`F2/F3` smallness for `CedgeProd`, but this socket does not expose or check
that smallness hypothesis itself.

The supplied product-reduction certificate and triangular multiplier bound
`multiplierSquareSumProduct <= Kmul` give, for `cLit = Kmul^{-1}`,

```text
cLit * L(x,u) <= A(x,u).
```

Combining the two estimates gives

```text
(cLit/2) * (residualSquareSumBase(x) + squareSum(u))
  <= A(x,u).
```

Since `Kmul > 0`, the final constant `cLit/2` is positive.

The regular radius is also assumed positive.  This is not needed for the scalar
inequality algebra, but it prevents the conclusion from being only an
empty-ball statement.

## Lean Shape

The theorem should live in `RegularSuspensionCoordinates.lean` under
`PaperEndpointFixedBaseRegularCoordinateSourceData`:

```text
exists_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_of_productCoordinateShape_nhdsWithin_source
```

Its conclusion is the same `hadapted_lower` shape consumed by
`OriginalLossLocalMeasure.lean`.

## Boundaries

This theorem does not construct `CedgeProd`, prove source coverage, prove that
`u` is an analytic coordinate, prove the signed-box pushforward, transport
density/Jacobian factors, produce normal crossings, compute pole order, or
extract an RLCT.
