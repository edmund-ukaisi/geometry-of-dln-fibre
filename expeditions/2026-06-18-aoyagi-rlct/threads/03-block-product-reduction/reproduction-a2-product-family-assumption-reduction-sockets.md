# Reproduction - A2 product-family assumption-reduction sockets

Date: 2026-06-25.

Status: pen-and-paper reproduction for finite-coordinate bridges behind the
product-coordinate adapted lower-bound socket.

## Source Boundary

Aoyagi p.13 displays the product-difference block

```text
[ C1 - E_r              -F2
  -F3        prod_s C^(s) - F3 F2 ].
```

The cleaned coordinate family is

```text
X = C1 - E_r,    F2,    F3,    D = prod_s C^(s),
```

while the literal displayed block uses the corrected residual
`D - F3 F2`.  The independent regular variables are the entries of
`X`, `F2`, and `F3`.

This slice does not construct the analytic product chart.  It records what can
be proved once a supplied product family has the expected finite coordinate
properties.

## Cleaned-To-Literal From `F2/F3` Smallness

For a fixed-base edge family, define

```text
F23(Cedge,z) = squareSum(F2(Cedge,z)) + squareSum(F3(Cedge,z)).
```

The already-formalised finite estimate says that if `F23(Cedge,z) <= 1`, then

```text
squareSum(cleaned(Cedge,z)) <= 2 * squareSum(literal(Cedge,z)).
```

For a product family `CedgeProd(x,u)`, the source-filter form is obtained by
applying this pointwise estimate after the supplied eventual bound

```text
F23(CedgeProd(x,u)) <= 1
```

on the source filter, uniformly for every `u` in the regular ball.  This is an
`nhdsWithin`-eventual statement in the base variable plus a ball quantifier in
the regular variable; it is not a product-neighborhood or product-chart
theorem.

## Product Shape From Component Identities

The cleaned product-difference coordinate map splits as a disjoint sum:

```text
productDifference(Cedge,z)
  = regularBlock(Cedge,z) ⊕ residualBlock(Cedge,z).
```

Therefore

```text
squareSum(productDifference(Cedge,z))
  = squareSum(regularBlock(Cedge,z))
    + squareSum(residualBlock(Cedge,z)).
```

For a product family it is enough to assume the two component identities

```text
regularBlock(CedgeProd(x,u)) = u,
residualBlock(CedgeProd(x,u)) = residualBlock(CedgeBase x).
```

Then the cleaned square-sum has the socket shape

```text
squareSum(productDifference(CedgeProd(x,u)))
  = squareSum(residualBlock(CedgeBase x)) + squareSum(u).
```

The final equality only swaps the two summands.

## Combined Socket

The previous product-coordinate adapted lower-bound socket assumed both the
square-sum shape and cleaned-to-literal comparison directly.  This slice adds
a wrapper where the cleaned-to-literal comparison is derived from supplied
`F2/F3` smallness.  The product-coordinate shape can now also be supplied via
component identities, using the shape bridge above.

There is also a fully composed finite-coordinate wrapper.  Its assumptions are
the component identities, product-family `F2/F3` smallness, the
product-reduction certificates, a positive multiplier constant `0 < Kmul`, and
the uniform triangular multiplier bound with that `Kmul`.  It first derives
the square-sum shape from the component identities, derives the
cleaned-to-literal comparison from `F2/F3` smallness, and then calls the
adapted lower-bound socket.  Thus downstream callers no longer need to build
either `hshape` or `hclean_le_literal` manually when they have the concrete
coordinate behavior.

## Radius-Derived `F2/F3` Smallness

The remaining `F2/F3` smallness input is also finite-coordinate when the
product-family regular coordinates are literally the Euclidean parameter `u`.
Let `rho` be the regular-coordinate index

```text
rho = AoyagiRegularBlockCoordinateIndex(iota, mu, nu).
```

For any regular-coordinate function `coord : rho -> R`, the `F2` and `F3`
sub-square-sums are bounded by the full regular-coordinate square-sum:

```text
squareSum(F2 coord) + squareSum(F3 coord)
  <= squareSum(coord).
```

This is only the decomposition

```text
squareSum(coord)
  = squareSum(Ctop coord) + squareSum(F2 coord) + squareSum(F3 coord)
```

and nonnegativity of the omitted `Ctop` square-sum.

If

```text
regularBlock(CedgeProd(x,u)) = u
```

pointwise, then

```text
F23(CedgeProd(x,u)) <= squareSum(u).
```

If also `u` lies in the Euclidean ball of radius `Rmax` and `Rmax <= 1`, then

```text
squareSum(u) = ||u||^2 <= 1.
```

The ball membership gives `||u|| < Rmax`; composing with `Rmax <= 1` gives
`||u|| <= 1`, and squaring is valid because norms are nonnegative.  Thus

```text
F23(CedgeProd(x,u)) <= 1.
```

No separate `0 < Rmax` is needed for this finite implication.  The final
adapted lower-bound wrapper still keeps `0 < Rmax`, as the existing socket and
later local-measure APIs carry a positive-radius/nonvacuity condition.

The strongest composed finite-coordinate wrapper now assumes the regular and
residual component identities, `0 < Rmax`, `Rmax <= 1`, the product-reduction
certificates, `0 < Kmul`, and the uniform triangular multiplier bound with
that `Kmul`.  It derives both the product-coordinate square-sum shape and the
cleaned-to-literal comparison before invoking the adapted lower-bound socket.

## Boundaries

No `CedgeProd` is constructed.  No analytic product coordinates, source
coverage, signed-box pushforward, density/Jacobian transport, normal
crossings, pole order, or RLCT extraction is proved.
