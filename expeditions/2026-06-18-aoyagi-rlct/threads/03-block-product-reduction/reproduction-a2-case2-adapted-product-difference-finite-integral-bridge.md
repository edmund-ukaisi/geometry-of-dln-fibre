# A2 Case 2 adapted product-difference finite-integral bridge

## Claim

For the endpoint-transported explicit continuing Case 2 selected-entry source
chart, the source-stratum finite-integral theorem can be applied with the loss
equal to Aoyagi's fixed-base adapted p.13 product-difference square-sum.  The
regular-plus-residual lower comparison is then not an external hypothesis: it
is produced by the existing source-coordinate product-reduction theorem.

The conclusion is a one-sided finite-integral statement over

```text
(mu.restrict (U inter sourceStratum)).prod nu
```

with exponent

```text
-(t + aoyagiTheorem2RegularVariableCount 2 H r / 2).
```

## Source Calculation

Aoyagi Lemma 2, PDF pp. 10-11, gives the elementary block elimination

```text
F2 = -A1^{-1} A2,
F3 = -A3 A1^{-1},
C4 = -A3 A1^{-1} A2 + A4.
```

Aoyagi Theorem 3, PDF pp. 11-13, iterates this block elimination through the
product.  At p. 13 the product difference is displayed, after multiplication
by regular block triangular matrices, as

```text
[ C1 - Er       -F2
  -F3      prod_s C^(s) - F3 F2 ].
```

Thus the finite p.13 square-sum contains:

- the regular block `C1 - Er`;
- the regular block `F2`;
- the regular block `F3`;
- the reduced residual block `prod_s C^(s) - F3 F2`.

The regular-suspension coordinate theorem already formalises the local
quantitative version of this display.  For the self-base product-coordinate
family

```text
CedgeProd =
  paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
    W2 B2 U0 hU0 (fun E => E),
```

there exist `R > 0` and `c > 0` such that, eventually on the source-rank
stratum and for `u` in the regular-coordinate ball,

```text
c * (residualSq(x) + regularSq(u))
  <= paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
       W2 B2 U0 hU0 CedgeProd (x, u).
```

This is precisely the lower-comparison hypothesis of the Case 2
source-stratum finite-integral socket when `loss` is specialised to the adapted
product-difference square-sum.

## Radius Bookkeeping

The density is assumed continuous and positive at `(base, 0)`.  The standard
density-shrink lemma first gives a radius `Rden <= Rmax` and a finite bound
`C` with source-stratum eventual bounds

```text
0 <= density(x, u),
density(x, u) <= C
```

on the ball of radius `Rden`.

The adapted lower-bound theorem is then applied with `Rmax = Rden`, producing
`R <= Rden` and `c > 0`.  The density bounds are restricted from `Rden` to `R`,
so all hypotheses fed to the finite-integral socket use the same final radius
`R`.

## Lean Route

Apply

```text
exists_pos_radius_le_eventually_nhdsWithin_density_bounds_of_continuousAt_pos
```

on the source-rank stratum for the identity edge-family source map.

Then apply

```text
exists_pos_radius_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase_nhdsWithin_source
```

with `V = W2`, `Bv = B2`, `x0 = base`, `CedgeBase = fun E => E`, and the
density-shrink radius as `Rmax`.

Finally call the existing Case 2 source-stratum chart-produced theorem

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure
```

with

```text
loss =
  paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
    W2 B2 U0 hU0 CedgeProd.
```

## Boundary

This proves a finite-integral handoff for the chart-produced selected-entry
source measure and the adapted p.13 product-difference square-sum.  It does
not identify this adapted square-sum with an original statistical loss, prove a
reverse implication, prove source-rank support, choose signed-box radii, prove
selected-entry source/image equality, transport an external source prior or
Jacobian, construct normal crossings, compute pole order, or extract RLCT.

## Kill Conditions

- The product-coordinate family used by the lower-bound theorem is not
  definitionally the `CedgeProd` used in the finite-integral conclusion.
- The lower-bound radius and density-bound radius are not reconciled before
  invoking the finite-integral socket.
- The theorem silently keeps a supplied lower comparison for the adapted
  product-difference square-sum.
- The result is named as an original-loss or RLCT theorem rather than as a
  chart-produced adapted-product-difference finite-integral bridge.
