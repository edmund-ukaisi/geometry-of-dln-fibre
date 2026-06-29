# A2 Case 2 original-loss finite-integral bridge

## Claim

For the endpoint-transported explicit continuing Case 2 selected-entry source
chart, the source-stratum finite-integral theorem can be applied with the loss
equal to the original endpoint square-Frobenius `lossDLN` written in supplied
endpoint bases.  The source measure is still the chart-produced selected-entry
pushforward measure, and the edge family in the loss is the chart-produced
regular product-coordinate family.

The conclusion is a one-sided finite-integral statement over

```text
(mu.restrict (U inter sourceStratum)).prod nu
```

with exponent

```text
-(t + aoyagiTheorem2RegularVariableCount 2 H r / 2).
```

## Source Calculation

Aoyagi Lemma 2, PDF pp. 10-11, performs block Gaussian elimination on a
full-rank block.  Aoyagi Theorem 3, PDF pp. 11-13, iterates that elimination
through the product and obtains, on p. 13, the transformed product-difference
display

```text
[ C1 - Er       -F2
  -F3      prod_s C^(s) - F3 F2 ].
```

The previously banked adapted-product-difference bridge formalises the local
quantitative consequence of this display for the self-base product-coordinate
family

```text
CedgeProd =
  paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
    W2 B2 U0 hU0 (fun E => E).
```

After shrinking the regular-coordinate radius, there is `cprod > 0` such that
eventually on the source-rank stratum and for `u` in the regular ball,

```text
cprod * (residualSq(x) + regularSq(u))
  <= paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
       W2 B2 U0 hU0 CedgeProd (x, u).
```

The bridge to the original endpoint loss is finite linear algebra.  For any
fixed endpoint bases

```text
b : forall j, Module.Basis (Fin (d j)) R (reverseVertex W2 j),
```

the endpoint-basis comparison gives `c0 > 0` such that for every product
coordinate point `(x,u)`,

```text
c0 * paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss
       W2 B2 U0 hU0 CedgeProd (x, u)
  <= lossDLN d target
       (chainMapMatrixTuple b
         (fun p => CedgeProd (x,u) p)).
```

The fixed adapted Frobenius loss is equal to the adapted product-difference
square-sum:

```text
paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss
  = paperEndpointFixedBaseAdaptedProductDifferenceSquareSum.
```

Multiplying the adapted lower bound by `c0` gives the lower comparison needed
by the generic Case 2 source-stratum finite-integral socket:

```text
(c0 * cprod) * (residualSq(x) + regularSq(u))
  <= lossDLN d target
       (chainMapMatrixTuple b
         (fun p => CedgeProd (x,u) p)).
```

Here

```text
target =
  LinearMap.toMatrix (b 0) (b (Fin.last 2))
    (chainMap (reverseVertex W2) (reverseEdge W2 B2)
      0 (Fin.last 2) (Fin.zero_le (Fin.last 2))).
```

## Radius Bookkeeping

As in the adapted bridge, the density is assumed continuous and positive at
`(base, 0)`.  First shrink from `Rmax` to a density radius `Rden <= Rmax`,
obtaining source-stratum eventual bounds

```text
0 <= density(x, u),
density(x, u) <= C
```

on the regular ball of radius `Rden`.

Then apply the product-coordinate adapted lower-bound theorem with
`Rmax = Rden`, obtaining the final radius `R <= Rden` and `cprod > 0`.
The density bounds are restricted from `Rden` to `R`.  The endpoint-basis
comparison is pointwise and does not shrink the radius.

The finite-integral socket is then invoked at the final radius `R` with
regular lower constant `c0 * cprod`.

## Lean Route

1. Add the endpoint comparison dependency to the Case 2 retained-passive
   local Jacobian-measure bridge.
2. In the theorem, define `CedgeProd`, `target`, and `originalLoss`.
3. Use

   ```text
   exists_pos_const_forall_adaptedProductDifferenceFrobeniusLoss_le_lossDLN_chainMapMatrixTuple
   ```

   to obtain `c0 > 0`.
4. Use the same density shrink and source-coordinate adapted lower-bound
   theorem as the adapted-product-difference bridge.
5. Rewrite the adapted Frobenius loss to the adapted square-sum using

   ```text
   paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss_eq_squareSum
   ```

   and compose the two inequalities into
   `(c0 * cprod) * (residualSq + regularSq) <= originalLoss`.
6. Call

   ```text
   exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure
   ```

   with `loss = originalLoss`.

## Boundary

This proves finite integrability for the endpoint-basis original
square-Frobenius `lossDLN` evaluated on the chart-produced product-coordinate
edge family.  It does not prove a reverse implication, source-rank support,
selected-entry source/image equality, transport of an external source prior,
Jacobian comparison for such a prior, normal crossings, pole order, or RLCT.

## Kill Conditions

- The endpoint comparison is applied to a different `CedgeProd` from the one
  used in the finite-integral conclusion.
- The adapted Frobenius-to-square-sum rewrite is missing, so the comparison
  does not compose with the source-coordinate lower bound.
- The lower-bound constant is not kept positive after multiplication.
- The theorem is named or described as source-prior/Jacobian transport rather
  than as endpoint-basis original-loss finite integrability.
