# A2 with-following readback product-residual prior transfer

Date: 2026-07-03.

This note records the bookkeeping step that specializes the arbitrary product
finite-integral transfer to the with-following readback product residual.

## Calculation

The existing original-prior readback theorem returns a continuation of the
form

```text
for every beta, nu, F,
  integral over theta x beta of F(sourceChart theta, beta) finite
  implies integral over edgeFamily x beta of F finite.
```

To remove the dummy factor, take the one-point type at the continuation's
universe and put a Dirac mass on its unique point.  For any s-finite left
measure,

```text
integral over alpha x {*} of f(a, *) with respect to mu.prod (dirac *)
  = integral over alpha of f(a, *) with respect to mu.
```

This is the lemma now named

```text
lintegral_prod_dirac_right
```

and the corresponding one-factor specialization of an arbitrary product
transfer is

```text
lintegral_lt_top_of_forall_prod_transfer_unit
```

Applying this to

```text
f E =
  ofReal ((aoyagiCoordinateSquareSum
    (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
      W2 B2 n hS hcont hnext hU0 eNext e E)) ^ (-t))
```

gives the named Aoyagi specialization

```text
lintegral_case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidual_lt_top_of_forall_prod_transfer
```

If the local source chart satisfies the left-inverse identity on a measurable
set `V`,

```text
readback (sourceChart z) = z    for z in V,
```

then the previously proved square-sum identity rewrites the source pullback of
the readback residual to the source-side product residual.  Therefore a finite
source integral for

```text
case2PassiveThetaWithFollowingFactorProductResidualReadout
```

gives the source-integral hypothesis needed by the preceding product-transfer
specialization.  This adapter is now named

```text
lintegral_case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidual_lt_top_of_forall_prod_transfer_of_leftInverse
```

## Boundary

The source-side measurability and finite integral are explicit hypotheses.
The left-inverse adapter uses only `lintegral_congr_ae` and a measurable `V`.
This proves no source-side product-residual integrability, no endpoint-density
theorem, no determinant-Haar transport, no original-prior density bound, no
normal crossings, no pole order, and no RLCT extraction.  Its role is to
consume the product-transfer continuation already produced by the prior
readback package.
