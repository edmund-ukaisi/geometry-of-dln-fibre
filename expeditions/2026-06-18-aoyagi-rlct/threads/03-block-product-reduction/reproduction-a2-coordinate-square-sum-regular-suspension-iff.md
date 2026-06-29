# Reproduction - A2 coordinate-square-sum regular-suspension iff

Date: 2026-06-29.

Status: pen-and-paper reproduced; Lean formalised for the coordinate
square-sum model.

## Source Anchor

Aoyagi PDF p. 13 separates the displayed product-difference block into
regular variables and residual variables.  After the elementary square-sum
comparison, the local model is

```text
G(x,u) = a(x) + ||u||^2,
```

where `u` is the regular coordinate vector and `a(x)` is the residual
square-sum.

The previous reverse threshold-shift theorem proved the model statement for an
arbitrary real-valued base function `a`.  The present step specialises

```text
a(x) = aoyagiCoordinateSquareSum (b x)
```

and, for residual matrices,

```text
a(x) =
  aoyagiCoordinateSquareSum
    (AoyagiResidualBlockCoordinateIndex.value (D x)).
```

## Calculation

Let `E` be the finite-dimensional regular coordinate space and let
`d = finrank_R(E)`.  The generic model theorem says that, for `R > 0`,
`t > 0`, a Borel measurable structure on `E`, and an additive Haar measure on
`E` with the `SFinite` instance used by Lean's product-integral API, and

```text
AEMeasurable a mu,
a(x) > 0 a.e.,
a(x) <= R^2 a.e.,
```

we have

```text
int^-_(x,u) 1_{ball(0,R)}(u)
  ofReal((a(x)+||u||^2)^(-(t+d/2))) d(mu.prod nu) < infinity

iff

int^-_x ofReal(a(x)^(-t)) dmu < infinity.
```

Substituting the finite coordinate square-sum for `a` changes no analytic
argument.  The reverse direction still uses the same lower fiber ball
`ball(0,sqrt(a(x)))`; therefore positivity and local boundedness become

```text
0 < aoyagiCoordinateSquareSum (b x)       a.e.,
aoyagiCoordinateSquareSum (b x) <= R^2    a.e.
```

and measurability becomes

```text
AEMeasurable (fun x => aoyagiCoordinateSquareSum (b x)) mu.
```

The residual-block form is only the substitution

```text
b x = AoyagiResidualBlockCoordinateIndex.value (D x).
```

No matrix algebra or loss comparison is used in this step.

## Lean Shape

Lean formalises the coordinate specialization in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionSquareSumIntegrability.lean
```

with:

```text
lintegral_ofReal_residual_power_lt_top_of_coordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top
lintegral_ofReal_coordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_iff_residual_power_lt_top
lintegral_ofReal_residual_power_lt_top_of_residualBlockSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top
lintegral_ofReal_residualBlockSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_iff_residual_power_lt_top
```

The coordinate proofs call the generic model theorems with
`a := fun x => aoyagiCoordinateSquareSum (b x)`.  The residual-block proofs call
the coordinate theorems with
`b := fun x => AoyagiResidualBlockCoordinateIndex.value (D x)`.

Focused build:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionSquareSumIntegrability
```

passed.

## Nonclaims

- No p. 13 analytic chart coverage.
- No source-prior, Jacobian, or density transport.
- No original DLN loss statement.
- No proof that Aoyagi's reduced residual coordinates satisfy the residual
  negative-power integrability input.
- No removal of the local bound `a <= R^2`.
- No pole-order, normal-crossing, or RLCT extraction.
