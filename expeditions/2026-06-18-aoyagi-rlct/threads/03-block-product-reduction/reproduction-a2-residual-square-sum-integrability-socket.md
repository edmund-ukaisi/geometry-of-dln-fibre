# Reproduction - A2 residual square-sum integrability socket

Date: 2026-06-25.

Status: pen-and-paper reproduction and Lean formalisation for a square-sum
specialisation of the residual-power threshold-shift bridge.

## Scope

Aoyagi's p. 13 residual model is expressed by a finite family of scalar
residual coordinates.  The repository uses

```text
aoyagiCoordinateSquareSum b = sum_i b_i^2
```

for such finite coordinate families, and

```text
AoyagiResidualBlockCoordinateIndex.value D
```

for the entries of a residual matrix block `D`.

This slice does not prove positivity or finite residual negative-power
integrability.  It only specialises the already-proved analytic product
theorem to the square-sum base parameter

```text
a(x) = aoyagiCoordinateSquareSum (b x)
```

and then to a residual matrix block.

## Calculation

The residual-power threshold-shift bridge proves:

```text
a(x)>0 a.e.,
t>0,
∫⁻ x, ofReal(a(x)^(-t)) dmu < infinity
```

imply finite product lower integral for

```text
(a(x)+||u||^2)^(-(t+d/2))
```

over `alpha x ball(0,R)`, where `d=finrank_R(E)`.

Substituting

```text
a(x) = aoyagiCoordinateSquareSum (b x)
```

gives the coordinate-square-sum theorem.  Substituting further

```text
b(x) = AoyagiResidualBlockCoordinateIndex.value (D x)
```

gives the residual-block-square-sum theorem.

No analytic or geometric information about `b` or `D` is used.  All required
properties remain hypotheses:

```text
0 < aoyagiCoordinateSquareSum (b x)   for mu-a.e. x,
∫⁻ x, ofReal((aoyagiCoordinateSquareSum (b x))^(-t)) dmu < infinity.
```

## Lean Shape

Lean proves the following in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionSquareSumIntegrability.lean
```

```text
lintegral_ofReal_coordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_le_residual_power_scale
lintegral_ofReal_coordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_residual_power_lt_top
lintegral_ofReal_residualBlockSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_residual_power_lt_top
```

The file imports both the coordinate square-sum definitions and the analytic
integrability theorem, leaving `RegularSuspensionIntegrability.lean`
independent of the coordinate layer.

## Role In The Aoyagi Route

This is a naming and interface socket for Aoyagi p. 13: later work can try to
prove the a.e. positivity and residual negative-power lower-integral
hypotheses for the actual reduced residual coordinate map, then feed them
directly into the residual-block theorem.

## Nonclaims

- No proof that Aoyagi's reduced residual coordinates satisfy positivity.
- No proof of residual negative-power integrability.
- No theorem for a positive-measure zero set of the residual square-sum.
- No endpoint theorem, divergent-side theorem, or threshold equality.
- No bounded-density/prior transport theorem.
- No Aoyagi p.13 analytic chart/Jacobian construction.
- No normal-crossing construction, pole order, or RLCT extraction.
