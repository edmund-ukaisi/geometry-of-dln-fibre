# Reproduction - A2 p.13 regular-coordinate bounded-density adapter

Date: 2026-06-25.

Status: pen-and-paper reproduction and Lean formalisation for a source-facing
finite-side adapter.

## Source Motivation

On Aoyagi p. 13, after Theorem 3, the displayed centered product has regular
blocks `C1-Er`, `F2`, `F3` and lower-right literal block
`prod_s C^(s) - F3 F2`.  The cleaned residual block `prod_s C^(s)` enters
after the separately proved finite square-sum comparison.  The displayed
regular contribution is one half of the number of scalar regular block
coordinates:

```text
r^2 + r*(H(L+1)-r) + (H(1)-r)*r.
```

Earlier Lean work proved the abstract product-measure finite-side theorem with
a regular Euclidean factor `E` and exponent shift `finrank(E)/2`.  This slice
specialises that theorem to the actual p. 13 regular coordinate index carried
by `PaperEndpointFixedBaseRegularCoordinateSourceData`.

## Derivation

Let

```text
rho =
  AoyagiRegularBlockCoordinateIndex
    (Fin (finrank U0))
    endpointComplement(last)
    endpointComplement(0).
```

The regular fiber is the Euclidean coordinate space

```text
E = EuclideanSpace R rho.
```

The source-data package already proves

```text
card(rho) = aoyagiTheorem2RegularVariableCount N H r.
```

Since `finrank_R(EuclideanSpace R rho)=card(rho)`, we get

```text
finrank_R(E) = aoyagiTheorem2RegularVariableCount N H r.
```

For `u : E`, Mathlib gives

```text
||u||^2 = sum_i u_i^2.
```

This is exactly the repo's `aoyagiCoordinateSquareSum (fun i => u i)`.
Therefore a supplied product-measure lower bound in p.13 coordinate language,

```text
c * (residualSquareSum(x) + regularSquareSum(u)) <= loss(x,u),
```

becomes the lower bound expected by the generic bounded-density theorem:

```text
c * (residualSquareSum(x) + ||u||^2) <= loss(x,u).
```

Together with the supplied hypotheses

```text
residualSquareSum(x) > 0 a.e.,
int^- x, ofReal(residualSquareSum(x)^(-t)) < infinity,
0 <= density(x,u) <= C
```

on the regular ball, the generic bounded-density wrapper proves finite
lower-integrability at exponent

```text
t + finrank_R(E)/2.
```

Rewriting `finrank_R(E)` by the source-data count gives the p.13-facing
exponent

```text
t + aoyagiTheorem2RegularVariableCount N H r / 2.
```

## Lean Shape

Lean proves this in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionSquareSumIntegrability.lean
```

with names

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.regularCoordinateEuclidean_finrank_eq_regularVariableCount
PaperEndpointFixedBaseRegularCoordinateSourceData.lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residual_power_lt_top
```

The adapter includes `R>0` as a source-facing local-ball hypothesis.  The
underlying finite-side inequality is still true for an empty regular ball, but
Aoyagi's local chart use is a positive-radius statement.

## Boundary

This theorem does not prove:

- the p.13 analytic product chart;
- source-filter facts imply product-measure a.e. hypotheses;
- comparison between the original DLN loss and the p.13 literal square-sum;
- the lower-loss bound used by the adapter;
- Jacobian/prior density transport or boundedness;
- residual positivity or residual negative-power integrability;
- endpoint/divergence, threshold equality, pole order, normal crossings, or
  RLCT extraction.
