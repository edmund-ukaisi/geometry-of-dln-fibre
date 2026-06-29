# Reproduction - A2 p.13 regular-coordinate model iff

Date: 2026-06-29.

Status: pen-and-paper checked; Lean formalised for the fixed-base p.13 square
model.

## Source Anchor

Aoyagi PDF p. 13 isolates the regular variables in the product-difference
block as the entries of

```text
C1 - I,  F2,  F3.
```

Their count is

```text
k = r^2 + r(H(1)-r) + r(H(L+1)-r)
  = -r^2 + r(H(1)+H(L+1)).
```

In the fixed-base formalisation, these regular variables are indexed by

```text
AoyagiRegularBlockCoordinateIndex
  (Fin (finrank U0))
  (endpoint complement at Fin.last N)
  (endpoint complement at 0).
```

The existing theorem

```text
regularCoordinateEuclidean_finrank_eq_regularVariableCount
```

identifies the Euclidean dimension of this regular-coordinate space with
`aoyagiTheorem2RegularVariableCount N H r`.

## Model Calculation

Let

```text
a(x) =
  aoyagiCoordinateSquareSum
    (paperEndpointFixedBaseResidualBlockCoordinateMap W B U0 hU0 Cedge x).
```

The coordinate-square-sum threshold-shift iff already proves, for a
finite-dimensional regular coordinate space `E`,

```text
int^-_(x,u) 1_{ball(0,R)}(u)
  ofReal((a(x)+||u||^2)^(-(t+finrank(E)/2))) d(mu.prod nu) < infinity

iff

int^-_x ofReal(a(x)^(-t)) dmu < infinity
```

under the local hypotheses

```text
AEMeasurable a mu,
0 < R,
a(x) > 0 a.e.,
a(x) <= R^2 a.e.,
0 < t,
```

with `[SFinite nu] [nu.IsAddHaarMeasure]`.

For the p.13 regular-coordinate Euclidean space, we substitute the residual
coordinate square-sum above and rewrite

```text
finrank(E) = aoyagiTheorem2RegularVariableCount N H r,
||u||^2 = aoyagiCoordinateSquareSum (fun i => u i).
```

This gives the displayed fixed-base p.13 model:

```text
residualSquareSum(x) + regularCoordinateSquareSum(u)
```

at exponent

```text
t + aoyagiTheorem2RegularVariableCount N H r / 2.
```

The source-data package is used here only to provide the regular-variable
count through `regularCoordinateEuclidean_finrank_eq_regularVariableCount`.
No field of the package supplies chart coverage, loss comparison, or a
measure-transport theorem in this wrapper.

## Lean Shape

Lean formalises the wrapper in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionSquareSumIntegrability.lean
```

as

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.lintegral_ofReal_p13RegularCoordinates_model_lt_top_iff_residual_power_lt_top
```

The proof:

1. defines the regular-coordinate index `rho`;
2. rewrites `finrank (EuclideanSpace R rho)` using the source-data count
   theorem;
3. applies the coordinate-square-sum model iff with
   `b x = paperEndpointFixedBaseResidualBlockCoordinateMap ... x`;
4. rewrites `||u||^2` to the regular coordinate square-sum using
   `EuclideanSpace.real_norm_sq_eq`.

Focused build:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionSquareSumIntegrability
```

passed.

## Nonclaims

- No proof of measurability, positivity, boundedness, or residual
  integrability for the residual square-sum.
- No p.13 analytic chart coverage.
- No source-prior, Jacobian, or density transport.
- No original DLN loss statement.
- No pole-order, normal-crossing, or RLCT extraction.
