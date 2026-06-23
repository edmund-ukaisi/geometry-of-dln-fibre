# Reproduction - Chart-certificate unit multiplication

Date: 2026-06-23.

Status: reproduced and formalised as A0 chart-certificate algebra.

## Source Boundary

Aoyagi PDF pp. 5-6 uses normal-crossing local coordinates in which the loss
and Jacobian/prior contribution have monomial forms with exponents `k_j` and
`h_j`, and the finite RLCT arithmetic depends only on

```text
(h_j + 1) / (2 k_j)
```

for coordinates with `k_j > 0`.

The printed display suppresses analytic unit factors.  The Lean chart
certificate spine records them explicitly:

```text
K(pi_c(u)) = U_K(c,u) * prod_j z_j^(2 k_cj)
J(c,u)     = U_J(c,u) * prod_j z_j^(h_cj).
```

This slice is only the elementary algebra saying that multiplying either
display by an already supplied unit changes the unit field and leaves all
exponent arrays unchanged.  It is not a construction of those analytic units.

## Certificate Operation

Let `C` be a supplied chart certificate.  Suppose we are given new functions
`K'` and `J'`, together with chartwise factors `A(c,u)` and `B(c,u)` such that

```text
K'(pi_c(u)) = A(c,u) * K(pi_c(u)),
J'(c,u)     = B(c,u) * J(c,u),
```

and suppose each `A(c,u)` and `B(c,u)` is a unit.

Define a new certificate with the same chart point types, chart maps,
coordinates, and exponent arrays:

```text
k'_cj = k_cj,
h'_cj = h_cj.
```

The new unit fields are

```text
U'_K(c,u) = A(c,u) * U_K(c,u),
U'_J(c,u) = B(c,u) * U_J(c,u).
```

Since the product of two units is a unit, the new unit fields still satisfy
the algebraic unit requirement in the chart-certificate spine.

## Monomial Check

For the loss:

```text
K'(pi_c(u))
  = A(c,u) * K(pi_c(u))
  = A(c,u) * (U_K(c,u) * prod_j z_j^(2 k_cj))
  = (A(c,u) * U_K(c,u)) * prod_j z_j^(2 k_cj).
```

Thus the loss exponent array is unchanged.

For the Jacobian/prior contribution:

```text
J'(c,u)
  = B(c,u) * J(c,u)
  = B(c,u) * (U_J(c,u) * prod_j z_j^(h_cj))
  = (B(c,u) * U_J(c,u)) * prod_j z_j^(h_cj).
```

Thus the Jacobian/prior exponent array is unchanged.

No coordinate power is absorbed into a unit by this operation unless a caller
separately supplies a unit witness for it.  Divisor monomial shifts such as
`prod_j z_j^(m k_j)` belong to the existing exponent-shift operation, not to
the intended use of this unit-only transformer.

## Exponent Projection

Forgetting chart-level fields gives exactly the original finite exponent data:

```text
(C.unitMultiply ...).exponentData = C.exponentData.
```

Consequently the finite values are preserved:

```text
(C.unitMultiply ...).exponentData.exponentMinimum
  = C.exponentData.exponentMinimum

(C.unitMultiply ...).exponentData.exponentOrder
  = C.exponentData.exponentOrder.
```

## Lean Names

Expected names:

```text
AoyagiNormalCrossingChartCertificate.unitMultiply
AoyagiNormalCrossingChartCertificate.unitMultiply_lossExp
AoyagiNormalCrossingChartCertificate.unitMultiply_jacobianPriorExp
AoyagiNormalCrossingChartCertificate.exponentData_unitMultiply
AoyagiNormalCrossingChartCertificate.exponentData_exponentMinimum_unitMultiply
AoyagiNormalCrossingChartCertificate.exponentData_exponentOrder_unitMultiply
```

## Nonclaims

This does not construct chart neighborhoods, prove chart coverage, prove
analytic nonvanishing, compute a volume form, prove a Jacobian theorem, prove
regular-coordinate additivity, produce a global normal-crossing certificate,
prove pole order, or extract an RLCT.  It is certificate algebra on an already
supplied chart-certificate spine.

## Kill Conditions

- A coordinate monomial factor is treated as a unit without a supplied unit
  witness.
- The exponent arrays are changed by this operation.
- The operation is used as a substitute for proving analytic nonvanishing or
  chart production.
- The operation is used to invoke the extraction theorem without a separately
  supplied extraction hypothesis for a genuine chart certificate.
