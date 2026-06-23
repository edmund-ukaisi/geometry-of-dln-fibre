# Reproduction - Chart-certificate Jacobian-prior loss shift

Date: 2026-06-23.

Status: A0 chart-certificate algebra.

## Source Boundary

Aoyagi PDF pp. 5-6 uses the finite normal-crossing exponents through ratios

```text
(h_j + 1) / (2 k_j)
```

for coordinates with `k_j > 0`.  The earlier A0 finite shift slice proved that
replacing `h_j` by `h_j + m k_j` shifts each active ratio, and hence the finite
minimum, by `m/2`.

Aoyagi PDF p. 13 motivates this socket through the regular variables after the
product reduction.  This reproduction does not prove that those regular
variables have been constructed.  It only lifts the finite exponent-array shift
to the chart-certificate spine by changing the recorded Jacobian/prior monomial.

## Certificate Operation

Let `C` be a supplied chart certificate.  On a chart point write

```text
z_j = C.coord c u j
k_j = C.lossExp c j
h_j = C.jacobianPriorExp c j
```

The certificate already has a Jacobian/prior monomial identity

```text
J(c,u) = U(c,u) * prod_j z_j ^ h_j.
```

Define the shifted certificate by leaving the chart point type, chart map,
coordinates, loss, loss unit, and Jacobian/prior unit unchanged, and replacing

```text
J(c,u)
```

by

```text
J(c,u) * prod_j z_j ^ (m k_j).
```

The new Jacobian/prior exponent array is

```text
h'_j = h_j + m k_j.
```

## Monomial Check

Substitute the old monomial identity:

```text
J(c,u) * prod_j z_j^(m k_j)
  = (U(c,u) * prod_j z_j^h_j) * prod_j z_j^(m k_j).
```

By associativity and the finite product rule,

```text
(U * prod_j z_j^h_j) * prod_j z_j^(m k_j)
  = U * prod_j (z_j^h_j * z_j^(m k_j)).
```

For every `j`,

```text
z_j^h_j * z_j^(m k_j) = z_j^(h_j + m k_j).
```

Therefore the shifted certificate has

```text
J'(c,u) = U(c,u) * prod_j z_j^(h_j + m k_j).
```

The loss monomial identity and both unit witnesses are unchanged.

## Exponent Projection

Forgetting the chart-level fields gives exactly the previous finite
exponent-array operation:

```text
(C.jacobianPriorLossShift m).exponentData
  = C.exponentData.jacobianPriorLossShift m.
```

Consequently the already proved finite exponent-array theorems apply:

```text
(C.jacobianPriorLossShift m).exponentData.exponentMinimum
  = C.exponentData.exponentMinimum + m/2

(C.jacobianPriorLossShift m).exponentData.exponentOrder
  = C.exponentData.exponentOrder.
```

## Lean Names

```text
AoyagiNormalCrossingChartCertificate.jacobianPriorLossShift
AoyagiNormalCrossingChartCertificate.jacobianPriorLossShift_lossExp
AoyagiNormalCrossingChartCertificate.jacobianPriorLossShift_jacobianPriorExp
AoyagiNormalCrossingChartCertificate.exponentData_jacobianPriorLossShift
AoyagiNormalCrossingChartCertificate.exponentData_exponentMinimum_jacobianPriorLossShift
AoyagiNormalCrossingChartCertificate.exponentData_exponentOrder_jacobianPriorLossShift
```

## Nonclaims

This does not construct regular coordinates, chart coverage, analytic unit
neighbourhoods, a Jacobian/volume-form theorem, a regular-suspension
certificate, normal crossings, pole order, RLCT additivity, or the
normal-crossing-to-RLCT extraction theorem.  It is an operation on an already
supplied chart-certificate spine.

## Kill Conditions

- The shifted chart certificate must project definitionally to the existing
  finite exponent-data shift.
- The loss exponents and active-coordinate set must remain unchanged.
- The theorem must not be used as a substitute for constructing the
  post-Theorem-3 regular-suspension chart certificate.
- Any final RLCT statement must still use the single cited extraction theorem
  only after the full chart certificate has been supplied.
