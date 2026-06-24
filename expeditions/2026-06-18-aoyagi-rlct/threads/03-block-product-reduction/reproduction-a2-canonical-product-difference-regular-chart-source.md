# Reproduction - A2 canonical product-difference regular-chart source

Date: 2026-06-24.

Status: reproduced before Lean implementation.

## Source Anchor

Aoyagi PDF pp. 11-13 reduce the endpoint product near a rank-`r` base chain to
regular block variables and a residual product.  On p. 13 the regular blocks
appearing in the product-difference ideal are

```text
C1 - Er,   F2,   F3,
```

while the singular residual block is the product of the reduced matrices
`C^(s)`.

The already formalised canonical product-difference local source certificate
gives the source-side p. 13 local package: centered continuous canonical fields,
the product-difference entry-ideal equality with those fields, and residual
rank formulas, all relative to Aoyagi's source-shaped rank stratum and with the
base chain included in that stratum under supplied rank data.

## Boundary Being Reproduced

The current regular-suspension interface has an abstract source predicate

```text
RegularChartSource Cred Cfull regularCount.
```

The elementary A2 certificate can discharge this field when the predicate is
specialised to the canonical product-difference local source certificate.
This is a source-domain handoff only.  It does not construct the full
regular-suspension chart and does not prove analytic ideal transport,
coverage, Jacobian compatibility, or the finite exponent shift.

The Lean predicate is:

```text
AoyagiCanonicalProductDifferenceRegularChartSource W B x0 Cedge r rEdge
```

applied to `Cred`, `Cfull`, and `regularCount`.  It ignores the chart
certificates and regular count by design, because its content is exactly the
A2 source-side product-difference local certificate.

## Constructor

Given

```text
PaperEndpointCanonicalProductDifferenceLocalSourceCertificate
  W B x0 Cedge r rEdge,
```

and the still-supplied regular-suspension fields

```text
RegularIdealTransport Cred Cfull regularCount,
RegularCoverage Cred Cfull regularCount,
RegularJacobianCompatible Cred Cfull regularCount,
Cfull.exponentData = Cred.exponentData.jacobianPriorLossShift regularCount,
```

Lean constructs

```text
AoyagiSuppliedRegularSuspensionBoundary Cred Cfull regularCount
  (AoyagiCanonicalProductDifferenceRegularChartSource W B x0 Cedge r rEdge)
  RegularIdealTransport RegularCoverage RegularJacobianCompatible.
```

This fills only the `regular_chart_source` field.  The other fields remain
exactly the supplied obligations of the general boundary.

## Nonclaims

- No scalar coordinate list for the regular blocks.
- No proof that the regular-coordinate count is
  `aoyagiTheorem2RegularVariableCount`.
- No construction of `Cfull` from `Cred`.
- No analytic ideal or germ transport theorem.
- No chart coverage theorem.
- No Jacobian compatibility theorem.
- No proof of the finite exponent-shift equality.
- No normal-crossing production, pole-order theorem, or RLCT theorem.
