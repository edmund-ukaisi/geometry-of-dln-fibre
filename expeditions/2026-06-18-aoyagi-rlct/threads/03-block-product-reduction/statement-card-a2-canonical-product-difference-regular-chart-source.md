# Statement Card - A2 canonical product-difference regular-chart source

Date: 2026-06-24.

Lean file:
`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionInterface.lean`

## Lean Names

```text
AoyagiCanonicalProductDifferenceRegularChartSource
AoyagiSuppliedRegularSuspensionBoundary.of_canonicalProductDifferenceRegularChartSource
```

## Statement Shape

`AoyagiCanonicalProductDifferenceRegularChartSource` specialises the abstract
regular-suspension source predicate to the already proved A2 local source
certificate:

```text
PaperEndpointCanonicalProductDifferenceLocalSourceCertificate W B x0 Cedge r rEdge.
```

The constructor
`AoyagiSuppliedRegularSuspensionBoundary.of_canonicalProductDifferenceRegularChartSource`
builds the supplied regular-suspension boundary for this specialised source
predicate from:

```text
PaperEndpointCanonicalProductDifferenceLocalSourceCertificate W B x0 Cedge r rEdge,
RegularIdealTransport Cred Cfull regularCount,
RegularCoverage Cred Cfull regularCount,
RegularJacobianCompatible Cred Cfull regularCount,
Cfull.exponentData = Cred.exponentData.jacobianPriorLossShift regularCount.
```

## Scope

This is an A2-to-regular-suspension interface theorem.  It reduces one abstract
regular-suspension field, `regular_chart_source`, to the source-backed local
product-difference certificate.

## Nonclaims

It does not scalarize the regular blocks, prove the regular count, construct
the full chart certificate, prove ideal transport, prove coverage, prove
Jacobian compatibility, prove the exponent equality, produce normal crossings,
identify pole order, or extract RLCT.
