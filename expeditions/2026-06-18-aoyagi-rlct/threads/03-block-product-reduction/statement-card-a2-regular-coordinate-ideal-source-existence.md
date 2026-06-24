# Statement Card - A2 regular-coordinate ideal source existence

Date: 2026-06-24.

Lean file:

- `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionAlgebraicSource.lean`

## Lean Name

```text
exists_aoyagiCanonicalProductDifferenceRegularCoordinateIdealSource
```

## Statement Shape

Given a continuous reversed-edge family `Cedge` at `x0`, the base equality
`Cedge x0 = reverseEdge W B`, supplied product rank `r`, supplied edge ranks
`rEdge`, and supplied base inequalities `r <= rEdge p`, Lean constructs

```text
AoyagiCanonicalProductDifferenceRegularCoordinateIdealSource
  W B x0 Cedge r rEdge Cred Cfull regularCount.
```

The proof is exactly the composition of the existing raw local source
certificate constructor

```text
exists_paperEndpointCanonicalProductDifferenceLocalSourceCertificate
```

with

```text
aoyagiCanonicalProductDifferenceRegularCoordinateIdealSource_of_localSourceCertificate.
```

## Scope

Source-side algebraic existence for the canonical product-difference
regular-coordinate/residual ideal source predicate.

## Nonclaims

No source-rank openness, analytic germ-ideal transport, construction of
`Cfull`, construction of regular ideal transport, chart coverage, Jacobian
compatibility, exponent shift, normal crossings, pole order, or RLCT.
