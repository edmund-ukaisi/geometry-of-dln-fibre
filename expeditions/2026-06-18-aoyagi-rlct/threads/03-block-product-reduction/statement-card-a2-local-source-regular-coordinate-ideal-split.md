# Statement Card - A2 local source regular-coordinate ideal split

Date: 2026-06-24.

Lean file:
`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`

## Lean Name

```text
PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate.exists_regularCoordinateIdeal_source_neighborhood
```

## Statement Shape

Given a fixed-base canonical product-difference local source certificate, Lean
produces an ordinary neighborhood `U` of the base point.  For every
`x in U` that also lies in `paperEndpointFixedBaseSourceRankStratum`, the
canonical product-difference entry ideal satisfies

```text
matrixEntryIdeal(productDifference at x)
  =
AoyagiRegularBlockCoordinateIndex.entryIdeal
  (S.Ctop - 1) (-S.B) (lowerLeftBlock S.L)
  ⊔ matrixEntryIdeal S.D.
```

## Scope

Local source-side algebraic ideal bookkeeping.  The result composes the
existing local source certificate with the scalar regular-coordinate ideal and
regular/residual ideal split.

## Nonclaims

No source-rank openness, analytic ideal/germ transport, regular-suspension
chart construction, coverage, Jacobian compatibility, normal crossings, pole
order, or RLCT.
