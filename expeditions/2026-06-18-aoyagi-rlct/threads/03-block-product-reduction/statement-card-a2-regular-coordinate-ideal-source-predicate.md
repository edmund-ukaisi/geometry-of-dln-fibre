# Statement Card - A2 regular-coordinate ideal source predicate

Date: 2026-06-24.

Lean files:

- `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`
- `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionAlgebraicSource.lean`

## Lean Names

```text
PaperEndpointFixedBaseRegularCoordinateIdealSourceNeighborhood
PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate.exists_regularCoordinateIdeal_source_neighborhood
PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate.regularCoordinateIdealSourceNeighborhood
AoyagiCanonicalProductDifferenceRegularCoordinateIdealSource
aoyagiCanonicalProductDifferenceRegularCoordinateIdealSource_of_localSourceCertificate
AoyagiSuppliedRegularSuspensionBoundary.of_canonicalProductDifferenceRegularCoordinateIdealSource
```

## Statement Shape

`PaperEndpointFixedBaseRegularCoordinateIdealSourceNeighborhood` is a named
fixed-base source-side predicate.  It records an ordinary neighborhood `U` of
the base point such that, for each `x in U` lying in
`paperEndpointFixedBaseSourceRankStratum`, the canonical product-difference
entry ideal splits as

```text
AoyagiRegularBlockCoordinateIndex.entryIdeal
  (S.Ctop - 1) (-S.B) (lowerLeftBlock S.L) ⊔ matrixEntryIdeal S.D.
```

`AoyagiCanonicalProductDifferenceRegularCoordinateIdealSource` packages an
existential fixed-base local source certificate together with that named
neighborhood predicate, in the same argument shape as a supplied
regular-suspension source obligation.

The boundary constructor fills only the `regular_chart_source` field of
`AoyagiSuppliedRegularSuspensionBoundary`; ideal transport, coverage, Jacobian
compatibility, and exponent shift remain supplied.

## Scope

Source-side algebraic product-difference bookkeeping for Aoyagi's p. 13
regular/residual block separation.

## Nonclaims

No source-rank openness, analytic germ-ideal transport, construction of the
full regular-suspension chart `Cfull`, chart coverage, Jacobian compatibility,
exponent-shift proof, normal crossings, pole order, or RLCT.
