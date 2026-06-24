# Statement Card - A2 residual-coordinate source data

Date: 2026-06-24.

Lean file:

- `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`

## Lean Names

```text
AoyagiResidualBlockCoordinateIndex
AoyagiResidualBlockCoordinateIndex.value
AoyagiResidualBlockCoordinateIndex.entryIdeal
AoyagiResidualBlockCoordinateIndex.entryIdeal_eq_matrixEntryIdeal
AoyagiResidualBlockCoordinateIndex.value_centered_continuousAt
AoyagiResidualBlockCoordinateIndex.card_eq_endpointResidualEntryCount
paperEndpointResidualBlockCoordinateIndex_card_eq_endpointResidualEntryCount
PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.residualBlockScalarCoordinates_centered_continuousAt
PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.residualBlockCoordinateIndex_card_eq_endpointResidualEntryCount
PaperEndpointFixedBaseResidualBlockScalarCoordinatesCenteredContinuousAt
```

The existing structure `PaperEndpointFixedBaseRegularCoordinateSourceData` now
also carries:

```text
residualScalarCoordinates_centered_continuousAt
residualCoordinateIndex_card_eq_endpointResidualEntryCount
```

## Statement Shape

The residual scalar-coordinate index is the product of the row/left and
column/right residual endpoint indices.  Its value function reads entries of
the residual block `D`, and its scalar-coordinate ideal is definitionally equivalent to
`matrixEntryIdeal D`.

For the fixed-base canonical product-difference local certificate, Lean
projects the existing centered continuity of `S.D` to each residual scalar
coordinate.  Under the dimension convention and base product rank, the
residual-coordinate index cardinality is

```text
(H 1 - r) * (H (N+1) - r).
```

## Scope

Source-side scalar bookkeeping for the residual block in Aoyagi's p. 13
regular/residual split.  This strengthens the source-data package by making
the reduced block entries explicit, while keeping them separate from the
regular-coordinate index and regular-variable shift.

## Nonclaims

No analytic residual chart, normal-crossing certificate, germ-ideal transport,
chart coverage, Jacobian compatibility, exponent shift, regular-coordinate
additivity, pole order, or RLCT is proved.
