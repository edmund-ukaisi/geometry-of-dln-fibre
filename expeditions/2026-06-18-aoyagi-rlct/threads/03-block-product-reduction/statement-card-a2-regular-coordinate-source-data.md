# Statement Card - A2 regular-coordinate source data

Date: 2026-06-24.

Lean file:

- `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`

## Lean Names

```text
PaperEndpointFixedBaseRegularBlockScalarCoordinatesCenteredContinuousAt
PaperEndpointFixedBaseResidualBlockScalarCoordinatesCenteredContinuousAt
PaperEndpointFixedBaseRegularCoordinateSourceData
PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate.regularCoordinateSourceData
exists_paperEndpointFixedBaseRegularCoordinateSourceData_of_rank_eq
```

## Statement Shape

The fixed-base source-data structure packages:

- the layer-dimension convention `H(k+1)=finrank(W k)`;
- a fixed-base canonical product-difference local source certificate;
- the source-neighborhood regular/residual ideal split;
- centered continuity for the scalar regular coordinates
  `S.Ctop - 1`, `-S.B`, and `lowerLeftBlock S.L`;
- centered continuity for scalar residual coordinates of `S.D`;
- the cardinality equality with
  `aoyagiTheorem2RegularVariableCount N H r`.
- the residual endpoint entry count `(H 1-r)*(H(N+1)-r)`.

The rank-equality theorem starts from a continuous reversed-edge family based
at `B`, base product rank `r`, base edge ranks `rEdge`, and the dimension
convention.  It chooses a total-kernel complement and returns the fixed-base
regular-coordinate source-data package.

## Scope

Source-side regular-coordinate data for Aoyagi's p. 13 regular-variable
separation.  This is intended as input for a later concrete
regular-suspension/transport boundary.

## Nonclaims

No exact-rank or source-rank openness, analytic germ-ideal transport,
regular-suspension chart construction, chart coverage, Jacobian compatibility,
normal crossings, pole order, or RLCT is proved.
