# Statement Card - A2 single-edge residual-product realisation

## Claim

In the one-edge p.13 product-coordinate matrix

```text
productCoordinateSingleEdgeMatrix F2 F3 Ctop D,
```

the raw suffix residual product is the supplied residual matrix `D`, assuming
`IsUnit Ctop.det`.

## Lean Statements

```text
ChartLocalSuffixState.residualProduct_productCoordinateSingleEdge_eq
paperEndpointFixedBaseSingleEdgeProductCoordinateMatrixOfEuclidean_residualProduct_eq
```

## Dependencies

- `ChartLocalSuffixState.suffixState_productCoordinate_fields_one`
- `ChartLocalSuffixState.suffixState_D_eq_residualProduct`
- the fixed-base matrix constructor
  `paperEndpointFixedBaseSingleEdgeProductCoordinateMatrixOfEuclidean`

## Kill Conditions

- If the Schur residual theorem is read as a raw lower-right block identity,
  the claim is wrong: the raw lower-right block is `D + F3*Ctop*F2`.
- If the determinant-unit hypothesis is removed, the current Schur-complement
  cancellation no longer has the stated proof.
- If the statement is generalized to multi-edge chains without intermediate
  factor data, it conflicts with the rank obstruction already formalised for
  residual-factor products.

## Verification

Focused `ProductReduction` and `RegularSuspensionCoordinates` builds passed
via `scripts/lb`.  The full `scripts/lb` build passed.  `scripts/sorries`
reported zero forbidden markers, and `git diff --check` was clean.

## Boundary

This is finite one-edge product-coordinate algebra.  It is not source-chart
construction, source coverage, residual-index equivalence, density/Jacobian
transport, normal-crossing production, pole-order computation, or RLCT
extraction.
