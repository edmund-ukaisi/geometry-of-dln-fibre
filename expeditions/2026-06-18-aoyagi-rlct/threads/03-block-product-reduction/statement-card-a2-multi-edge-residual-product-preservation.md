# Statement Card - A2 multi-edge residual-product preservation

Date: 2026-06-25.

## Claim

For a chain with at least two edges, raw p.13 product-coordinate matrices whose
residual factors are chosen as the base transformed Schur residual blocks have
the same residual product as the base family.

## Lean Artifacts

```text
ChartLocalSuffixState.schurResidualBlock_fromBlocks_upperRight_zero
ChartLocalSuffixState.schurResidualBlock_fromBlocks_lowerLeft_zero
ChartLocalSuffixState.residualProduct_eq_of_residualBlock_eq
ChartLocalSuffixState.suffixState_tail_fields_of_productCoordinateEdges_from
ChartLocalSuffixState.residualBlock_productCoordinateEdges_succSucc
ChartLocalSuffixState.residualProduct_productCoordinateEdges_succSucc_eq_base
```

## Inputs Kept Explicit

- the base edge matrix family `Ebase`;
- the new raw product-coordinate edge matrix family `E`;
- the regular blocks `F2`, `F3`, `Ctop`;
- raw right, middle, and left p.13 matrix-shape hypotheses for `E`, with
  residual factors `residualBlock Ebase last p`.

## Nonclaims

No one-edge endpoint-collapse statement is included here.  No dependent
`G(x,u)` family, parameter-continuity theorem, source coverage, product chart,
density/Jacobian transport, normal crossings, pole order, or RLCT extraction
is proved.

## Verification

Focused build passed:
`LAKE_SHARED=$PWD/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.ProductReduction`.
Full build passed:
`LAKE_SHARED=$PWD/.lake-local-shared scripts/lb DLNFibre`.
`scripts/sorries` reports zero `sorry`, `#exit`, `native_decide`, and `axiom`;
`git diff --check` is clean.
