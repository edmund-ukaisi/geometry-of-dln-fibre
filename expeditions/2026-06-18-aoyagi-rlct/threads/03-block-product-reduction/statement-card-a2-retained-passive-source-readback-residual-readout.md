# Statement card - A2 retained-passive source-readback residual readout

## Claim

For a fixed-base retained-passive-shaped edge family, the p.13 residual block
coordinate map is the scalar-entry map of the retained-passive
source-readback residual-factor product.

## Lean artifact

File:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalSource.lean`

Expected theorem:

```lean
paperEndpointFixedBaseResidualBlockCoordinateMap_eq_sourceReadback_residualFactorProduct
```

## Proved inputs

- `paperEndpointFixedBaseResidualBlockCoordinateMap_eq_residualProduct`
  identifies the fixed-base residual coordinate map with the deterministic
  suffix residual product.
- `RetainedPassiveNonredundantCoordinateData.sourceReadbackSuffixState_D_eq_residualFactorProduct_C`
  identifies the same suffix `D` block with the residual-factor product of the
  retained-passive source-readback `C` blocks.

## Supplied inputs

Only the fixed-base endpoint data and the edge family are parameters.  No
source chart, determinant-chart membership, measure, or loss hypotheses are
used.

## Nonclaims

This is not a selected-entry chart construction and not a residual-source
integrability theorem.  It does not prove weighted pushforward, Jacobian/source
density, original-loss comparison, normal crossings, pole order, or RLCT.
