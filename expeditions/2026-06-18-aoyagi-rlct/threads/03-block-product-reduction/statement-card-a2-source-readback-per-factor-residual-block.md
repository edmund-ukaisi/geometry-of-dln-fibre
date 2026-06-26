# Statement card - A2 source-readback per-factor residual block

## Claim

For every retained-passive-shaped source edge family `E` and edge index `p`,
the source-readback residual factor is exactly the Schur residual block of the
transformed source edge visited by the suffix recursion.

## Lean artifact

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
```

Theorem:

```lean
sourceReadback_C_eq_schurResidualBlock_sourceReadbackTransformedEdge
```

Statement:

```lean
(sourceReadback E).C p =
  schurResidualBlock (sourceReadbackTransformedEdge E p)
```

The proof is `rfl`.

## Role

This is a source-readback per-factor API theorem.  It complements the already
landed full residual readout
`paperEndpointFixedBaseResidualBlockCoordinateMap_eq_sourceReadback_residualFactorProduct`
by exposing the individual factors that enter that product.

## Nonclaims

No endpoint equivalence, Case 2 factor identity, full-suffix collapse, source
chart, source image, pivot nonzero proof, pushforward/Jacobian theorem,
original-loss comparison, normal crossing, pole order, or RLCT extraction is
proved.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates
```

passed on 2026-06-26.

Review:

```text
threads/03-block-product-reduction/review-a2-source-readback-per-factor-residual-block.md
```
