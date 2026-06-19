# Statement card - A4 pivot-first following-factor transport

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @
`a3f0ab623481ef756e8f3994b6f02f8a39caacb0`.

Names:

- `DLNFibre.DLN.Aoyagi.pivotFirstFollowingFactor`
- `DLNFibre.DLN.Aoyagi.pivotFirstMatrix_mul_pivotFirstFollowingFactor`

## Statement

Lean now names the following factor in pivot-first column coordinates and
proves that multiplying the pivot-first residual block by this reindexed
following factor is the same as reindexing the pre-reindexed product in the
pivot-first row order.

## Source role

Aoyagi's displayed `Q/P` calculation replaces the following factor by
`Q^{-1} C`. The existing pivot-first `Q/P` product theorem assumes that `C` is
already in pivot-first column coordinates. This checkpoint supplies the finite
matrix reindexing theorem that identifies that transported following factor.

## Proved

- `pivotFirstFollowingFactor colPivot C` is `C` with rows reindexed by
  `pivotFirstIndexEquiv colPivot`.
- Matrix multiplication commutes with this pivot-first reindexing:

```text
pivotFirstMatrix rowPivot colPivot A * pivotFirstFollowingFactor colPivot C
  =
(A * C).submatrix (pivotFirstIndexEquiv rowPivot) id.
```

## Assumed

- This is only the finite matrix block `A` and following factor `C`; any
  source-to-block coordinate construction is external to this theorem.

## Not proved

- No selected-entry chart construction, affine atlas, or chart coverage.
- No regularity/Jacobian theorem for the coordinate change.
- No exponent update, transition invariant, termination proof,
  normal-crossing certificate, or RLCT extraction.

## Reproduction and review

- Reproduction artifact:
  `reproduction-pivot-first-following-factor-a4.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
- `lake build DLNFibre`
- `./scripts/sorries`
- `git diff --check`
