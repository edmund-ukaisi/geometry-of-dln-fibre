# Review - A2 triangular block diagonal form

Reviewer: xhigh `Kepler`.  Scope: uncommitted changes in
`lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean` and
`lean/DLNFibre/DLN/Aoyagi/ProductReductionBoundary.lean`.

## Verdict

Pass.  No findings.

## Checks run by reviewer

- `lake env lean DLNFibre/DLN/Aoyagi/ProductReduction.lean`
- `lake env lean DLNFibre/DLN/Aoyagi/ProductReductionBoundary.lean`
- `git diff --check`

## Audited points

- `S.L` is proved lower unitriangular as `[I 0; F3 I]`.
- The right multiplier is stated as `[I F2; 0 I]`, with proof witness
  `F2 = -S.B`.
- Endpoint types match the reversed Aoyagi orientation: `F3` is at
  `Fin.last N`, and `F2` is at `0`.
- Product order is `left * total * right`, matching the existing certificate.
- Determinant-unit conjuncts are only algebraic regularity of triangular block
  matrices.

## Residual nonclaims

No chart coverage theorem, exact-rank openness, ideal/RLCT consequence,
normal-crossing extraction, or full source-hypothesis version of Aoyagi
Theorem 3 is claimed here.
