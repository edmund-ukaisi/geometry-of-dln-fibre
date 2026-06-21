# Review - A2 residual product

Reviewer: xhigh `Pascal`. Endpoint-wrapper scout: xhigh `Copernicus`.
Scope: current residual-product changes in
`lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean` and
`lean/DLNFibre/DLN/Aoyagi/ProductReductionBoundary.lean`.

## Verdict

Pass. No blocking findings.

## Checks

- `lake env lean DLNFibre/DLN/Aoyagi/ProductReduction.lean` passed for the
  reviewer.
- Controller focused builds passed:
  `lake build DLNFibre.DLN.Aoyagi.ProductReduction` and
  `lake build DLNFibre.DLN.Aoyagi.ProductReductionBoundary`.
- Forbidden-token scan in the target ProductReduction file found no `sorry`,
  `axiom`, `native_decide`, or `#exit`.

## Audited points

- `ChartLocalSuffixState.residualProduct` is defined as a product of
  transformed Schur residual blocks, not raw lower-right edge blocks.
- `residualProduct_castSucc` unfolds in the same order as the suffix-state
  `D` update.
- `suffixState_D_eq_residualProduct` ties the named product to the existing
  deterministic state field.
- The endpoint wrapper is a direct rewrite of the existing certificate's
  `S.D`, using `suffixState_D_eq_residualProduct`.

## Non-blocking note

The top-level abstract residual-product wrapper keeps the existing strong
chart hypothesis `forall p Bprev, identityCornerDetChart ...`, while its proof
only uses the recursively visited `Bprev` values. This is stronger than the
chart-local induction needs, but it is explicit in the statement and not
mathematically false.

## Residual nonclaims

This is not a full Aoyagi Theorem 3 source-hypothesis theorem, not exact-rank
openness, not chart coverage, not analytic ideal transport, not a
normal-crossing statement, and not an RLCT consequence.
