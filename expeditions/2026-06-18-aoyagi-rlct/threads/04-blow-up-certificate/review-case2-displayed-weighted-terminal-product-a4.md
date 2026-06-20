# Review - A4 Case 2 displayed weighted terminal product

Status: xhigh source/math and Lean/API review passed for the finite
weighted terminal-product checkpoint.

## Scope Reviewed

Files:

- `lean/DLNFibre/DLN/Aoyagi/EntryIdeal.lean`
- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `threads/04-blow-up-certificate/reproduction-case2-displayed-weighted-terminal-product-a4.md`
- `threads/04-blow-up-certificate/statement-card-a4-case2-displayed-weighted-terminal-product.md`

Lean theorem:

- `DLNFibre.DLN.Aoyagi.matrixEntryIdeal_case2DisplayedPaperWeightedTerminalProduct_eq_topStack_of_not_next_cont`

## Verdict

No high- or medium-severity findings.

The theorem proves the intended supplied-data statement: under displayed pivot
validity and failed next continuation, the diagonal-weighted stopped terminal
product with a supplied suffix `F` has the same matrix-entry ideal as the stack
of `(Wold * Cold) * F` and `(b0 * C0) * F`.

## Checks

- `F` is incorporated before zero-row deletion.  The proof does not use an
  invalid rule that entry-ideal equality is preserved by arbitrary right
  multiplication.
- The surviving pivot row remains weighted by `b0`; there is no unit
  assumption or cancellation of `b0`.
- `Cold`, `Wold`, `b0`, `b`, and `F` remain supplied finite data.
- The theorem does not identify the right hand side with Aoyagi's
  `C'^(S+1)`, choose the row/column terminal presentation, or construct
  chart-produced post-data.

## Review Fixes Applied

- Renamed the theorem from
  `matrixEntryIdeal_case2DisplayedPaperWeightedTerminalProduct_eq_topStack` to
  `matrixEntryIdeal_case2DisplayedPaperWeightedTerminalProduct_eq_topStack_of_not_next_cont`
  so the API name exposes the failed-continuation hypothesis.
- Removed a redundant explicit finite-instance binder from the public theorem
  signature.
- Added this review artifact, which the statement card already referenced.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/EntryIdeal.lean`
- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
