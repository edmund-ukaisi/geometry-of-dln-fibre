# Statement card - A4 Case 2 arbitrary-suffix terminal wrapper

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceOldTopSuffix_entryIdeal_eq_sourceTerminalProduct_of_not_next_cont`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceOldTopSuffix_entryIdeal_eq_suppliedTerminalCprimeProduct_of_not_next_cont`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.exists_oldTopSuffix_entryIdeal_eq_relabelSuppliedTerminalProduct_of_actualWidth`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.exists_oldTopSuffix_entryIdeal_eq_relabelOriginalRowsTerminalProduct_of_actualWidth`

## Statement

Lean now exposes stopped Case 2 source-row terminal wrappers with the remaining
right following product kept as an arbitrary supplied matrix `F`.

In Lean, `F : Matrix τ υ R`: the row/input type `τ` is fixed by the terminal
`C'` factor's output columns, while the output column type `υ` is arbitrary.

## Proved

- The stopped source old-top/supplied-suffix entry-ideal equality rewrites from
  the paper terminal candidate to the one-based source-row terminal product.
- A supplied `SuppliedTerminalCprimeBridge` rewrites that source-row terminal
  product as `(terminalWeight * Cterm) * F`.
- In the actual-width branch `n(S+1)=J+1`, the surviving pivot weight can be
  read from the relabelled `(S+1,0)` post-state.
- In the same actual-width branch, the supplied bridge can be specialized to
  the original source rows `1..J+1`.

## Not Proved

- `F` remains supplied; this is not a theorem that produces the source suffix
  or an empty following product.
- The terminal bridge is consumed, not chart-produced.
- The original-row specialization is actual-width only and does not cover the
  row-exhausted wide-next branch.
- No chart production, chart coverage, Jacobian, normal-crossing/RLCT,
  termination, transition invariance, printed-vector repair, or
  source-produced `C'^(S+1)` theorem.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
