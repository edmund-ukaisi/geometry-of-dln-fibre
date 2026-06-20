# Review - A4 Case 2 displayed source-terminal candidate

Status: xhigh source/math and Lean/API review passed after a proof-shape
cleanup.

## Scope Reviewed

Files:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `threads/04-blow-up-certificate/reproduction-case2-displayed-source-terminal-candidate-a4.md`
- `threads/04-blow-up-certificate/statement-card-a4-case2-displayed-source-terminal-candidate.md`

Lean names:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedPaperTerminalWeight`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedPaperTerminalCnext`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedPaperTerminalCprimeCandidate`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedPaperTerminalCprimeCandidate_eq_weight_mul_cnext_mul`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedPaperTerminalCprimeCandidate_eq_verticalBlock_mul`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceDisplayedWeightedTerminalProduct_entryIdeal_eq_topStack_of_not_next_cont`

## Verdict

No source/math fidelity findings.

The candidate keeps weights outside the unweighted stack `[Cold; C0]`, then
multiplies by the supplied suffix `F`.  The theorem's assumptions remain
explicit: a supplied displayed boundary, supplied old top multiplier and block,
supplied suffix, and failed next continuation.

## Checks

- The candidate is source-order shaped: `(blockdiag(Wold,[b0]) * [Cold;C0]) * F`.
- The theorem combines only the supplied displayed source-chart `Q/P` identity
  with the existing stopped terminal absorption theorem.
- It does not claim `[Cold;C0]` is Aoyagi's source-produced `C'^(S+1)`.
- It does not use chart coverage, Jacobian arithmetic, RLCT extraction,
  termination, transition invariance, printed-vector repair, or unit
  cancellation.
- The row-vs-column terminal issue remains documented as a boundary: Lean uses
  the already formalised displayed pivot-first stopped block.

## Review Fixes Applied

- Extracted
  `case2DisplayedPaperTerminalCprimeCandidate_eq_verticalBlock_mul` so the main
  theorem no longer relies on a fragile final local `change` block.
- Split the source-order candidate into separately named terminal weight and
  unweighted terminal `Cnext` components.
- Added this review artifact, which the statement card references.
- Updated the statement card verification command to say it is run from
  `lean/`.

## Verification

- `git diff --check`
- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
