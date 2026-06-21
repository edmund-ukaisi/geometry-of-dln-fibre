# Review - A4 Case 2 post-pivot source residual

Reviewer: xhigh `Bacon`.

Scope:

- `case2DisplayedPostPivotSourceResidual`;
- `case2SourceResidualBlock_postPivotSourceResidual`;
- `case2DisplayedPaperDppp_mul_Cprime_postPivot_eq_sourceResidualBlock_sourceFollowingFactor`;
- reproduction/card/ledger updates for the post-pivot source-residual slice.

## Findings

None.

## Verdict

Pass for the narrow Aoyagi-only slice.  The Lean additions are limited to a
zero-extended source-coordinate representative of
`case2DisplayedPostPivotResidualBlock`, an entrywise restriction-recovery
lemma, and a rewrite of the existing lower-row product into
`case2SourceResidualBlock * case2SourceFollowingFactor` notation.

The review found no claims of chart production, source-produced successor
post-data, transition invariance, full successor product, terminal relabeling,
normal crossings, pole order, or RLCT.

## Commands Run

- `git status --short --branch`
- `git diff -- lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `git diff -- expeditions/...`
- targeted `rg`/`sed` inspections of the new Lean names and artifacts
- `pdftotext -f 19 -l 22 paper-sources/aoyagi-2023-consideration-of-learning-efficiency-of-dln/aoyagi-2023-neural-networks-preprint.pdf -`
- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
- `git diff --check`

## Residual Risk

Later consumers still need to preserve the distinction between this finite
notation adapter and any genuine chart-produced transition or analytic/RLCT
result.
