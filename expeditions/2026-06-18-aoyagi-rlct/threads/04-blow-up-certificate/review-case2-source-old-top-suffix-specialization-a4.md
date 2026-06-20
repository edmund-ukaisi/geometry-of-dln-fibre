# Review - A4 Case 2 source old-top/suffix specialization

Status: passed xhigh source/math review and xhigh Lean/API review; focused
Lean verification passed after implementation.

## Scope Reviewed

Files:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `threads/04-blow-up-certificate/reproduction-case2-source-old-top-suffix-specialization-a4.md`
- `threads/04-blow-up-certificate/statement-card-a4-case2-source-old-top-suffix-specialization.md`

Lean names:

- `DLNFibre.DLN.Aoyagi.case2SourceOldTopRowIndex`
- `DLNFibre.DLN.Aoyagi.case2DisplayedSourceOldTopWeight`
- `DLNFibre.DLN.Aoyagi.case2DisplayedSourceOldTopBlock`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceDisplayedOldTopSuffixTerminalProduct_entryIdeal_eq_of_not_next_cont`

## Verdict

PASS.  The checkpoint is source-faithful as a specialization of the existing
stopped terminal theorem: old top rows are `1..J`, the old top diagonal is
`diag(pre.weight i)`, and the old top block is the source row restriction
`C(i,t)` over those rows.

Caveat: this does not construct the suffix product or source-produced
`C'^(S+1)`.  The suffix `F` remains supplied.

## Checks

- Old top rows are `1,...,J`, separate from the active residual block.
- The old top diagonal uses `pre.weight`, not a new or transported weight.
- The suffix `F` remains supplied.
- The result is a specialization of an existing terminal theorem, not a proof
  of source-produced `C'^(S+1)`.
- No chart production, coverage, Jacobian, normal-crossing/RLCT, termination,
  transition invariant, automatic gap/tail transport, or printed-vector repair
  is claimed.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- Source/math reviewer: PASS, no source/math fidelity issue.
- Lean/API reviewer: PASS, no blocking Lean/API issue.
