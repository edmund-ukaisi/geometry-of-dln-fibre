# Review - A4 Case 2 displayed terminal source model

Status: xhigh source/math and precision review passed for the intended
checkpoint; controller Lean verification passed after implementation.

## Scope Reviewed

Files:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `threads/04-blow-up-certificate/reproduction-case2-displayed-terminal-source-model-a4.md`
- `threads/04-blow-up-certificate/statement-card-a4-case2-displayed-terminal-source-model.md`

Lean names:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedActualWidthTerminalSourceModel`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedActualWidthTerminalSourceModel.terminalWeightCandidate`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedActualWidthTerminalSourceModel.terminalCnextCandidate`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedActualWidthTerminalSourceModel.terminalProductCandidate`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedActualWidthTerminalSourceModel.not_next_cont_of_actualWidth_exhausted`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedActualWidthTerminalSourceModel.introducedLabel_terminal_iff_succStage_zero`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedActualWidthTerminalSourceModel.introducedLabelFinset_terminal_eq_succStage_zero`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.exists_weightedTerminalProduct_entryIdeal_eq_terminalProductCandidate_of_actualWidth`

## Verdict

No source/math fidelity blocker found.

The xhigh source check confirmed that actual next-width exhaustion
`n(S+1)=J+1` is sufficient, and under displayed pivot validity necessary, for
identifying old `(S,J+1)` introduced labels with stage-relabelled `(S+1,0)`
introduced labels.  Prefix exhaustion alone is insufficient: if
`prefixMinNat n S = J+1` but `n(S+1) >= J+2`, then `(S,J+2)` is an extra
label at `(S+1,0)`.

## Checks

- The model remains supplied: `Atop`, `Ctop`, and `F` are fields.
- The theorem derives failed next continuation from actual-width exhaustion
  and calls the existing supplied displayed-boundary terminal theorem.
- The label-domain equality is stated only for `introducedLabel` and
  `introducedLabelFinset`; it is not used to claim recurrence or exponent
  post-data over `(S+1,0)`.
- The pivot weight `post.weight (J+1)` remains outside the unweighted
  candidate matrix.
- No chart production, chart coverage, regularity, Jacobian arithmetic,
  normal crossings, RLCT extraction, termination, transition invariant, or
  printed-vector repair is claimed.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
