# Review - A4 Case 2 terminal relabel-weight candidate

Status: xhigh source/math and Lean/API review passed for the intended
checkpoint; focused Lean verification passed after implementation.

## Scope Reviewed

Files:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `threads/04-blow-up-certificate/reproduction-case2-terminal-relabel-weight-candidate-a4.md`
- `threads/04-blow-up-certificate/statement-card-a4-case2-terminal-relabel-weight-candidate.md`

Lean names:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceTerminalEntryIdeal_eq_relabelCandidate_of_actualWidth`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.exists_terminalModelEntryIdeal_eq_relabelProductCandidate_of_actualWidth`

## Verdict

No source/math or Lean/API blocker found.

The xhigh source/math scout `James the 4th` confirmed that this is a harmless
rewrite of the stopped supplied terminal candidate, useful only for downstream
vocabulary.  The xhigh Lean/API scout `Planck the 4th` confirmed the proof
shape and the dependent `b0` model issue: the source-model wrapper must be
specialized to `b0 = data.terminalRelabelPost.weight (J+1)` rather than
transporting a model whose `b0` is definitionally `post.weight (J+1)`.

## Checks

- The theorem requires actual-width exhaustion.
- The result is presentational API, not new chart production.
- `Atop`, `Ctop`, and `F` remain supplied.
- No source-produced `C'^(S+1)`, gap/tail transport, coverage, Jacobian,
  normal-crossing/RLCT, termination, transition invariant, or printed-vector
  repair is claimed.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- From `lean/`: `lake build DLNFibre`
- From `lean/`: `scripts/sorries`
- Forbidden-token scan over `lean/DLNFibre/DLN/Aoyagi`
- `git diff --check`
