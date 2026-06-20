# Review - A4 Case 2 source-chart terminal model constructor

Status: xhigh source/math and Lean/API review passed for the intended
checkpoint; focused Lean verification passed after implementation.

## Scope Reviewed

Files:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `threads/04-blow-up-certificate/reproduction-case2-source-chart-terminal-model-constructor-a4.md`
- `threads/04-blow-up-certificate/statement-card-a4-case2-source-chart-terminal-model-constructor.md`

Lean name:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.exists_terminalModelEntryIdeal_eq_relabelProductCandidate_of_sourceChartMap_actualWidth`

## Verdict

No source/math or Lean/API blocker found.

The xhigh source/math scout `Dewey the 4th` confirmed that this is
source-faithful as a composed supplied-boundary API: instantiate the displayed
source-chart boundary, then apply the actual-width terminal relabel-model
wrapper.  The xhigh Lean/API scout `Godel the 4th` confirmed feasibility and
recommended avoiding models indexed by `post.weight(J+1)`.

The accepted Lean statement writes the concrete relabelled source-chart
post-state weight directly in the terminal model parameter.  A prettier local
`data` statement was tested but rejected after it triggered field-projection
and elaboration timeout problems in the full theorem body.

## Checks

- The theorem keeps `Atop`, `Ctop`, and `F` supplied.
- The theorem uses actual-width exhaustion.
- The terminal matrix remains a candidate.
- No source-produced `C'^(S+1)`, chart coverage, Jacobian, normal-crossing/RLCT,
  termination, transition invariant, gap/tail transport, or printed-vector
  repair is claimed.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- From `lean/`: `lake build DLNFibre`
- From `lean/`: `scripts/sorries`
- Forbidden-token scan over `lean/DLNFibre/DLN/Aoyagi`
- `git diff --check`
