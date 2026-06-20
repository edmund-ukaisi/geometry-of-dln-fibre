# Review - A4 Case 2 actual-width terminal relabel

Status: xhigh source/math and Lean/API review passed for the intended
checkpoint; controller Lean verification passed after implementation.

## Scope Reviewed

Files:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `threads/04-blow-up-certificate/reproduction-case2-actual-width-terminal-relabel-a4.md`
- `threads/04-blow-up-certificate/statement-card-a4-case2-actual-width-terminal-relabel.md`

Lean names:

- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.stageRelabelSuccZero`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.stageRelabelSuccZero_step_eq`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.stageRelabelSuccZero_weight_eq`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelLevelInvariants.relabel_currentSucc_succStage_zero_of_nextWidth_eq`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelExponentCertificates.relabel_currentSucc_succStage_zero_of_nextWidth_eq`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.terminalRelabelPost`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.terminalRelabelPost_step_eq_of_actualWidth`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.terminalRelabelPost_weight_eq_of_actualWidth`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.terminalRelabelPostLevelInvariants_of_actualWidth`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.terminalRelabelExponentDomain_of_actualWidth`

## Verdict

No source/math fidelity blocker found.

The xhigh source/math scout `Lovelace the 4th` and xhigh Lean/API scout
`Tesla the 4th` both confirmed that this is a valid elementary consequence of
actual next-width exhaustion.  Recurrence states are total maps, so copying
`level` and `var` is harmless.  Step equality follows by rewriting the finite
product domain, and exponent certificates transport because the state
parameter appears only in the introduced-label proof.

## Checks

- The relabel assumes actual-width exhaustion, not merely prefix exhaustion.
- Labels are not renamed; `(S,J+1)` remains the source label identity.
- The result transports supplied data only.
- Gap and flat-tail packages are not transported.
- No chart production, source-produced following matrix, coverage, Jacobian,
  normal-crossing/RLCT, termination, transition invariant, or printed-vector
  repair is claimed.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- From `lean/`: `lake build DLNFibre`
- From `lean/`: `scripts/sorries`
- Forbidden-token scan over `lean/DLNFibre/DLN/Aoyagi`
- `git diff --check`
