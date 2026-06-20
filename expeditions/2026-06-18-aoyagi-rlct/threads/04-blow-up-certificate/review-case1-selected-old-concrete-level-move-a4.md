# Review - A4 Case 1(1) Selected-Old Concrete Level Move

Reviewers: xhigh source/math reviewer `Nash the 3rd`; xhigh Lean/API reviewer
`Chandrasekhar the 3rd`.

Status: passed after Lean implementation and verification.

## Findings

No blocking findings.

The source/math reviewer found one caveat: "variables unchanged" must mean
recurrence-label variables only, not raw residual matrix coordinates.  The
reproduction note and Lean docstring now state that caveat explicitly.

The Lean/API reviewer recommended not giving the constructor an explicit `J`
argument, because `J` is already carried by
`IntroducedLabelRecurrenceState L n S J alpha`.  The Lean implementation uses
`pre.case1SelectedOldLevelMove s0 k0`.

## Verdict

The checkpoint is source-faithful recurrence bookkeeping for Aoyagi Case 1(1).
It provides a canonical same-domain post-state for the existing erased-base
lowered-recurrence boundary, without claiming chart production.

## Residual Risks

- The theorem does not construct the selected-old blow-up chart from raw
  coordinates.
- The theorem does not identify `(s0,k0)` from the `Unit` finite-center token.
- Chart coverage, regularity from coordinates, Jacobian accounting, normal
  crossings, RLCT extraction, and the full transition invariant remain open.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
