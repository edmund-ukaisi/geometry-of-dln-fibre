# A4 Case 2 Recurrence-State Interface Review

Date: 2026-06-19.

Scope: xhigh review/exploration of a narrow recurrence-state interface after
the introduced-label finite-domain bridge.

## Reviewers

- Source/pen-and-paper reviewer: `Averroes the 2nd`.
- Lean/API reviewer: `Pauli the 2nd`.

## Verdict

The interface is appropriate only as a thin package of recurrence data. The
source supports naming:

- active domain `introducedLabelFinset`,
- Nat-valued recurrence levels `level`,
- variables `var`,
- derived recurrence factors `step`,
- derived row weights `weight`.

The Lean/API review recommends keeping `step` and `weight` derived from
`level`, `var`, and `introducedLabelFinset`; do not store them as independent
fields because that would add coherence obligations without proving more source
mathematics.

Follow-up API tightening: the least-value gap bridge now uses the equality-only
`IntroducedLabelLevelInvariants`; the stronger level/tail package extends it,
but its flat-tail field is not required for Case 2 gap conversion.

## Required Caveats

- This does not prove that Aoyagi's transition produces the state.
- This does not prove the Case 2 gap.
- This does not prove source comparability; the Case 2 label gap alone is not
  enough for the source's comparability sentence.
- This does not resolve the printed Case 2 vector mismatch or the
  `b'_i`/standalone-`u` normalization ambiguity.
- This is not a chart coverage, Jacobian, exponent update, termination,
  normal-crossing, or RLCT theorem.

## Checks

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`:
  passed.
- From `lean/`: `lake build DLNFibre`: passed.
- From `lean/`: `./scripts/sorries`: `0 sorry`, `0 #exit`,
  `0 native_decide`, `0 axiom`.
- From worktree root: `git diff --check`: passed.
