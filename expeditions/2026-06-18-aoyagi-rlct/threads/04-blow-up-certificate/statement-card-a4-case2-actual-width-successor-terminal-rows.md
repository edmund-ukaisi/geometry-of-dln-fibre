# Statement card - A4 Case 2 actual-width successor terminal rows

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Name:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.sourceChart_actualWidth_terminalOriginalRowsSuccFollowingSuppliedSuffixBoundary`

## Statement

In the actual next-width exhausted Case 2 branch, restate the supplied-`F`
terminal boundary with terminal rows written as original rows of the
formula-level successor following factor `Csucc`.

## Proved

The existing actual-width terminal boundary has terminal rows
`case2DisplayedSourceTerminalOriginalRows C`.  Since actual next-width
exhaustion gives `case2DisplayedSourceSuccessorFollowingFactor ... C = C`,
the same boundary holds with
`case2DisplayedSourceTerminalOriginalRows Csucc`.

## Assumed

- Displayed Case 2 hypotheses.
- Actual next-width exhaustion `n(S+1)=J+1`.
- The same supplied chart-family boundary and pre-state certificates as the
  existing actual-width supplied-following boundary.
- A supplied following matrix `F`.

## Cited

- None in Lean.  This is finite equality rewriting.

## Deferred

- Source-suffix, identity-following, finite-center, and frontier-package
  variants.
- Source/chart production of `Csucc`, `F`, source suffixes, old-top rows, full
  successor `C'^(S+1)`, successor chart-family data, chart coverage,
  transition invariance, Jacobian arithmetic, normal crossings, pole order,
  termination, and RLCT extraction.

## Review

- xhigh `Aristotle` passed the theorem as useful but very small API alignment
  and recommended adding only the arbitrary supplied-`F` theorem.

## Verification

- `cd lean && lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` passed.
- `cd lean && lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic` passed.
- `cd lean && lake build DLNFibre` passed, with only pre-existing Core
  warnings.
- `cd lean && scripts/sorries` reported
  `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
- `git diff --check` passed.
