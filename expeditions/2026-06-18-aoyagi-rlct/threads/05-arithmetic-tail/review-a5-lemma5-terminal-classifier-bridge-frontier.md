# Review - A5 Lemma 5 terminal-classifier bridge frontier

Reviewer: Herschel, xhigh source/API audit.
Date: 2026-07-02.

Verdict: pass for a construction/obstruction card; fail for attempting a Lean
discharge from Aoyagi alone at the current frontier.

## Findings

No blocking findings against the new frontier packet.

The reviewer confirmed that the current Lean layer only has supplied-boundary
wrappers.  A terminal counted-datum classifier requires a `classify` function,
a `mapsTo` proof into `aoyagiLemma5CountDatumSet`, and injectivity on
`TC.terminalMinimumLabels`.  Aoyagi pp. 24-27 do not currently supply such a
source-backed function on arbitrary terminal-minimum labels.

For `TC.UpperBoundClassifier`, the missing field is the no-extra direction:
for every label in `TC.terminalMinimumLabels`, produce a branch in
`TC.fullBranches` with the same `TC.branchLabel`.  For the stronger
back-to-label bridge, the branch must also have counted datum equal to the
classifier value.

The reviewer also confirmed the main source obstructions:

- Lemma 4 is sufficient, not a converse.
- The Case 1(2) sentence that `J` is increased by one is not an injectivity
  theorem.
- Displayed families `(3)`--`(5)` are not currently safe as a complete source
  construction.  Existing notes record guard, endpoint, and increment
  obstructions for `(3)` and `(4)`, while Eq5 is represented in Lean as
  supplied piecewise payload data rather than an existence/exhaustiveness
  theorem.

## Recommendation

Keep the A5 packet as a construction/frontier specification.  Do not add a
new Lean theorem unless it removes a concrete supplied field.  A future source
proof must first provide the explicit bridge fields named in the construction
card: label-to-source-vector, minimum-to-lambda, counted-datum maps-to,
counted-datum injectivity, back-to-label/no-extra, and branch-label
injectivity.

## Nonclaims

This review does not prove the classifier, injectivity, no-extra coverage,
back-to-label bridge, Lemma 5 order count, pole order, normal crossings, or
RLCT extraction.
