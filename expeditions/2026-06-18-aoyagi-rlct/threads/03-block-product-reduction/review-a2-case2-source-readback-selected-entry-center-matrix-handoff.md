# Review - A2 Case 2 source-readback selected-entry center-matrix handoff

Date: 2026-06-28.

Reviewer: xhigh `Galileo`.

Verdict: PASS.  No blocking findings.

## Findings

The theorem
`case2PostPivotSelectedEntrySourceReadback_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix`
is a faithful exact-shape rewrite.  It uses the existing theorem
`case2PostPivotSelectedEntrySourceReadback_residualFactorProduct_eq_successorSelectedEntryMatrix`
and proves the new statement by unfolding `case2SuccessorSelectedEntryMatrix`.
The unfolded right-hand side matches the definition of
`case2SuccessorSelectedEntryMatrix`.

The documentation and ledger entries stay within scope.  They frame the result
as a finite readback equality and explicitly disclaim local-measure theorem,
source-prior pushforward, chart-image membership, Jacobian density comparison,
coverage, normal crossings, pole order, and RLCT.

## Controller Verification

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2SelectedEntryChartBridge` passed.
`scripts/sorries`, `git diff --check`, and touched-Lean-file forbidden-marker
search were clean.  Direct axiom-footprint probe for the new endpoint reported
`[propext, Classical.choice, Quot.sound]`.

