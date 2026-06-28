# Review - A2 Case 2 constructed source-readback production

Date: 2026-06-28.

Reviewer: xhigh `Boole`.

Verdict: PASS.  No blocking findings.

## Findings

The review found the Lean theorem sound at its narrow scope.  The construction
chooses `residual` and `Cprime`, packages them as
`case2PostPivotRetainedPassiveData`, proves `data.detChart`, and uses
`sourceRecursiveDetChart_edgeMatrix_of_detChart` plus
`sourceReadback_edgeMatrix_eq` to identify the actual source readback of
`data.edgeMatrix` with `data`.  The product and nonzero claims are transported
from the already constructed `case2PostPivotFreeTwoEdgeFactorFamily` theorem.

The orientation is correct: `case2PostPivotFreeTwoEdgeFactorFamily` sets
`C 0` to the free following factor and `C 1` to the post-pivot residual block,
and the two-edge residual-factor product is `C 1 * C 0`.

The scope is correctly fenced as constructed source production only.  It does
not claim arbitrary retained-passive source/readback factor alignment,
source/prior transport, normal crossings, pole order, or RLCT.

## Follow-Up Fix

The reviewer noted one wording issue: the Lean docstring called
`sourceReadback_edgeMatrix_eq` a right-inverse theorem.  The docstring was
changed to "readback-after-source inverse theorem" before banking.

Controller verification after the wording fix: focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2SelectedEntryChartBridge`, full
`DLNFibre` build, `scripts/sorries`, `git diff --check`, changed-Lean-file
forbidden-marker search, and direct `#print axioms` audits passed.  The new
endpoints report `[propext, Classical.choice, Quot.sound]`.
