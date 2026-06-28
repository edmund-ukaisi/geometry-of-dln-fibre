# Review - A2 Case 2 explicit selected-entry source-family regularity

Date: 2026-06-28.

Reviewer: xhigh `Gibbs`.

Verdict: PASS.  No blocking findings.

## Findings

The new theorem names match their statements and proof scope:

- `continuous_case2SuccessorSelectedEntryMatrix` proves continuity of
  `yNext |-> case2SuccessorSelectedEntryMatrix ... yNext eNext`, entrywise via
  `SelectedEntrySignedBox.CenterCoord.continuous_chartMap`.
- `continuous_case2PostPivotSelectedEntryRetainedPassiveData` proves
  continuity of the constructed retained-passive datum only.
- `continuous_case2PostPivotSelectedEntryRetainedPassiveData_detChart_subtype`
  is the determinant-chart subtype version using the already-proved membership.
- `continuous_case2PostPivotSelectedEntrySourceEdgeFamily` composes that
  subtype map with existing retained-passive `edgeMatrix` continuity.
- `measurable_case2PostPivotSelectedEntrySourceEdgeFamily` follows from
  continuity.

The reviewer found no hidden nonzero-pivot hypothesis and no hidden
source-prior pushforward, Jacobian/density transport, arbitrary coverage,
normal-crossing, pole-order, or RLCT claim.

The reproduction and statement card are faithful: they frame the result as
finite-coordinate continuity/measurability and explicitly defer pushforward,
Jacobian, coverage, normal crossings, pole order, and RLCT.

## Controller Verification

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2SelectedEntryChartBridge` passed.  Full
`DLNFibre` build passed.  `scripts/sorries`, `git diff --check`, and
touched-Lean-file forbidden-marker search were clean.  Direct axiom-footprint
probes for the five new endpoints reported
`[propext, Classical.choice, Quot.sound]`.

