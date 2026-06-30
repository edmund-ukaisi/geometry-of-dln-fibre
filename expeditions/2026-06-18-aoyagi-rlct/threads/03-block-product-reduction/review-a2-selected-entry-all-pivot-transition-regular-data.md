# Review - A2 selected-entry all-pivot transition regular data

Date: 2026-06-29.

## Verdict

PASS after documentation repair.

## Scope Reviewed

Lean:

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntryAllPivotTransitionRegularData.lean
lean/DLNFibre.lean
```

Artifacts:

```text
reproduction-a2-selected-entry-all-pivot-transition-regular-data.md
statement-card-a2-selected-entry-all-pivot-transition-regular-data.md
```

## Source/Scope Review

Reviewer: Erdos the 4th, xhigh.

Initial verdict: one concrete documentation finding.

The reviewer found that the initial reproduction and statement card
over-attributed the all-pivot transition/renormalization to Aoyagi PDF
pp. 15-22.  The Lean transition comes from the repo's finite selected-entry
overlap algebra: `sourceChartTransitionPoint` and
`chartMap_sourceChartTransitionPoint_eq_of_target_normalized_ne_zero`.
Aoyagi supports the chosen-pivot selected-entry substitution; the all-pivot
transition record is expedition-built finite overlap bookkeeping over those
existing lemmas.

Repair: the reproduction and statement card now state exactly that source
boundary.

Final recheck: PASS.  The prior over-attribution finding is resolved.

The reviewer also confirmed that the Lean slice itself is scope-honest: the
domain is exactly `{denom != 0}`, and chart-map preservation consumes the same
nonzero-denominator hypothesis.

Erdos independently checked:

```text
lake env lean DLNFibre/DLN/Aoyagi/SelectedEntryAllPivotTransitionRegularData.lean
```

The direct Lean check passed.

## Lean/API Review

Reviewer: Confucius the 4th, xhigh.

Verdict: PASS.  No concrete findings.

The reviewer checked that:

- the shared all-pivot context is used in
  `selectedEntryAllPivotAnalyticTransitionRegularData`;
- `transitionDomain` is exactly the normalized target-coordinate nonzero
  locus;
- `transitionMap` is the finite selected-entry division formula;
- the continuity proof decomposes product/pi continuity and divides only on
  the transition domain;
- chart-map preservation invokes the finite preservation lemma with the same
  nonzero hypothesis;
- no new global simp attributes, `unsafe`, `axiom`, `admit`, or `sorry` occur
  in the reviewed module;
- the aggregator import is appended in `lean/DLNFibre.lean`.

Confucius independently checked:

```text
lake env lean DLNFibre/DLN/Aoyagi/SelectedEntryAllPivotTransitionRegularData.lean
lake env lean DLNFibre.lean
```

Both passed.  The exported predicate axiom probe reported only
`[propext, Classical.choice, Quot.sound]`.

## Controller Verification

Controller local checks:

```text
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.SelectedEntryAllPivotTransitionRegularData
env LEAN_NUM_THREADS=3 lake env lean -E warning DLNFibre/DLN/Aoyagi/SelectedEntryAllPivotTransitionRegularData.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre
lean/scripts/sorries
git diff --check
```

The focused build, warning-level direct Lean check, full local `DLNFibre`
build, zero-sorry scan, and whitespace check passed.  The full build emitted
only pre-existing replay warnings from other modules.  The direct axiom probe
for both new public declarations reported only
`[propext, Classical.choice, Quot.sound]`.

## Nonclaims

No source production, branch termination, source-prior transport,
determinant-chart Haar transport, full supplied analytic atlas producer,
normal-crossing extraction, pole order, or RLCT is proved.
