# Review - A4 recurrence-aware Case 2 branch progress

Date: 2026-06-30.

Status: PASS.

## Scope For Review

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryBranchProgressBridge.lean`
- `threads/04-blow-up-certificate/reproduction-a4-recurrence-case2-branch-progress.md`
- `threads/04-blow-up-certificate/statement-card-a4-recurrence-case2-branch-progress.md`

## Source/Scope Review

Reviewer: `Avicenna`.

Verdict: PASS.  The review was read-only and found no source/scope findings.

The reviewer confirmed that the recurrence-aware bridge keeps child
recurrence data supplied and uses it directly in the continuing child.  The
source-production data, guard coverage, and prefix bound are all inputs, not
constructed.  The continuing-guard adapter only derives the displayed prefix
bound from a supplied guard and delegates to the prefix-bound adapter.

The reviewer also checked the reproduction and statement card and confirmed
that they preserve the supplied-data boundary and explicitly exclude
recurrence construction, source-production, terminal payloads, charts, normal
crossings, pole order, and RLCT.

The reviewer ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/SelectedEntryBranchProgressBridge.lean
```

and it passed.

## Lean/API Review

Reviewer: `Bernoulli`.

Verdict: PASS.  The review was read-only and found no Lean/API findings.

The reviewer confirmed that `childRecurrence` is indexed as

```text
IntroducedLabelRecurrenceState L n s.S (s.J + 1) alpha
```

matching `AoyagiRecurrenceBranchState.sameStageChildWithRecurrence`; that
`continuingChild` is definitionally the intended
`sameStageChildWithRecurrence s (childRecurrence s h)`; and that
`continuing_child_step` reduces through
`selectedEntryRecurrenceBranchTerminationData` to
`sameStageChildWithRecurrence_progress_of_prefixBound`.

The reviewer ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/SelectedEntryBranchProgressBridge.lean
```

and it passed.

## Controller Verification

The controller ran:

```text
lake env lean -E warning DLNFibre/DLN/Aoyagi/SelectedEntryBranchProgressBridge.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.SelectedEntryBranchProgressBridge
env LEAN_NUM_THREADS=3 lake build DLNFibre
lean/scripts/sorries
git diff --check
env LEAN_NUM_THREADS=3 lake env lean -E warning /tmp/aoyagi_recurrence_case2_branch_progress_axioms.lean
```

The direct warning check, focused local build, full local build, no-sorry
audit, whitespace check, and axiom probe passed.  The two new declarations
report only `[propext, Classical.choice, Quot.sound]`.

The full local build completed with pre-existing unrelated warnings in other
modules.

## Nonclaim Boundary

This bridge constructs no recurrence data, source-production payloads, branch
guards, terminal payloads, chart construction, analytic atlas fields, normal
crossings, pole order, or RLCT.
