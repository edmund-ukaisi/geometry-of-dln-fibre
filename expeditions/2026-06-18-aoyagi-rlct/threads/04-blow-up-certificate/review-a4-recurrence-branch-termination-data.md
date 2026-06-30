# Review - A4 recurrence branch termination data

Date: 2026-06-30.

Status: PASS.

## Scope For Review

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryBranchProgressBridge.lean`
- `threads/04-blow-up-certificate/reproduction-a4-recurrence-branch-termination-data.md`
- `threads/04-blow-up-certificate/statement-card-a4-recurrence-branch-termination-data.md`

## Source/Scope Review

Reviewer: `Russell`.

Verdict: PASS.  The review was read-only and found no source/scope findings.

The reviewer confirmed that the Lean adapter only fills
`SelectedEntryBranchTerminationData` fields with the existing recurrence-aware
`progressStep`, its well-foundedness proof, and an initial state using
supplied `initialRecurrence`.  It does not construct recurrence data or any
branch/source/terminal payloads.

The reviewer also checked the reproduction and statement card and confirmed
that they explicitly exclude source production, branch guards, terminal
payloads, full analytic-atlas branch termination, normal crossings, pole
order, and RLCT.

The reviewer ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/SelectedEntryBranchProgressBridge.lean
```

and it passed.

## Lean/API Review

Reviewer: `Ohm`.

Verdict: PASS.  The review was read-only and found no Lean/API findings.

The reviewer confirmed that the exported signature is universe-polymorphic over
`Param`, `R`, and `alpha`; the initial state constructor matches
`AoyagiRecurrenceBranchState` field order and the dependent recurrence fiber;
`step` is definitionally `AoyagiRecurrenceBranchState.progressStep L n alpha`;
and `step_wellFounded` has the matching well-founded target.  The adapter is
API-parallel to `selectedEntryIntroducedLabelBranchTerminationData`, with the
only extra required data being the initial recurrence payload.

The reviewer ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/SelectedEntryBranchProgressBridge.lean
```

and it passed.

## Controller Verification

The controller ran:

```text
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.SelectedEntryBranchProgressBridge
lake env lean -E warning DLNFibre/DLN/Aoyagi/SelectedEntryBranchProgressBridge.lean
env LEAN_NUM_THREADS=3 lake env lean -E warning /tmp/aoyagi_recurrence_branch_termination_axioms.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre
lean/scripts/sorries
git diff --check
```

The focused build, direct warning check, axiom probe, full local build,
no-sorry audit, and whitespace check passed.  The axiom probe reported only
`[propext, Classical.choice, Quot.sound]`.

The full local build completed with pre-existing unrelated warnings in other
modules.

## Nonclaim Boundary

This adapter constructs no recurrence data, source-production payloads, branch
guards, continuing children, terminal payloads, chart construction, full
analytic-atlas branch termination theorem, normal crossings, pole order, or
RLCT.
