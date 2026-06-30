# Review - A4 combined recurrence branch progress

Date: 2026-06-30.

Status: PASS.

## Scope For Review

- `lean/DLNFibre/DLN/Aoyagi/BlowupBranchProgress.lean`
- `threads/04-blow-up-certificate/reproduction-a4-combined-recurrence-branch-progress.md`
- `threads/04-blow-up-certificate/statement-card-a4-combined-recurrence-branch-progress.md`

## Source/Scope Review

Reviewer: `Heisenberg`.

Verdict: PASS.  The review was read-only and found no source/scope findings.

The reviewer confirmed that the Lean slice keeps the combined measure as
finite bookkeeping.  The Case 1(1) same-domain component is supported by the
above-pivot descent theorem and then combined into
`AoyagiRecurrenceBranchState`; the Case 1(2)/Case 2 same-stage payload
wrappers are support-growth statements; and the stage handoff is explicitly
phrased with supplied recurrence data only.

The reviewer also checked the reproduction and statement card nonclaim
boundaries and found no claim of source production, chart construction, full
analytic-atlas termination, normal crossings, pole order, or RLCT.

The reviewer ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/BlowupBranchProgress.lean
```

and it passed.

## Lean/API Review

Reviewer: `Ptolemy`.

Verdict: PASS.  The review was read-only and found no Lean/API soundness
findings.

The reviewer checked the dependent `(S,J)` recurrence state, weighted Nat
measure, `toIntroducedState` projection, stage handoff, and Case 1/Case 2
payload wrappers.  The statements were judged non-vacuous: same-stage progress
depends on actual-width validity, stage handoff uses finite-domain monotonicity
plus strict stage-budget decrease, and same-domain Case 1 progress is tied to
the above-pivot count decrease.

The reviewer ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/BlowupBranchProgress.lean
git diff --check
```

and checked the target Lean file for `sorry`/`admit`/`axiom`/`unsafe`; no
issues were found.

## Controller Verification

The controller has run:

```text
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.BlowupBranchProgress
lake env lean -E warning DLNFibre/DLN/Aoyagi/BlowupBranchProgress.lean
env LEAN_NUM_THREADS=3 lake env lean -E warning /tmp/aoyagi_combined_recurrence_progress_axioms.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre
lean/scripts/sorries
git diff --check
```

The focused build, direct warning check, axiom probe, full local build,
no-sorry audit, and whitespace check passed.  The axiom probe for the new
combined recurrence progress declarations reported only
`[propext, Classical.choice, Quot.sound]`.

The full local build completed with pre-existing unrelated warnings in other
modules.

## Nonclaim Boundary

This slice proves no source-production payloads, branch-guard coverage,
terminal payloads, full analytic-atlas branch termination theorem, normal
crossings, pole order, or RLCT.
