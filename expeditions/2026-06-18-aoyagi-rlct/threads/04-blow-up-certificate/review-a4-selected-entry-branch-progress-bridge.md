# Review - A4 selected-entry branch progress bridge

Date: 2026-06-30.

Status: PASS.

## Scope Reviewed

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryAnalyticAtlasProducer.lean`
- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryBranchProgressBridge.lean`
- `lean/DLNFibre.lean`
- `threads/04-blow-up-certificate/reproduction-a4-selected-entry-branch-progress-bridge.md`
- `threads/04-blow-up-certificate/statement-card-a4-selected-entry-branch-progress-bridge.md`

## Source/Scope Review

Reviewer: `Turing`.

Verdict: PASS.  The review was read-only and found no source/scope findings
requiring changes.

The reviewer confirmed that the revised API keeps
`SelectedEntryAtlasProducedBranchData` as source-production data only: it has
no `continuingChild` field.  The child/step data lives separately in
`SelectedEntryAtlasBranchProgressData`, which assumes supplied source
production and supplied termination, records active-guard coverage, and gives
a decreasing child only for `continuingGuard`.  Stopped branches get no child.

The reviewer checked that the Case 2 bridge stays within Aoyagi PDF pp. 19-22.
It defines active pivot validity as

```text
J+1 <= prefixMinNat n (S+1)
```

supplies only the finite introduced-label termination relation, and assumes
guard coverage plus either pivot validity or the displayed continuing guard
before choosing `(S,J+1)` as the continuing child.

The reviewer also confirmed that the docs match the separate-layer design and
explicitly disclaim source production, terminal rows, suffixes, chart domains,
coverage, transition regularity, normal crossings, pole order, RLCT,
stopped-guard exclusivity, and fake stopped-branch children.

Case 1(1) is not repackaged as support-growth progress.  The current slice has
only Case 2-named progress constructors, while prior Case 1(1) notes keep it
as same-domain lower-tail/old-plateau progress.

## Lean/API Review

Reviewer: `Kepler`.

Verdict: PASS.  The review was read-only and found no blocking Lean/API
findings.

The reviewer confirmed:

- `SelectedEntryAtlasProducedBranchData` is unchanged; no `continuingChild`
  was added, so existing constructors are not broken.
- `SelectedEntryAtlasBranchProgressData` has the right separate-layer shape:
  it consumes supplied source production and supplied termination, adds
  `activeGuard`, active-region guard coverage, and a child/step proof only
  for continuing branches.
- The Case 2 active guard is named accurately and is exactly pivot validity:

```text
s.J + 1 <= prefixMinNat n (s.S + 1)
```

- The prefix-bound bridge requires active-guard coverage plus
  `continuingGuard -> pivot-validity` and selects the same-stage child.
- The continuing-guard bridge requires active-guard coverage plus
  `continuingGuard -> case2DisplayedContinuingGuard` and derives the weaker
  prefix bound.
- No universe, typeclass, or import concerns were found.

The reviewer reran local checks from `lean/`:

```text
lake env lean DLNFibre/DLN/Aoyagi/SelectedEntryAnalyticAtlasProducer.lean
lake env lean DLNFibre/DLN/Aoyagi/SelectedEntryBranchProgressBridge.lean
lake build DLNFibre.DLN.Aoyagi.SelectedEntryBranchProgressBridge
lake env lean DLNFibre.lean
```

All passed.

## Controller Verification

So far the controller ran, using local `lake` rather than `scripts/lb`:

```text
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.SelectedEntryBranchProgressBridge
lake env lean -E warning DLNFibre/DLN/Aoyagi/SelectedEntryAnalyticAtlasProducer.lean
lake env lean -E warning DLNFibre/DLN/Aoyagi/SelectedEntryBranchProgressBridge.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre
lean/scripts/sorries
git diff --check
env LEAN_NUM_THREADS=3 lake env lean -E warning /tmp/aoyagi_selected_entry_branch_progress_axioms.lean
```

The focused build, direct warning checks, full build, no-sorry audit, and
whitespace check passed.  The full build replayed pre-existing warnings in
unrelated modules; the direct warning checks for the touched modules were
clean.

The axiom probe for

```text
selectedEntryIntroducedLabelBranchTerminationData
selectedEntryCase2DisplayedPrefixBoundBranchProgressData
selectedEntryCase2DisplayedContinuingBranchProgressData
```

reported only `[propext, Classical.choice, Quot.sound]`.
