# Review - A4 displayed Case 2 branch progress

Date: 2026-06-30.

Status: PASS.

## Scope Reviewed

- `lean/DLNFibre/DLN/Aoyagi/BlowupBranchProgress.lean`
- `threads/04-blow-up-certificate/reproduction-a4-case2-displayed-branch-progress.md`
- `threads/04-blow-up-certificate/statement-card-a4-case2-displayed-branch-progress.md`

## Source/Scope Review

Reviewer: `Mill`.

Verdict: PASS.  The review was read-only and found no concrete source/scope
issues.

The reviewer checked that Aoyagi PDF pp. 19-22 support the displayed Case 2
residual block, selected pivot, post-pivot block `D_{J+1}`, and same-stage
continuation `J -> J+1`.  In old-state notation, the next continuation guard is
correctly recorded as:

```text
J+2 <= M(S+1)
```

The stopped split into

```text
n(S+1)=J+1
M(S)=J+1
```

is finite arithmetic from `M(S+1)=min(M(S), n(S+1))`, not extra source
production.

The review confirmed that the Lean slice only names the guards, proves guard
completeness via the existing finite-frontier theorem, and proves
introduced-label progress for `(S,J) -> (S,J+1)`.  The docs explicitly deny
source-production payloads, branch termination, guard exclusivity, normal
crossings, pole order, and RLCT.

## Lean/API Review

Reviewer: `Curie`.

Verdict: PASS.  The review found no Lean/API issues.

Checks:

- The target definitions and theorems compile and keep theorem boundaries
  narrow.
- Guard completeness delegates to the existing frontier theorem with matching
  disjunction order.
- The progress lemmas only prove `progressStep` for `(S,J) -> (S,J+1)`.
- The module stays below `SelectedEntryBranchTerminationData`; it imports only
  `BlowupArithmetic`, with no selected-entry producer import.
- Reproduction and statement card nonclaims match the Lean surface.
- `lake build DLNFibre.DLN.Aoyagi.BlowupBranchProgress` passes from the local
  Lake package root `lean/`.

## Controller Verification

The controller ran, using local `lake` rather than `scripts/lb`:

```text
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.BlowupBranchProgress
env LEAN_NUM_THREADS=3 lake env lean -E warning DLNFibre/DLN/Aoyagi/BlowupBranchProgress.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre
lean/scripts/sorries
git diff --check
env LEAN_NUM_THREADS=3 lake env lean -E warning /tmp/aoyagi_branch_progress_axioms.lean
```

The focused build, direct warning check, full build, no-sorry audit, whitespace
check, and axiom probe passed.  The full build replayed pre-existing warnings
in unrelated modules; the direct warning check for `BlowupBranchProgress.lean`
was clean.

The new public declarations

```text
AoyagiIntroducedLabelBranchState.case2Displayed_frontier_guards_complete
AoyagiIntroducedLabelBranchState.case2SameStageChild_progress_of_prefixBound
AoyagiIntroducedLabelBranchState.case2SameStageChild_progress_of_continuingGuard
```

reported only the usual Lean/classical axiom footprint.

## Boundary

This review accepts only the displayed Case 2 branch-progress bridge.  It does
not certify source-production payloads, does not make stopped branches
exclusive, does not fill `SelectedEntryBranchTerminationData`, and does not
prove normal crossings, pole order, or RLCT.
