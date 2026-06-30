# Review - A4 introduced-label progress kernel

Date: 2026-06-29.

Status: PASS.

## Scope Reviewed

- `lean/DLNFibre/DLN/Aoyagi/BlowupBranchProgress.lean`
- `threads/04-blow-up-certificate/reproduction-a4-introduced-label-progress-kernel.md`
- `threads/04-blow-up-certificate/statement-card-a4-introduced-label-progress-kernel.md`

## Source/Scope Review

Reviewer: `Pauli the 4th`.

Verdict: PASS.  The source/scope review found no required wording fixes and
made no edits.

The review checked that Aoyagi PDF pp. 19-22 support only the narrow Case 2
bookkeeping claim used here: under the displayed continuation bound, the
inductive state advances from `(S,J)` to `(S,J+1)`.  The finite
`actualWidthLabelFinset`, `introducedLabelFinset`, and `remaining` measure are
correctly presented as expedition bookkeeping, not as source-produced by
Aoyagi.

The review also confirmed the nonclaim boundary: this slice proves no
source-production theorem, no all-branch Case 1/Case 2 termination theorem, no
selected-entry atlas producer branch-termination field, no normal crossings, no
pole order, and no RLCT extraction.

## Lean/API Review

Reviewer: `Chandrasekhar the 4th`.

Verdict: PASS.  The reviewer found no Lean/API soundness issues and made no
edits.

Checks:

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupBranchProgress.lean` exited 0.
- `lake env lean DLNFibre.lean` exited 0.
- The import is present in `lean/DLNFibre.lean`.
- The progress relation is scoped to fixed `L n` branch states and measures
  only `remaining L n child < remaining L n parent`.
- Well-foundedness is by inverse image into `Nat.lt_wfRel`.
- Case 2 increment strictness is monotone support inclusion plus the fresh
  witness `(S,J+1)`.
- The prefix-bound wrapper uses `prefixMinNat_le_width`.
- The file does not fill `SelectedEntryBranchTerminationData`; the all-pivot
  producer shell still takes termination as an explicit input.

## Replacement Lean/API Review

Reviewer: `Rawls the 4th`.

Verdict: PASS.  This replacement review was spawned after the original reviewer
was slow to return; it also found no concrete file/line issues and made no
edits.

Checks:

- Focused local `lake build DLNFibre.DLN.Aoyagi.BlowupBranchProgress` passed.
- Public names checked.
- Representative axiom probes showed only the usual Lean/classical axioms.
- The target Lean file contains no `sorry`, `admit`, `axiom`, `unsafe`,
  `native_decide`, or `#exit`.
- The docs keep the nonclaims explicit.

## Controller Verification

The controller independently ran, using local `lake` rather than `scripts/lb`:

```text
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.BlowupBranchProgress
env LEAN_NUM_THREADS=3 lake env lean -E warning DLNFibre/DLN/Aoyagi/BlowupBranchProgress.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre
lean/scripts/sorries
git diff --check
```

The focused build, direct warning check, full build, no-sorry audit, and
whitespace check passed.  The full build replayed pre-existing warnings in
other modules; the direct warning check for `BlowupBranchProgress.lean` was
clean.

Direct axiom probes for

```text
AoyagiIntroducedLabelBranchState.progressStep_wellFounded
AoyagiIntroducedLabelBranchState.support_ssubset_case2_increment
AoyagiIntroducedLabelBranchState.progressStep_case2_increment
AoyagiIntroducedLabelBranchState.progressStep_case2_increment_of_prefixBound
```

reported only `[propext, Classical.choice, Quot.sound]`.

## Boundary

This review accepts the progress kernel as a finite termination kernel only.
It does not certify that the constructed branch-source payloads satisfy the
progress relation, does not prove branch guard exhaustiveness, and does not
fill `SelectedEntryBranchTerminationData`.
