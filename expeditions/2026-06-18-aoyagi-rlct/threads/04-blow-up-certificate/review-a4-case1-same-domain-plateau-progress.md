# Review - A4 Case 1(1) same-domain plateau progress

Date: 2026-06-30.

Status: PASS.

## Scope Reviewed

- `lean/DLNFibre/DLN/Aoyagi/BlowupBranchProgress.lean`
- `threads/04-blow-up-certificate/reproduction-a4-case1-same-domain-plateau-progress.md`
- `threads/04-blow-up-certificate/statement-card-a4-case1-same-domain-plateau-progress.md`

## Scout Confirmation

Source/pen-and-paper scout: `Sagan`.

Verdict: supports the implemented target.  The scout identified the correct
Case 1(1) measure as the old-plateau count

```text
(introducedLabelFinset L n S J).filter
  (fun p => level p.1 p.2 = J+J1)
```

and recommended proving that `case1SelectedOldLevelMove` erases `(s0,k0)` from
that plateau.  The scout also confirmed that Case 1(1) should not be treated as
introduced-label support growth.

Lean/API scout: `Archimedes`.

Verdict: supports the implemented target.  The scout recommended consuming
`IntroducedLabelRecurrenceState.Case1SelectedOldLevelMoveData`, because it
contains selected membership, selected pre/post levels, and unchanged
non-selected levels.  The scout also recommended the above-pivot set as the
more useful same-domain Nat-valued progress measure.

## Source/Scope Review

Reviewer: `Boole`.

Verdict: PASS.  The review was read-only and found no source/scope findings.

The reviewer confirmed that the new definitions stay over the fixed same-domain
`(S,J)` introduced-label finset and prove selected-old lowering/erasure from
the `J+J1` plateau and from the above-pivot set, with strict count decrease.
The underlying API matches the intended source boundary: first-jump data supply
positivity and selected level, while `Case1SelectedOldLevelMoveData` records
same-domain selected lowering and unchanged non-selected introduced labels.

The reviewer also inspected the expedition docs and confirmed their nonclaim
boundaries: no Case 1(2), no support-growth claim, no chart/source
construction, no normal-crossing, pole-order, or RLCT claim.

The reviewer ran:

```text
git diff --check
lake env lean DLNFibre/DLN/Aoyagi/BlowupBranchProgress.lean
```

and both passed.

## Lean/API Review

Reviewer: `Arendt`.

Verdict: PASS.  The review was read-only and found no Lean/API findings.

The reviewer confirmed that the core erasure/progress lemmas correctly consume
`Case1SelectedOldLevelMoveData`; the same-domain wrappers only build that move
data and supply `firstJump.positive`.  The reviewer specifically noted that
using lower recurrence boundaries here would be too weak, since those expose
step equalities rather than the per-label level preservation needed for exact
finset erasure.

The reviewer ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/BlowupBranchProgress.lean
```

and it passed.

## Controller Verification

The controller ran, using local `lake` rather than `scripts/lb`:

```text
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.BlowupBranchProgress
lake env lean -E warning DLNFibre/DLN/Aoyagi/BlowupBranchProgress.lean
env LEAN_NUM_THREADS=3 lake env lean -E warning /tmp/aoyagi_case1_plateau_progress_axioms.lean
```

The focused build, direct warning check, and direct axiom probe passed.  The
axiom probe for the new plateau and above-pivot progress declarations reported
only `[propext, Classical.choice, Quot.sound]`.

## Nonclaim Boundary

This slice proves no chart construction, no source-production payload, no
Case 1(2) progress theorem, no introduced-label support growth, no full
branch termination, no normal crossings, no pole order, and no RLCT.
