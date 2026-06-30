# Review - A4 Case 1(2) row-strip progress bridge

Date: 2026-06-30.

Status: PASS.

## Scope Reviewed

- `lean/DLNFibre/DLN/Aoyagi/BlowupBranchProgress.lean`
- `threads/04-blow-up-certificate/reproduction-a4-case1-rowstrip-progress-bridge.md`
- `threads/04-blow-up-certificate/statement-card-a4-case1-rowstrip-progress-bridge.md`

## Source/Scope Review

Reviewer: `Wegener`.

Verdict: PASS.  The review was read-only and found no source/scope blockers.

The reviewer confirmed that the new theorem is narrowly conditional on
`Case1DisplayedRowStripJIncrementPayload` and proves only the finite
introduced-label progress step `(S,J) -> (S,J+1)`.  It uses only the payload's
actual-width proof for `(S,J+1)`, not chart/source/RLCT data.

The consumed payload is already scoped as finite Case 1(2) `J`-advance
bookkeeping and explicitly excludes chart construction, coverage, transition
invariance, Jacobians, normal crossings, and RLCT.  Its fields are finite
bounds/domain/exponent-certificate facts only.

The reviewer also checked that the docs correctly exclude Case 1(1) and
stronger analytic claims.  This matches Aoyagi's Case 1 split: Case 1(1) is
same-domain selected-old lowering, while Case 1(2) factors through
`u_(S,J+1)` and then continues with `J` increased by one under the non-strict
guard.

Non-blocking note: in local PDF extraction, the final "inductive statement
with `J` increased by one" sentence lands on physical PDF p. 19 after the
p. 18 display.  Existing Case 1 J-increment docs already cite this as p. 18,
so this inherited pagination convention is not treated as a blocker.

## Lean/API Review

Reviewer: `Euler`.

Verdict: PASS.  The review was read-only and found no blocking Lean/API
findings.

The reviewer confirmed:

- `progressStep_sameStage_increment` asks only for the state bounds and
  `J+1 <= n(S+1)`, exactly the actual-width side needed for the fresh label.
- The payload bridge is an appropriate case-specific API bridge from
  `Case1DisplayedRowStripJIncrementPayload` to `progressStep`; it intentionally
  uses only `payload.newLabelActualWidth`.
- Extracting `1 <= S`, `S <= L`, and `J+1 <= n(S+1)` from
  `payload.newLabelActualWidth` is sound because `actualWidthLabel` is defined
  as `1 <= s`, `s <= L`, `1 <= k`, and `k <= n(s+1)`.
- The theorem is non-vacuous because the underlying support-growth proof
  witnesses the fresh label `(S,J+1)` as absent before and present after.
- Reusing the old `progressStep_case2_increment` theorem through the generic
  alias is sound.  A future cleanup could make the generic theorem primitive
  and the Case 2 theorem an alias, but this is not a blocker.

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
env LEAN_NUM_THREADS=3 lake env lean -E warning /tmp/aoyagi_case1_rowstrip_progress_axioms.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre
```

The focused build, direct warning check, axiom probe, and full local build
passed.  The full build replayed pre-existing warnings in unrelated modules;
the direct warning check for `BlowupBranchProgress.lean` was clean.

The axiom probe for

```text
AoyagiIntroducedLabelBranchState.progressStep_sameStage_increment
AoyagiIntroducedLabelBranchState.progressStep_case1DisplayedRowStrip_jIncrementPayload
```

reported only `[propext, Classical.choice, Quot.sound]`.
