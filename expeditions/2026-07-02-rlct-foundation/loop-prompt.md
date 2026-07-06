# Loop prompt — `rlct-foundation` controller tick

Run ONE controller tick per invocation. Operate from `.claude/worktrees/rlct` on
`expedition/rlct-foundation`. **Careful: many other expeditions run in sibling worktrees** (genm-*, deriv-*,
fm*, dgc-*, dimension-stack) — stay strictly read-only outside this worktree; never touch their
branches/worktrees/builds/crons.

## The tick
1. **Recover / calibrate sensors.** Check the worktree tip + tree, `origin/expedition/rlct-foundation`, box
   load (`uptime`), and any teammate reports/idles. A teammate "done" and a green exit are *readings* — re-run
   the build, `scripts/sorries`, `scripts/cited` (once it exists), `#print axioms`, before believing them
   (CLAUDE.md § Controller operation; DA1/DA3/DA5).
2. **Ingest** completed threads: read the report, controller-review the diff (fidelity + name=content;
   **cordon green** — UNACCOUNTED = ∅, cites tagged+located), integrate (commit board + push).
3. **Re-anchor** on the brief's central question + the ladder (`priorities.md`). Rung 1 (cordon) gates R2–R8.
4. **Triage / re-plan** (closed loop): if a rung is harder than scoped or the recon changes the build-vs-cite
   reach, adjust the ladder — don't push a failing setpoint. Keep unblocked work moving.
5. **Delegate** the next rung with a guard-first brief + a routed decorrelated review on cruxes (R1
   correctness, the R4/R6 build-vs-cite boundary, R8 fidelity). One builder/committer at a time; disjoint-path
   parallelism only (R1 tooling · R0 read-only recon · G1 disjoint geometry).
6. **Integrate + re-gate** at rung/phase boundaries: full `scripts/lb DLNFibre` green, `scripts/sorries` = 0,
   `scripts/cited` green (no unaccounted / location violations), `#print axioms` standard-3 on BUILT headlines.
7. **Surface** decisions async + non-blocking (never a blocking `AskUserQuestion` in a loop). Proceed-on-silence
   within the staked boundary; **wait-for-explicit-go** for: the close PR *merge*, `dev → main`, and any change
   to the destination or definition of done.
8. **Idle-tick = regroup:** if this fires during a lull, re-ground, glance for drift, check teammates/PR/build,
   bank loose artefacts + lessons.

## Close
Per DA6: fold synthesis + the `citation-cordon.md` policy + README-status/ROADMAP updates into the ONE
expedition PR *before* signalling merge; branch/worktree cleanup after the operator merges. Auto-open ≤ 1 PR
this expedition unless authorised.
