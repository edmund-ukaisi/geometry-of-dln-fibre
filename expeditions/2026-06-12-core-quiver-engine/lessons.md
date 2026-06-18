# lessons.md — methodological learnings (core-quiver-engine)

Append-only. Record methodological learnings (directed suspicion for triage), not mathematical content.
New, DLN-specific Lean/Mathlib gotchas also go to `../../lean/CLAUDE.md`.

- **2026-06-12 — Agent-Teams worktree isolation is not guaranteed for every teammate; the controller
  shares the tree with any that land in the main checkout.** Spawning two teammates with
  `isolation: "worktree"` from the main checkout, only the *second* (`barcode`) got an isolated worktree
  (`.claude/worktrees/barcode`, own branch); the *first* (`basechange`) ran in the **main checkout** on the
  integration branch. Consequences hit immediately: (1) a controller `git add -A` swept the live worktree dir
  in as an **embedded gitlink** *and* the main-tree teammate's **in-progress, unbuilt** module — both pushed.
  Fixes: **gitignore `.claude/worktrees/`** (done); **never `git add -A` while a teammate shares the main
  tree — stage surgically** (`git add <path>`), and **green-gate a teammate's module before committing it**;
  **tell a main-checkout teammate not to `git commit`** (it would land on the integration branch and race the
  controller — sent `basechange` that instruction). Directed suspicion: after spawning worktree teammates,
  `git worktree list` to see who actually got isolated, and treat any in the main checkout as a shared-tree
  (serial, controller-commits) thread.
- **2026-06-12 — verify a teammate has actually STOPPED before spawning a successor for the same work.**
  I told `barcode` "you're done, stand by" and (treating it as stopped) spawned a fresh `assembly` tide for
  the remaining 4d assembly. But `barcode` kept working (momentum + async message-crossing) and had already
  landed step 1 (index-finding) + the subrep substrate — so `assembly` would have duplicated/raced it.
  `assembly`'s git-safety guard (it too landed in the main checkout) + its check of `barcode/rung-4d`'s live
  commits *before writing a byte* caught the collision; I stood `assembly` down and let `barcode` (warm,
  isolated, ahead) finish. **Rule:** before spawning a successor for work a teammate might still hold, confirm
  it is genuinely idle — an idle notification AND no recent commits on its branch (`git worktree list` +
  `git log <branch>`) — not merely that a "stop" message was sent. The git-safety + check-for-live-work guard
  on every spawned teammate is what made this recoverable (it worked twice).
