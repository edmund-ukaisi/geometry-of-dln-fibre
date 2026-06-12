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
