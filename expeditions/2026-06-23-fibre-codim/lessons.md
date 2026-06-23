# lessons — fibre-codimension bundle-shift (LR Lemma 4.6)  (append-only)

- **(setup) `fetch` updates `origin/dev`, not local `dev`.** Branching a new worktree off the LOCAL
  `dev` after a merge gave a *stale* base (`7854591`, PR #6) missing the just-merged PR #7. Fix:
  `git branch -f dev origin/dev` (no local `dev` worktree, so safe) before `git worktree add … dev`, or
  branch directly off `origin/dev`. [Relates to the ROADMAP "Process / harness uplift" items.]
- **(setup) Controller-in-worktree** ⟹ teammate `isolation: worktree` collapses to the shared worktree
  (serial). Acceptable; true isolation needs the controller in the main checkout (occupied by aoyagi).
- **(setup) Uplift A works — share `.lake/packages` via symlink.** The fresh-worktree `lake exe cache
  get` re-clones mathlib + builds the cache exe, which exceeds the 10-min bash cap (build killed twice).
  Fix: `rm -rf lean/.lake && mkdir lean/.lake && ln -s <main-checkout>/lean/.lake/packages
  lean/.lake/packages` — valid because the main checkout's mathlib rev (`8a178386`) matches this
  worktree's (same v4.29 pin). Result: `Core.Basic` built in **4.2 s** (vs the timed-out clone). This is
  the ROADMAP "Process / harness uplift A" applied by hand; worth scripting into a worktree hook. (Safety:
  shared `.lake/packages` is read-only at build time; the worktree's own DLNFibre oleans go in its own
  `.lake/build`. Only valid when the dep revs match.)
