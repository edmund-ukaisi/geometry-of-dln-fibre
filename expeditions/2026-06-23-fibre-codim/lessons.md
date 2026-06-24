# lessons — fibre-codimension bundle-shift (LR Lemma 4.6)  (append-only)

- **(setup) `fetch` updates `origin/dev`, not local `dev`.** Branching a new worktree off the LOCAL
  `dev` after a merge gave a *stale* base (`7854591`, PR #6) missing the just-merged PR #7. Fix:
  `git branch -f dev origin/dev` (no local `dev` worktree, so safe) before `git worktree add … dev`, or
  branch directly off `origin/dev`. [Relates to the ROADMAP "Process / harness uplift" items.]
- **(setup) Controller-in-worktree** ⟹ teammate `isolation: worktree` collapses to the shared worktree
  (serial). Acceptable; true isolation needs the controller in the main checkout (occupied by aoyagi).
- **(rotation hold) Uplift A implemented (draft, to-validate-on-box).** Authored the multi-worktree
  Lean build workflow during the VM-rotation hold: `docs/policies/lean-build-workflow.md` + `lean/scripts/lb`
  (shared-store symlink + global `flock` build semaphore + capped `-j`, on-the-fly tunable) + `lean/scripts/lake-store-setup`
  (one-time detached store materialisation) + `lean/CLAUDE.md` pointer. Key design point (operator): with
  MULTIPLE independent controllers each spawning teammate worktrees, per-session `-j` can't bound total
  concurrency — only a GLOBAL semaphore (in the wrapper, the single chokepoint) can. Target box t3.2xlarge
  (8 vCPU / 32 GB): shared mathlib is REQUIRED (can't hold unshared copies); global cap ≈6 workers.
  **TODO post-rotation:** validate the scripts on the box (esp. store-materialisation + the flock pool),
  then **promote the policy + scripts to `dev`** so every worktree inherits them.
- **(rotation hold) Build-script validation on the prior box — 3 bugs fixed + a real toolchain finding.**
  Tested `lb` end-to-end (temp store symlinked to the already-materialised packages — no `cache get`, no
  disturbing other sessions). Bugs: (1)(2) two `set -e` exits — `[ cond ] && { … }` at statement level
  exits the script when `cond` is false (the build-config-source and slot-wait lines); use `if … fi`.
  (3) **Lake 5.0 / Lean v4.29 has NO `-j`/`--jobs` flag** (`unknown short option '-j'`) — per-build
  parallelism is the **`LEAN_NUM_THREADS`** env instead. **Measured** that `LEAN_NUM_THREADS` caps the
  concurrent-`lean`-*subprocess* count (`=1`→1, `=4`→4), so `SLOTS × J` is a valid TOTAL-worker cap
  (`SLOTS=2, J=3` confirmed fine). Method notes: deleting a module's `.olean` does NOT force a rebuild
  (lake trusts its trace) — force via a source content change (revert with `git checkout`); `pgrep -c`
  exits non-zero on 0 matches (don't `|| echo 0` — it double-counts). Wrapper now validated except the
  one-time `cache get` (store-setup), which still needs the box.
- **(setup) Uplift A works — share `.lake/packages` via symlink.** The fresh-worktree `lake exe cache
  get` re-clones mathlib + builds the cache exe, which exceeds the 10-min bash cap (build killed twice).
  Fix: `rm -rf lean/.lake && mkdir lean/.lake && ln -s <main-checkout>/lean/.lake/packages
  lean/.lake/packages` — valid because the main checkout's mathlib rev (`8a178386`) matches this
  worktree's (same v4.29 pin). Result: `Core.Basic` built in **4.2 s** (vs the timed-out clone). This is
  the ROADMAP "Process / harness uplift A" applied by hand; worth scripting into a worktree hook. (Safety:
  shared `.lake/packages` is read-only at build time; the worktree's own DLNFibre oleans go in its own
  `.lake/build`. Only valid when the dep revs match.)
- **(rotation hold) Global build semaphore validated + one benign edge case.** With `SLOTS=1`, two
  concurrent `lb` builds correctly serialise: the loser logs "all 1 global build slots busy; waiting…"
  until the winner releases the `flock` slot, then proceeds (both green). The cross-session global cap
  works — the answer to the multi-controller RAM concern. **Known limitation (box-TODO):** `lb`'s
  `.lake/packages` self-heal runs *before* the slot acquire and is **not concurrency-safe within one
  worktree** — two `lb` in the *same* worktree could race the `rm -rf`/`ln -s`. Benign in intended use
  (one build per worktree at a time; distinct worktrees have distinct `.lake`). Fix on the box: wrap the
  self-heal in a per-worktree `flock` (separate fd from the global build pool).

## Multi-tide coordination — the G2-2 collisions, and protocol-level fixes (2026-06-24)

**Failure mode.** G2-2's elimination half saw THREE collisions: two formaliser tides grinding the SAME
residual in the SAME shared worktree. Zero damage (committed-seam discipline + the tides halting on
collision saved it), but heavy wasted effort + controller overhead.

**Root causes (mechanism, not carelessness):**
1. **Shared worktree.** All tides ran in the controller's one worktree ⟹ `.lake/build` races, git-index
   races, and an untracked in-flight `.lean` pollutes the whole-package build (duplicate decls) for the
   other tide. (`scripts/lb` builds every `.lean` in the package, tracked or not.)
2. **No reliable hard-stop.** `TaskStop` did not reach the `Agent`-spawned background tides (by name or
   `name@session`); only a `shutdown_request` worked — and a busy tide doesn't process it promptly.
3. **Message latency vs fast tides.** "stop / go / actually finish" messages crossed the tides'
   continued commits. The controller's model of "tide X is at state S" was always stale on arrival;
   tides commit + idle on their own cadence, not on a mid-burst message.

**Higher-level fixes (adopt as protocol):**
- **(A) One write-baton per branch.** Exactly one tide holds the write-baton for a module/branch.
  Issued on spawn; returned ONLY by *confirmed termination* (shutdown-approved / process-gone), never by
  a "standing down" message. Successor spawned only after the baton is returned. ⟹ terminate-then-spawn,
  never overlap.
- **(B) Hand-offs are terminate-then-spawn.** A tide that safety-valves commits a clean partial, is shut
  down (controller waits for the shutdown-approved event), THEN the successor reads the committed state +
  handoff doc. No "fresh tide for the residual" while the original is alive.
- **(C) Strictly serial formaliser tides in a shared worktree.** Until per-teammate worktree isolation
  exists, ONE write-tide at a time, full stop. (Scouts/reviewers that don't WRITE Lean may overlap —
  they don't touch `.lake/build` or commit source.)
- **(D) Act on committed state, not messages.** Source of truth = `git log` / the branch, not in-flight
  tide messages (stale by arrival). Redirect only at a tide's self-reported committed checkpoint.
- **(E) Never leave an untracked `.lean` in the package; commit partials frequently.** A hand-off is
  always from a clean committed state; an untracked in-flight module breaks the other tide's build.
- **(F) Don't re-scope a tide mid-flight via crossing messages.** If scope changes, wait for the tide's
  next checkpoint and re-spec then.

**For the operator at expedition end (harness asks):** (i) per-teammate worktree isolation for a
*worktree-based* controller — the real fix to (C), = ROADMAP Uplift B (currently teammate `isolation:
worktree` collapses onto the controller's worktree); (ii) a reliable controller hard-stop for background
tides (`TaskStop` didn't reach `Agent`-spawned ones). With (A)–(F) the collisions are structurally
impossible (never two write-tides on one branch), but (i)+(ii) would make it cheap rather than disciplined.
