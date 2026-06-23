# Lean build workflow — multi-worktree, multi-session

How we run `lake` builds when **many worktrees** and **multiple independent controller sessions**
(each with teammates in their own worktrees) share one machine. Implements ROADMAP "Process / harness
uplift A". The binding constraints are **build RAM** (Lean elaborator processes loading mathlib) and
**uncoordinated concurrency** across sessions — *not* disk.

> **Status: DRAFT — validate on the target box before relying on it.** The scripts
> (`lean/scripts/lb`, `lean/scripts/lake-store-setup`) are written but **untested** (authored during a
> VM-rotation hold). The store-materialisation step and the `flock` semaphore are the parts to test
> first on the new machine.

## The one rule

**Build via `lean/scripts/lb`, never bare `lake build`.** The wrapper is the single chokepoint that
makes shared dependencies and a *global* concurrency cap possible. A bare `lake build` bypasses both.

## Why — the two-layer model

`.lake/` holds two very different things:

- **`.lake/packages/` — dependencies (≈7.4 GB; 6.6 GB is mathlib).** External, pinned to fixed
  revisions, **fetched not compiled** (`cache get` unpacks prebuilt oleans). At a fixed pin it is
  **byte-identical in every worktree**.
- **`.lake/build/` — our own oleans (DLNFibre, small).** Compiled locally; **differs per branch**.

Lean 4 oleans are **memory-mapped (read-only)**. When multiple `lean` processes open the *same file
(same inode)*, the kernel keeps its pages in the page cache **once** and shares them across all
processes — automatically, no config. So pointing every worktree at **one shared copy** of
`.lake/packages` both avoids the per-worktree clone/decompress *and* collapses N resident copies of
mathlib to one. Per-worktree copies (what a per-worktree `cache get` produces) **defeat** the sharing
(different inodes → separately cached).

## What the wrapper does (every build, any worktree)

1. **Self-healing shared packages.** Ensures `lean/.lake/packages` is a symlink to the rev-keyed shared
   store (below); fixes it if missing/stale. `.lake/build` (our per-branch oleans) stays local. Because
   this runs on *every* build, it works for **any** worktree-creation path — controller's, manual
   `git worktree add`, or a teammate's `isolation: worktree` — with **no dependency on harness hooks**
   (which fire only *outside* a git repo, so not for our git worktrees).
2. **Global concurrency cap.** Acquires a slot from a **shared `flock` token pool** before compiling.
   This bounds **total** concurrent Lean work across *all* sessions and controllers — the only thing
   that does, since independent sessions can't see each other's `-j`.
3. **Capped build.** Runs `lake build -j $J "$@"`.

`SLOTS` (size of the token pool) and `J` (per-build `-j`) are read from `$LAKE_SHARED/build-config`
**each invocation** → **tunable on the fly** (edit the file; the next build adapts). Total concurrent
Lean workers ≈ `SLOTS × J`.

## The shared store

`~/.lake-shared/<mathlib-rev>/packages` — **rev-keyed** (a mathlib pin bump gets its own store; no
stale symlinks), materialised **once per rev**, made **read-only**. Branch-independent (not tied to any
session's checkout). `lean/scripts/lake-store-setup` builds it (one slow `cache get`); the wrapper
self-heals against it.

## Co-design with worktree isolation

The expedition isolation model (`expedition.md` §Isolation) tolerated *collapse-to-serial* only because
fresh worktrees were expensive to build. Once the wrapper makes any worktree build-ready in seconds with
shared RAM:

- **True per-teammate parallel isolation becomes the cheap default** — controllers can run from the main
  checkout with each teammate in its own worktree, all sharing one mathlib.
- **The binding constraint moves from per-worktree cost to *global* concurrency.** With **multiple
  controllers** each spawning teammates, per-session `-j` is insufficient; the **global semaphore** is
  what prevents oversubscription. Every build through the wrapper ⇒ one global cap, **independent of how
  many controllers/sessions exist**.
- **Topology-agnostic:** correct whether a controller is in the main checkout (distinct teammate
  worktrees) or itself in a worktree (teammates collapse onto it). Either way the wrapper shares packages
  and counts against the same global pool.

## Box sizing

Lean builds: each `lean` worker ≈ one core + ~0.5–2 GB private heap (heavy AG / `decide +kernel` modules
more), **on top of** the shared (mmap'd, one-copy) mathlib environment. The Claude sessions themselves
also consume CPU/RAM. So:

| Box | Shared mathlib | Global cap (`SLOTS×J`) | Note |
|---|---|---|---|
| **t3.2xlarge — 8 vCPU / 32 GB** | **required** (32 GB can't hold multiple unshared copies) | **≈6** (`SLOTS=2`, `J=3`) | 6–7 heavy parallel expeditions is *tight*: the cap keeps it **safe** (no OOM) but builds **queue** — bounded, not fast. Tune `SLOTS`/`J` down on RAM pressure; monitor. |

Rule of thumb: total workers `≤ min(vCPU − headroom, (RAM − OS − sessions − one-shared-mathlib) / ~1.5 GB)`.

## Setup order on a new machine (step 1, post-provision)

1. `lean/scripts/lake-store-setup` — one clean `cache get` → build `~/.lake-shared/<rev>/packages` (the
   single slow, one-time materialisation), set read-only.
2. Write `~/.lake-shared/build-config` (`SLOTS=2`, `J=3` for the t3.2xlarge).
3. `scripts/lb` + `scripts/lake-store-setup` present and executable; this policy + the `lean/CLAUDE.md`
   pointer in place.
4. Existing worktrees self-heal on their first `scripts/lb` build.

## Enforcement

Convention, documented here and in `lean/CLAUDE.md`, and **stated in every teammate spawn brief**
("build via `scripts/lb`, never bare `lake build`; do NOT `lake exe cache get`"). Harder enforcement
(shell alias, or `lb` refusing if not invoked through the pool) is a possible v2.

## Promotion

This policy + the scripts must live on **`dev`** so every branch-off-`dev` worktree inherits them
(authored on the `fibre-codimension` expedition branch during the rotation hold — promote to `dev`
early post-rotation, ahead of the expedition's own PR).
