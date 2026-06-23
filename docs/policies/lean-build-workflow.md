# Lean build workflow — many worktrees and sessions on one machine

How to run `lake` builds when this repository is checked out as **many git worktrees** and **several
independent sessions** compile concurrently on a single machine. Implements ROADMAP "Process / harness
uplift A". The binding constraints are build **RAM** and **uncoordinated concurrency** — not disk.

## The problem

Two independent costs.

### 1. A fresh worktree is expensive to make buildable

A `git worktree add` checkout shares the repository's `.git` history but starts with an **empty
`.lake/`**. Before it can build, `lake exe cache get` must (a) git-clone the mathlib dependency
repository (hundreds of MB of source), (b) compile lake's `cache` helper from source, and (c) download
and decompress mathlib's prebuilt object files (`.olean`) — **several GB** unpacked (≈6.6 GB for a
recent mathlib; the compressed download is ~0.4 GB). That is many minutes of work, repeated once per
worktree.

### 2. Many concurrent builds contend for RAM and CPU

The only code compiled locally is the *project's own* modules — **mathlib is fetched, not built** (see
the two-layer model below). But compiling one of our modules loads its transitive mathlib imports
**into memory**, so a single `lean` worker holds roughly **0.5–2 GB resident** (more for
import-heavy or `decide`/kernel-heavy modules). `lake build` spawns one worker per core by default
(`-j`), so **N independent sessions each running a build → N × cores workers**, each holding mathlib.

**RAM is the binding constraint**: exceeding physical memory triggers the OOM killer, which kills
`lean` processes and fails builds confusingly. CPU oversubscription (more workers than cores) is
secondary — it slows everything but degrades gracefully. And because independent sessions **cannot see
each other's `-j`**, a per-session cap cannot bound the global total; only a *shared* mechanism can.

## The two-layer model — why sharing is safe and free

`.lake/` holds two very different things:

- **`.lake/packages/` — dependencies** (mathlib, aesop, batteries, …). External, pinned to fixed
  revisions in `lake-manifest.json`, and **fetched, not compiled** (`cache get` unpacks prebuilt
  oleans). At a fixed set of pins this directory is **byte-identical in every worktree**.
- **`.lake/build/` — the project's own compiled output.** Built locally from our source; **differs per
  branch.**

So dependencies can be shared across all worktrees; only the small per-branch build output must stay
local.

### Memory-map sharing is automatic once the *files* are shared

Lean 4 `.olean` files are **memory-mapped read-only** — the loaded environment objects live *inside*
the mapped region. When several processes memory-map the **same file (same inode)**, the kernel keeps
that file's pages in the page cache **once** and backs every mapping with the same physical pages. So
if every worktree's `lean` processes open the **same** `.lake/packages` files, mathlib is resident in
RAM **once**, shared across all of them — automatically, no configuration.

The trap is the converse: a per-worktree `cache get` produces **separate** copies — identical bytes but
**different inodes** — which the kernel caches **separately**, giving N resident copies of mathlib.
**Sharing requires the same files, not identical copies.**

## The solution

### A shared, revision-keyed dependency store

Keep one copy of `.lake/packages` outside any worktree, keyed by the mathlib revision, e.g.
`~/.lake-shared/<mathlib-rev>/packages`:

- built **once per revision** (a single `cache get`), then made **read-only**;
- **revision-keyed**, so a worktree whose branch pins a *different* mathlib gets a different store
  rather than a stale one;
- branch-independent — not tied to any one checkout.

Each worktree's `.lake/packages` becomes a **symlink** to this store. Builds read the shared
(mmap-shared) oleans; each worktree still writes its own `.lake/build`.

### One wrapper as the single build entry point

**Build through the wrapper (`lean/scripts/lb`), never bare `lake build`.** On every invocation it:

1. **Self-heals the shared link** — ensures `.lake/packages` points at the store for *this* worktree's
   pinned revision (creating or repairing the symlink), leaving `.lake/build` local. Because this runs
   on every build, it works for **any** worktree regardless of how that worktree was created.
2. **Acquires a global build slot** — a shared counting semaphore (a pool of `flock` lockfiles) that
   caps the **total** number of concurrent builds across **all** sessions on the machine. This is the
   only thing that can bound global concurrency, since independent sessions do not otherwise coordinate.
3. **Builds with a capped `-j`.**

The pool size (`SLOTS`) and per-build parallelism (`J`) are read from a config file on **every**
invocation, so they retune live — edit the file and the next build adapts. Total concurrent workers ≈
`SLOTS × J`.

Building the store is a separate helper (`lean/scripts/lake-store-setup <mathlib-rev>`): it runs the
slow one-time `cache get`, so it is long-running and should be run detached. The wrapper requires the
store to already exist and prints the create command if it is missing.

## Sizing

Each `lean` worker costs roughly one core plus ~0.5–2 GB private heap, **on top of** the single shared
(mmap'd) mathlib copy; the sessions themselves also consume CPU and RAM. So set `SLOTS × J` to about:

> `min( cores − headroom, (RAM − OS − sessions − one shared mathlib) / ~1.5 GB )`

**Worked example — 8 vCPU / 32 GB:** the shared mathlib copy is *required* (32 GB cannot hold several
unshared copies); a global cap of about **6 workers** (e.g. `SLOTS=2`, `J=3`) leaves room for the OS
and the sessions. On a small machine, many heavy builds in parallel will **queue** on the semaphore —
that is the intended behavior: bounded and safe, not maximally fast. Lower the caps when RAM is tight.

## Relation to worktree isolation — a *separate* concern

This workflow makes any worktree cheap to build and light on RAM. It does **not** govern *how many
isolated worktrees a controller can give its teammates* — that is a distinct harness-topology question
(ROADMAP "Process / harness uplift B"): a controller running from the **main checkout** can spawn
teammates into their own worktrees, but a controller that is *itself* in a worktree has its teammates'
isolation-worktrees collapse onto its own (so those teammates must run serially). This build workflow
applies and helps in **either** topology (shared deps + global cap); it neither causes nor fixes that
collapse. Keep the two concerns separate.

## Enforcement and placement

- **Convention:** build via `lean/scripts/lb`; state it in every agent task brief ("build via
  `scripts/lb`; do not `lake exe cache get` in a worktree"). Harder enforcement (a shell alias, or the
  wrapper refusing to run outside the pool) is a possible later step.
- **Placement:** this policy and the scripts belong on the integration branch so every worktree
  branched from it inherits them.
