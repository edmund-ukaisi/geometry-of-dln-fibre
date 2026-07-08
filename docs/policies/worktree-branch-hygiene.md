# Worktree & branch hygiene

Worktrees are disposable; **`origin` is the bank.** A worktree can be lost (disk, `git worktree remove`,
a dead box); work that is committed and pushed cannot. An expedition spawns a root plus per-thread
worktrees and branches, and at scale — a single repo has held ~280 worktrees at once — the cost is real:
opaque names hide *who owns what* and *what is safe to remove*. This policy keeps ownership and lifecycle
legible from a name alone, and keeps cleanup safe.

Companion to [`../../CLAUDE.md`](../../CLAUDE.md) § Branch discipline (the `origin` / `dev` / `master` flow
and the push/PR gates) and [`expedition.md`](expedition.md) § Isolation (worktree isolation + the
sole-merger rule).

## Naming — a light, flat convention (not a hierarchy, not a registry)

The goal: from a branch or worktree *name alone*, a human or a script can tell **which expedition owns it**
and **what lifecycle role it plays**. Two tempting designs both fail at scale — the reasoning matters
because it fixes the shape:

- **A name-encoded *hierarchy* (`expedition/<slug>/thread-01`) is broken by git itself.** A ref cannot be
  both a file and a directory, so the root `expedition/<slug>` and a child `expedition/<slug>/thread-01`
  cannot coexist — git rejects the second with a lock / "directory–file conflict". Any scheme where the
  root is a path-prefix of its threads is a non-starter, and a slug rename orphans every encoded child.
- **A registry file (worktree → owner map) drifts.** It duplicates ground truth (`git worktree list`, the
  ref list), adds a single-writer file to serialize, and desyncs the moment someone forgets to update it.

So the convention is **flat, slug-prefixed, and treated as a hint not a contract** — a violation never
breaks git; the worst case is a name that is harder to grep:

- **Branches — flat siblings under one prefix, full slug first.** The role separator is `--`, and **slugs
  never contain `--`**; that single rule makes the grep unambiguous.
  - expedition root: `expedition/<slug>` (e.g. `expedition/rlct-foundation`)
  - its sub-branches: `expedition/<slug>--<role><nn>-<topic>` — flat siblings under `refs/heads/expedition/`,
    **never nested** under the root. `<role>` ∈ `t` (thread) · `rev` (review) · `fix` · `probe`.
    E.g. `expedition/rlct-foundation--t02-zeta`, `expedition/rlct-foundation--rev-fidelity`.
  - ownership is then exactly `git branch --list 'expedition/<slug>*'`; the root `expedition/<slug>` and a
    sub-branch `expedition/<slug>--…` are siblings (distinct ref files), so they never collide.
  - non-expedition work keeps its own top prefix: `chore/<topic>`, `harness/<topic>`, `review/<topic>`.
  - *(Historical anti-pattern this fixes: sub-branches named off a truncated slug — `expedition/rlct-r2`
    under a root `expedition/rlct-foundation` — so ownership was not derivable from the name.)*
- **Worktrees — one parent directory per expedition:** `.claude/worktrees/<slug>/<role>` (`…/root`,
  `…/t02-zeta`, `…/rev-fidelity`). Filesystem directories have no ref-collision problem, so grouping by
  directory is safe *here* and is the highest-leverage piece: ownership is the `<slug>` path segment
  (`git worktree list | grep "/<slug>/"`) and cleanup is exactly that set.
- **What we do NOT rename:** substrate-created scratch worktrees (`agent-<hash>`, the Agent-Teams runtime
  pool) are named by the harness, not the expedition — out of scope here. Discipline only what the
  expedition itself creates.

This is not too rigid because it is flat (no git hierarchy to collide), convention-not-enforced (grep is
best-effort; a stray name costs legibility, not correctness), and scoped to our own artifacts. It buys the
one thing cleanup actually lacked — *ownership derivable from the name* — with no registry to maintain.

## The bank invariant

`origin` is the bank at **two levels** — a running one inside the expedition, and the final one at close:

- **Within the expedition — the root branch is the running bank.** As each thread lands, the controller
  merges it into the expedition root `expedition/<slug>` and **pushes to `origin/expedition/<slug>`**. That
  pushed root is the authoritative store of the expedition's completed work: a thread worktree can then be
  lost without losing its work, and `origin/expedition/<slug>` always reflects what is done. The controller
  keeps the root synced to remote and pushes often — the worst case is then a stale worktree, never lost
  work. (This is the day-to-day meaning of "`origin` is the bank", not only the close-out PR.)
- **At close — the `→ dev` PR is the final bank.** Because completed threads are already merged into the
  root, once the root's PR merges to `dev` its whole history is an ancestor of `dev` *by construction* —
  closeout needs no per-branch forensic audit.
- **Never local-only.** No tip should live only in a worktree. Audit one with
  `git for-each-ref --contains <tip> refs/remotes/origin/` — empty output means that worktree holds the
  *only* copy of its work.

## Close-out — the last motions of an expedition (a controller job)

Cleanup is a **pre-merge** step: tidy first, then merge. The merge to `dev` is the expedition's *final*
motion — so most of the cleanup is a set of final commits on the root, done before signalling readiness.

**Before signalling "ready to merge"** (all on the expedition root):

1. **Tidy sub-branches into the root.** Each landed thread is merged into `expedition/<slug>`; then reclaim
   its now-redundant worktree (`git worktree remove` — plain, which *refuses* on uncommitted/untracked
   changes; `--force` only once the sole obstruction is confirmed to be the gitignored `.lake` symlink) and
   delete its absorbed sub-branch **local + remote** (safe — its commits are in the root).
2. **Fold close-out docs into the root** (synthesis, README/ROADMAP status, lessons) as the final
   cleanup commits, and **push the root to `origin`**. `origin/expedition/<slug>` now holds the complete,
   banked expedition.
3. **Signal "ready to merge"** — operator-gated (the PR merge; see [`expedition.md`](expedition.md) § Gates).

**After the `→ dev` PR merges** (the final motion):

4. Delete the expedition **root** branch (local + remote) and remove the **root** worktree — these can only
   go once the root has merged (it was the PR head). `git worktree list | grep "/<slug>/"` is then empty.
   The per-branch preflight (ancestor of `origin/dev`) is run and *shown*; at scale, print only exceptions.

## Guard rails

- **Stay in your lane.** Touch only your own expedition's worktrees and branches. A sibling's worktree —
  even one whose commits look absorbed into a parent — is its controller's to reclaim.
- **"Unmerged → `dev`" ≠ unsafe.** A thread branch merged into its expedition root is banked *in the
  parent*, not lost — check containment in any `origin/*` ref, not only `dev`.
- **Never delete a branch with an open PR, or one checked out in another worktree.** Act only on a quiesced
  expedition (owning agents idle / stood down).
- **`--contains` misses squash / rebase merges.** When the merge style is not `--no-ff`, ancestry cannot see
  the absorption; fall back to the PR-merged fact (the bank invariant), not the ancestor check alone.

## Deliberately out of scope (for now)

- **Substrate-scratch reclamation.** The `agent-<hash>` pool (created by the Agent-Teams runtime, no
  expedition owner) is the operator's / harness's periodic concern, not a per-controller close-out step.
- **Automation.** A `scripts/expedition-cleanup <slug>` keyed on the naming convention (remove worktrees +
  delete branches that are ancestors of `origin/dev`, refuse and list exceptions otherwise) is the natural
  next step once the convention lands, replacing the manual loop. Roadmapped, not built.
