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

- **The `→ dev` PR is the bank.** Once an expedition's PR merges, its root and every thread branch merged
  into that root are ancestors of `dev` *by construction* — so closeout needs no per-branch forensic audit;
  the merge already established that the content is banked.
- **Bank before you rely on it.** Push expedition and thread branches to `origin` so no tip is local-only.
  Audit one worktree with `git for-each-ref --contains <tip> refs/remotes/origin/` — empty output means that
  worktree holds the *only* copy of its work.

## Cleanup at close (a controller job)

After the expedition's PR merges:

1. **Remove the expedition's worktrees** — `git worktree list | grep "/<slug>/"`, then `git worktree remove`
   each. Prefer plain `remove` (it *refuses* on uncommitted/untracked changes — the safety you want); reach
   for `--force` only after confirming the sole obstruction is the gitignored `.lake` symlink (which points
   at the shared store and is not touched by removal).
2. **Delete the merged branches, local and remote** — `git branch -D` and `git push origin --delete` — but
   only those that are ancestors of `origin/dev` (or absorbed into a banked parent). Run the per-branch
   preflight first and *show it*; at scale, print only the exceptions, not every row.

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
