# Lessons — `rlct-bridge` (append-only)

Carried forward from `fibration-geometry` (cross-expedition wisdom), plus RLCT-specific notes.

## L0 — Disposition (operator standing directive)

Run as a large rising-sea hero arc. **Hold the vision, let the sea rise inexorably.** "No Mathlib
support is not a blocker" — build the missing geometric scaffolding; the analytic RLCT core is the honest
**cited** seam, not a wall. Be *more* ambitious than the teammates; targets at the edge of reach; drop
scope only for a genuine blocker. The controller is an **adaptive feedback controller**: keep the quest
fixed, re-route the rungs to what lands. Recon sharpens the target; it does not earn a veto. **Just Do
It** when within reach; roadmap a bare unargued extension; surface to move the boundary.

## L2 — Tide hygiene + cross-base integration

Tides commit + green-gate BEFORE reporting "ready". Cross-base: isolation worktrees branch from
`origin/dev` (LACKS the controller's just-landed commits) — a dependent tide's first step is
`git merge expedition/rlct-bridge --no-edit`. Controller integrates uniformly via worktree-disk copy +
wires the aggregator (single-writer) + full `scripts/lb DLNFibre` green-gate before committing. Keep
statement-card SHA anchors at landed PR commits.

## L3 — A framing/naming error recurs; fix by grep of the SEMANTIC CLASS, whole-file, not the flagged line

fibration-geometry cost **five** owner review rounds — every one was prose/docstring name=content (the
math/Lean was bedrock throughout), and they recurred because I fixed flagged lines + a literal-phrase
grep while the same frame survived elsewhere. The four failure modes to grep against, each pass:
(1) **same file, other sections** (forward-pointer vs main blocker; card Proved/Deferred vs
title/intro/Claim; def docstring vs module header); (2) **semantic class, not literal string** (the same
frame in many wordings); (3) **non-repo artefacts** (the PR *description* — re-read after every framing
fix); (4) **stale cross-refs after a rename** (grep the old name repo-wide). Re-grep clean + read the
changed files' full prose before declaring a sweep done.

## L4 — RLCT name=content (this expedition's existential trap)

The recurring trap here: an `rlct_…`-named result that secretly *assumes* the analytic interface it
should expose, or names a *geometric* (codim/lci/mildness) fact as if it were the *analytic* rlct
conclusion. The cited boundary is the thin `RlctInterface` (rlct-of-a-quadratic; Watanabe `≤`; the
resolution `≥` criterion) — stated explicitly, every DLN result attached to it as an INPUT, not folded
into an apparent analytic proof. The wall is the LOWER bound (singular-stratum mildness); the upper-bound
slab must not be named as the equality.
