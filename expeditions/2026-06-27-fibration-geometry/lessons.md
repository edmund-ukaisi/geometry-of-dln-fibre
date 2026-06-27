# Lessons — `fibration-geometry` (append-only)

## L0 — Disposition steer (operator, 2026-06-27)

> "Don't treat recon as 'derisking'. You can do hero tasks well — particularly as these are well
> established mathematics. You as controller (adaptive and feedback controller) can keep the vision and
> let the sea rise, inevitably. That something doesn't have much Mathlib support is not at all a blocker
> for you. Structure the expedition well for a large task: the loop-prompt and the hourly cron as
> backstop in addition to teammate pings — so you understand you can just let the sea rise."

**Why:** I had been over-weighting the scouts' "sub-wall / no Mathlib lemma" labels as near-verdicts and
gating action behind more recon + more sign-off questions. The operator's standing read: these are
classical, well-established results; the controller's job is to hold the vision and rise to them
inevitably via tides, *building* the missing scaffolding. Recon sharpens the target; it does not earn a
veto.

**How to apply:** (1) Set targets at the edge of reach; drop scope only for a *genuine* blocker, never to
look tidy or save effort. (2) "No packaged Mathlib lemma" → scope a tide to build it (e.g. the over-field
minor criterion as the dual of `exists_invertible_minor_of_rank`). (3) Run the unattended machinery:
`loop-prompt.md` + an hourly cron backstop + teammate pings, so the tick keeps running and the sea keeps
rising between operator touches. (4) Keep delegating + integrating (controller does not rabbit-hole into
Lean), but be *more* ambitious than the teammates. Bedrock discipline (AUDIT, decorrelated review,
name = content) is unchanged — ambition is in the *target*, rigour in the *gate*.

## L1 — Recon structural findings (digested into brief.md)

- The three "bundle" questions collapse onto **one keystone**: the prime/residue-field rank bridge
  (`rankROpen = {rank = r}`). Solve once.
- **P2 (target rebase) is redundant**: LR's Lemma-4.6 bundle is a target-side `G_out`-equivariant object,
  genuinely different from our source-side atlas; its only *used* consequence (arbitrary-`B` count) is
  already proved. Don't chase it for completeness.
- The RLCT runway's true wall is the **singular-locus lower bound** (`rlct ≥ codim/2` everywhere), not
  the smooth locus (which gives only the upper bound). This expedition builds the upper-bound slab and
  roadmaps the lower bound — it cannot close `rlct = codim/2` and must not be named as if it did.

## L2 — Tide commit-hygiene + cross-base integration (wave 1, 2026-06-27)

- **Tides must commit + green-gate BEFORE reporting "ready to merge".** S1 reported done but left its
  module + artefacts UNCOMMITTED on its worktree disk (branch still at the base SHA). Recoverable
  (controller integrated from disk), but it loses the provenance SHA and risks loss. Spawn prompts now
  say "commit to your own branch and green-gate every commit." **How to apply:** when a tide reports,
  `git ls-tree`/`status` its worktree before assuming a commit exists; integrate from disk if needed.
- **Cross-base rule.** Isolation worktrees branch from `origin/dev`, which LACKS the controller's
  just-landed expedition commits. A tide that must build on a prior rung needs
  `git merge expedition/fibration-geometry --no-edit` as its first step (the branch is a local ref in
  the shared repo). Bake this into every spawn prompt for a rung that depends on an earlier one.
- **Integration is uniform via worktree-disk copy** (works whether the tide committed or not) + wire the
  aggregator import myself (single-writer) + full `scripts/lb DLNFibre` green-gate before committing.

## L3 — A framing error recurs; fix it by grep, not by line (PR #12 review, 2026-06-27)

**Why:** the owner's first PR review flagged a base/total reversal (`Spec(sweepSigmaRing)` is the
source/total, not the base) + a nonsensical `SchurLoc ≅ source-chart` bridge at *specific lines*. I fixed
those exact lines. The owner's re-review found the **same** framing still living in ~8 other spots
(other docstrings, the brief central question, priorities/threads/loop-prompt, the S5 card's verbatim
signature block, stale SHA anchors). Two review rounds spent on one root error.

**How to apply:** when a review (or my own check) finds a *framing/naming* error — not a one-off typo —
treat it as a class: `grep -rn` the stale phrase(s) across **all** live docs + Lean + cards + ROADMAP +
aggregator + the operational prompts, and fix every occurrence in one pass, then re-grep to confirm clean
before re-pushing. A framing error is almost never in exactly one place. (Also: keep statement-card SHA
anchors pointed at *landed PR commits*, never worktree/base/pre-fix SHAs; and the internal `synthesis.md`
tick-ledger records the journey — leave its historical mentions, don't rewrite history there.)

**Sharpening (after under-sweeping THREE rounds, 2026-06-27).** Grepping the *exact phrases I'd seen* is
not enough — the same error wears many phrasings. The concrete failure modes that bit me, each a search
to run explicitly: (1) **same file, other sections** — I fixed a forward-pointer but not the main blocker
prose in the same module; a card's Proved/Deferred but not its title/intro/section-header/Claim; a `def`
docstring but not the module-header docstring. Read the WHOLE file's prose, not just the flagged line.
(2) **semantic class, not literal string** — "S3 target NOT met", "missing rung", "the S3 payoff",
"to-be-formalized", "coherent/triple cocycle", "P-bridge", "in flight", "witnesses non-emptiness" are all
the *same* stale frames in different words; grep each variant. (3) **non-repo artefacts** — the PR
*description* carried the same framing (grep can't reach it; re-read it after every framing fix).
(4) **cross-references to a renamed item** — renaming the `P-bridge` row left stale `P-bridge` mentions
elsewhere. After any rename, grep the old name repo-wide. Re-grep ALL of these and read the changed files'
full prose before declaring a sweep done.
