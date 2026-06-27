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
