# Diagnosis synthesis — rising sea, hard-part avoidance, or local incentives?

Three decorrelated facet seats (2026-07-15): [`facet-hardpart.md`](facet-hardpart.md) (the avoidance
timeline), [`facet-machinery.md`](facet-machinery.md) (predictability + route-survival),
[`facet-incentives.md`](facet-incentives.md) (the reward gradient). Question posed by the operator:
was the expedition hampered by not taking the rising sea seriously enough, by hard-part avoidance /
local incentives, or something else — and was the "build the general machinery in parallel, without
fear of waste" instinct right?

**Status caveat (from facet-machinery, holds for everything below):** at the diagnosis fork the
expedition is NOT closed — the final route is fixed by adjudication (routeverify, 07-15 09:16), not
by a green build; the capstone was in flight. "Machinery that carried the proof" = machinery the
verified final spec calls for.

## The unified finding: one error, five times, three levels

The three facets are one causal chain observed at three levels.

1. **The route was decided correctly on 2026-06-25 and the decision lapsed.** The June reproduction
   (facet-machinery) did not merely *name* every carrying move of the final route (block-elim/Schur,
   blow-up with Jacobian u^(codim−1), divisor bookkeeping, the literal incidence chart); it
   **adjudicated the fork and decided it**: the coupled diag(b) recursion is the route; the
   decoupled/"light" alternative is *provably insufficient at corank ≥ 2*. That verdict — the
   reproduction's headline — existed as prose in `theory/` and never became structure. Every one of
   the five endgame forks (facet-hardpart's lineage: cruxfin shell-0, the full-block arc, the subset
   route, brickd-design's T2, route B) is **a rediscovery of the decoupled route** — the exact move
   ruled out in June. The expedition did not make five errors; it made one error five times, because
   the artifact that should have made it un-repeatable (a standing refuted-edge on decoupling) did
   not exist. This is the burden-of-knowledge failure (retrieval-and-status, not education) in its
   purest observed form.
2. **The avoidance was locally rational because the commons was unbuilt** (facet-incentives ×
   facet-machinery). Each route comparison scored "go around the crux with banked pieces" cheaper
   than "attack the crux with tools we'd first have to build" — locally correct arithmetic when the
   toolkit isn't on the shelf. The gradient is the aggregate of four individually-correct rules
   (anti-treadmill, goal-distance "not on the critical path = scaffolding — stop", weakest
   hypotheses, boundary discipline) with **zero credit channel for generality** (the hardener's
   right-extension channel is advisory and outgunned). Under-built commons → avoidance rational →
   nobody builds the commons. The equilibrium is self-sustaining and every agent in it behaves well.
3. **The observable symptom is the sufficiency-paraphrase fork** (facet-hardpart's sharpening): no
   terminal detour was built on a false object — every one rested on a *verified, fidelity-PASSed*
   lemma whose **coverage/sufficiency claim was an unverified paraphrase** ("discharges (a)/(b)",
   "2 mechanical fills", "exposes decLoss"). The harness had a strong verification channel for
   objects and none for *fits*. The selling register at route-adoption points ("bypasses", "does NOT
   need", "STRICT WIN") is the same vocabulary the writing policy bans from documents — it is the
   vocabulary of scope-down reward, and it marks every fork.

## The operator's instinct, scored

- **"General machinery should just be built in parallel, with faith"** — CONFIRMED, with one
  discriminator the record supplies: the safe level is **domain-generality** (statements about
  matrix integrals/identities per se: radial/polar CoV, det-Gram/Wishart corank integrability,
  rank-r codim, spectral identities, Schur/block-LU, minor charts). These survived *every* route
  change — survival ⇔ domain-generality, almost perfectly. What died was route-glue (statements
  coupling several route objects: the shellSpine bridge, frobSqBlockFull, the pivotShell tower).
  **The waste-fear had its sign backwards**: waste concentrated in the narrow route-specific work
  the incentives favored, plus duplication costs of *not* treating lemmas as library (#112
  Mathlib-worthy lemma parked on a worktree branch → lost → rebuilt; 4× found-already-banked).
- **The one-night existence proof:** the 5-module determinantal-incidence family — the machinery the
  verified route runs on — was built and fidelity-reviewed in ONE NIGHT once commissioned, over an
  already-banked Core base. A June-25 commission of (A) matrix radial/polar CoV + (B) determinantal
  charts / rank-strata integrability would have prefabricated essentially the whole July engine AND
  removed the cost asymmetry that made decoupling attractive.
- **The honest counterexample:** (C) measurable frames / Brick F — general in intent, built into a
  genuine Mathlib gap, later avoided via per-point charts, "likely droppable" from the mint cone.
  Early general building is not free; under the operator's "good libraries anyway" accounting it
  retains value (Mathlib-extraction candidate #1), but it caps the claim: parallel library tides
  should build the *domain* toolkit the source paper's moves dictate, not every plausible
  generality.
- **The quiver worry — acquitted.** No de-novo duplication: the RLCT modules import no quiver/orbit
  machinery; the analytic (measure) stratification and Core's algebraic orbit stratification are
  different spaces that meet exactly at the number minAdm — and that meeting point WAS exploited
  (minAdm = cCodim proven natively as the bedrock cross-check). Consuming Core's scalar outputs was
  the right interface.

## What single change moves the most

Ranked by leverage on THIS record:

1. **Make route decisions un-lapsable** (the expedition-map: the 06-25 adjudication as a standing
   node; refuted-alternative edges; any new route proposal touching a refuted shape gets flagged at
   proposal time). This kills all five forks at once. Cheapest, most upstream.
2. **The day-5 library commission** (rising sea, scoped by the domain-generality discriminator: the
   toolkit the source paper's proof moves dictate). This removes the cost asymmetry that made the
   forks attractive — necessary for (1) to hold under pressure, because a standing decision that is
   expensive to execute invites relitigating.
3. **The route-adoption gate** (already designed: composition skeleton against verbatim statements +
   corner-battery instantiation) as the mechanical backstop for whatever still gets proposed.
4. **The incentive patches** (facet-incentives' four proposals, all anchored to proven consumers:
   generalize-what-you-just-used; Mathlib-worthy ⟹ canonical immediately, never a side branch; the
   narrow scaffolding-rule exception; hardener teeth at transitions) as the sustaining fix.

The counter-narrative, stated fairly: the gates worked — nothing false was ever minted; every false
object died pre-build or pre-mint; the cost was ~2 days of endgame wall-clock and ~half the terminal
dispatches, not correctness. The process was expensive, not unsound. The diagnosis is about buying
the same soundness at a fraction of the spend.
