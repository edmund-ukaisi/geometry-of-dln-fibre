# Facet: incentive structure — does the harness reward narrow bricks over general machinery?

Retrospective facet for the `aoyagi-full` expedition (branch `origin/expedition/aoyagi-full`, fork
`413566b3`, 3012 commits, 2026-06-20 → 2026-07-15). Read-only archaeology; sources cited by sha,
`synthesis.md` line, `discuss-at-close.md` item, or policy file.

**Question.** Does the harness's operational incentive structure systematically favor narrow,
route-specific bricks over general-machinery building — a "local incentive gradient" producing
hard-part avoidance and reactive (rather than proactive) library building, even when every individual
actor behaves well?

**Verdict (stated up front).** Yes. A local incentive gradient exists and it points toward narrow,
consumer-shaped bricks. It is not caused by any single bad rule; it is the **aggregate vector of four
individually-correct rules** (weakest-hypotheses bedrock, the anti-treadmill sorry-skeleton contract,
"keep full clip", and "fill the layer only within a staked boundary"). The one credit channel that
funds general machinery (the hardener's "right extension → Just Do It") is advisory, argument-gated,
and scale-gated, so it is weaker than the immediate, unconditional, per-tick credit that attaches to
closing a named sorry on the critical path. The observable consequence: general machinery in this
expedition was built **only as a byproduct** of a critical-path brick's proof (never planned), was
repeatedly **scoped down to exactly the consumer's need**, and when it sat off the critical path it was
**lost** (#112) or **superseded** (waist SVD-qPeel, Brick F). The measurable language trend confirms
it: "brick" per-100-commits rose ~8× into the endgame while "reusable" stayed flat.

---

## 1. Reward-signal map

### 1a. What a tide gets credited for (the immediate, unconditional channel)

The unit of credit is **a named sorry in the goal-skeleton closed, clean-three, on the critical path.**
The ★ markers in the commit log — the ledger's explicit celebration — attach without exception to
*named-target closures*, never to "built a general family beyond the brick's need":

> `★ Brick F COMPLETE` · `★ CRUX SORRY-FREE` · `★ O2 FIDELITY PASS` · `★ D1 WALL DISSOLVED` ·
> `★ general-L R1-LOWER achiever hdiv COMPLETE` · `★ smeared branch CLOSED` · `★ CAPSTONE` (log, `grep ★`)

The vocabulary of a landing is `DONE` (129 commits) / `LANDED` (161) / `banked` (250) / `clean-three`
(199). "clean-three" — `#print axioms` = `[propext, Classical.choice, Quot.sound]` — is the
axiom-cleanliness badge that gates a landing.

The pipeline-management rule makes this channel *saturating*: after any landing the controller must
immediately refill the critical path. From `loop-prompt.md` (operator, 2026-07-10, BINDING):

> "**After a landing (integration/brick), IMMEDIATELY commission the next critical-path build(s) — do
> NOT defer to 'next tick' or leave the pipeline empty.** An empty queue after a landing is a controller
> STALL, not a rest."

and `lessons.md` (2026-07-10, "Keep FULL CLIP"): the controller's executive function *is* keeping "the
critical path SATURATED with builds." Note the object: the *critical path*. Spare capacity is defined as
belonging to the critical path, so there is no idle capacity that could be pointed at
non-critical-path generalization.

### 1b. The penalty channel for scope beyond the brick

The single strongest anti-machinery rule is the **anti-treadmill contract** in `brief.md`, installed
explicitly as a reaction to the *prior* expedition's failure (sprawl with no stop condition):

> "Every work unit **closes a named `sorry` in the skeleton** — never adds free-floating scaffolding
> (wrappers/boundaries/bridges). The **sorry-count must trend down.**"
>
> "**Periodic goal-distance check** (controller tick): is every live file on the critical path to a
> named `sorry`? If a file is not, it is scaffolding — stop and re-aim."

This directly reclassifies any lemma more general than the current brick's need as "scaffolding →
stop and re-aim." It is reinforced by two bedrock/precision virtues that independently point the same
way:

- `bedrock.md` §Statement 1.3: "carry the **weakest** hypotheses that suffice — drop unused ones …
  an unused hypothesis that looks load-bearing **lies about the content**." A more-general statement
  carries hypotheses the immediate consumer does not use.
- `precision.md` §Scope: "Proving `X` for one instance … while the name reads as `X` in general is …
  overclaim"; and `bedrock.md` §Rising sea scopes hardening to "**within a boundary already staked** …
  Moving the boundary into new territory is the different act — **and the one that needs direction**."

So *interior* hardening is funded and celebrated ("completion capacity is abundant … comparative
advantage"), but **boundary-extension into new general territory is gated on "direction"** — an
operator/controller act, not a tide's default.

### 1c. The one credit channel that DOES fund general machinery

`hardener.md` is the only role with an explicit positive channel for building beyond the brick:

> "Surfacing 'this is the right / spiritually-in-scope extension' is a **positive** finding, not a
> complaint. The honest response to a right extension: **Just Do It** if it is within reach …
> otherwise **put it on the roadmap**."

But three qualifiers make it weaker than the brick-closure channel: (i) it is **advisory** —
"Advises; the controller decides … not a veto"; (ii) it must be **earned by argument** — "a 'right
extension' [is] a claim you must argue, not assert"; (iii) the hardener is a **scale-gated controller
assistant** — `CLAUDE.md` says "skip on small expeditions", triggered on a ~60-commit / phase-transition
cadence. Against a per-landing, unconditional, pipeline-saturating brick-closure signal, an advisory
argument-gated channel loses on frequency and immediacy.

### 1d. The asymmetry, named

| | brick-closure credit | general-machinery credit |
|---|---|---|
| frequency | every landing | at hardener cadence / phase transition |
| conditionality | unconditional | earned argument + "within reach" |
| authority | the metric itself (sorry-count↓) | advisory (controller decides) |
| scope funded | critical-path close | interior-of-staked-boundary only; boundary-move "needs direction" |
| pipeline pressure | "keep full clip" refills it | competes for the same saturated pipeline |

**Interpretation.** Every actor behaving *well* — carrying weakest hypotheses, keeping files on the
critical path, refilling the pipeline, naming results for what they prove — produces the same vector:
scope each build to exactly the consumer's need, close the named sorry, bank clean-three, recharge.
That is the gradient. It is the shadow of the organizing contract ("one headline theorem + a
sorry-skeleton whose count must trend down"), whose credit metric has no slot for a reusable library.

---

## 2. Concrete instances

Facts first (each cited); interpretation flagged.

### 2a. Machinery MORE general than its brick — what happened to it

| instance | citation | what happened | verdict-class |
|---|---|---|---|
| Fubini-shift abstract theorem `rlctAt(Σx²+core)=n/2+rlctAt(core)` | `lessons.md` 2026-06-21 (l.260–277) | Abstracted a heavy sub-fact into a general reusable theorem; **celebrated** ("(c) yields a MORE GENERAL, reusable theorem") | Kept — but driver was **axiom-hygiene** (keep the module axiom-clean), and it was the *natural dual* of the ≥-direction, not a speculative extension |
| Brick F: measurable sorted-eigenvalue decomposition, a "**6-module mountain**" | `de2f9d5e4` (F2 scale recalibration), COMPLETE `5e1144059`/`f29a0bc8e` | Built because the head-split brick needed it; `★ Brick F COMPLETE`, clean-three | **Off-route by close**: priorities LATE-5 (`synth.md` l.10) marks "**Brick F likely DROPPABLE** on the incidence path" — a general 6-module build the final route may not consume |
| D-C spectral dimension-counting core `RouteMSJKyFan` | `a09fdd266`; scoped `3a0d23c86` | "~300–450-line **from-scratch spectral-LA build**", clean-three "linchpin" | Built for the brick; general-flavoured but not banked as a Core asset |
| #112 PSD-cone det-monotonicity (`det_le_det_of_posSemidef_le`), "a clean, **Mathlib-worthy PSD lemma**" | `discuss.md` #102 (l.2826); `synth.md` UPDATE l.648 | Banked on a **worktree branch, never integrated**, branch gone; `git log --all -S` finds it in zero `.lean` files — **LOST**, had to be rebuilt | The sharpest instance: genuinely-general machinery **evaporated** because it was off the critical path and the process did not protect it |
| waist SVD-qPeel machinery | `02c454d3a` (2026-07-14) | Built for the waist stratum, then "**SVD-qPeel SUPERSEDED**" by a bare-box reduction | Superseded route-specific machinery |

**Interpretation.** General machinery in this expedition was *always a byproduct discovered mid-proof*
(a brick needed an eigendecomposition, a spectral count, a det-monotonicity), never a planned
foundation. Two of the five were off-route or lost by the endgame. Nothing in the credit structure
protected them: #112 was marked "banked" and lost anyway; Brick F was `★ COMPLETE` and then droppable.

### 2b. Machinery scoped DOWN from general to minimal — consistently rewarded

The "the consumer needs only X, not the tight Y" move recurs and is uniformly framed as a **STRICT
WIN / LIGHTER / de-risk**:

- **cruxfin** (`d6010ef90`, 2026-07-14): "CRUX drastically SIMPLIFIED — cruxfin+Codex full-block route
  (row-Gram floor + pure-cube + **divergence-forces-c'<N/2 via hpiv**) **bypasses
  S3/coupled-residual/radial** … (a)-chain **needs only** D=crux." The consumer (box-finiteness) needs
  only the one-directional `RHS<⊤ ⟹ LHS<⊤`, not the tight comparator.
- **D1 ≥-leg** (`synth.md` UPDATE-384, l.2687): "needs only a QUASI-SPLIT by constant comparison
  (**NOT the full Gromoll–Meyer Morse lemma**)."
- **geleg1 rung 8** (`synth.md` l.1217): "invertible-derivative slot **needs ONLY the banked left
  inverse** — the ~100–120 L reverse-inverse algebra is **ELIMINATED**."
- **cover assembly** (`synth.md` l.322): "the cover assembly needs **ONLY exhaustiveness** `box⊆⋃S_j`,
  **NOT shell measurability** — … so it **sidesteps** the ordered-eigenvalue continuity Mathlib LACKS."
- **D1 ≤ conclusion** (`synth.md` l.2727): "the ≤ conclusion **needs only a ONE-SIDED lower bound** … A
  LOWER bound is LIGHTER."
- **hCore** (`synth.md` l.2635): "collapses to ONE clean NETWORK-FREE abstract diffeo lemma … **hCore
  DECOUPLES from R1** … NO R1 coordination. ⟹ TWO STRICT WINS."

**Interpretation.** Each of these is *individually correct* — weakest-hypotheses is a genuine bedrock
virtue, and shaping a proof to the consumer's real need is good discipline. The point is the
**aggregate**: the reflex, fired dozens of times and rewarded every time, is "find the minimal
consumer-shaped statement that discharges this brick." The gradient operates entirely inside the
*sound* region — these are not slop, they are exactly why the gradient is invisible to the audit gates.

### 2c. "Shortcut" language before verification — the immune system that exists (and its blind spot)

The harness has a **strong, explicit anti-shortcut immune response** — a whole family of `lessons.md`
entries where a proposed shortcut is caught by a decorrelated check:

- "a shortcut whose ANSWER matches is a **cross-check, not a proof path**" (Q4-lct trap, l.376);
- the `ht`-discharge shortcut that passed on anchors but was WRONG on increasing-width steps
  (l.765 — "test a property-breaking witness");
- the `admBound`-direct shortcut caught by a decorrelated pen-and-paper (l.780);
- a named-hypothesis defer whose conclusion was **provably false** on part of its own antecedent,
  caught by a decorrelated reviewer (`lessons.md` 2026-07-11, l.1294).

**Interpretation.** This immune system catches *unsound* shortcuts. It has no reason to resist the
*sound* scope-downs of §2b — and it should not, since they are correct. But that is precisely why the
gradient survives: the review gates filter unsound-narrow, not narrow-per-se. There is no gate that
asks "was a general lemma available here that we declined to build?"

### 2d. Explicit proactive-library deliberation — did anyone propose it?

Only twice, and neither became a foundations program:

- **Item 40** (`discuss.md` l.794, 2026-06-28) — the one genuinely proactive proposal: build D1's and
  L2's shared gauge-slice as a "**REUSABLE `local_constant_rank_chart` interface** that BOTH L2 (1131)
  and D1(a) (1177) consume, rather than a producer-internal specialization." **Outcome:** the presumed
  coupling was later found to be an artifact — "**Item 86's D1→R1-core-resolution coupling is
  RETRACTED (it was an r=1 artifact)**" (`synth.md` l.2635) — and D1 and L2 were each built through
  their own narrower strands (D1 via geleg1/geleg8, `synth.md` l.1171/1217). The shared interface never
  materialized. (This is *correct* — they were not actually shared — but it is the only proactive-reuse
  proposal on record, and it dissolved.)
- **BUILT-INDEX** (operator directive, UPDATE-887, `synth.md` l.665–666, 2026-07-11): "**BUILT-INDEX
  (durable library)** … index what's built so pieces aren't lost." **This is a bookkeeping index to
  prevent the #112-loss failure, not a decision to build general foundations ahead of need.** It
  catalogs what the bricks already produced.

The closest thing to a standing proactive mandate is `brief.md` standing decision 5, "**Build what
Mathlib lacks** (RLCT, monomial integrals, resolution substrate)" — but it is scoped to what *this
proof* needs, and `README`/`CLAUDE.md`'s reusable-"engine"/`Core` split is a *different programme*
(Lehalleur–Rimányi), explicitly **out of scope** for this expedition (`brief.md` §Scope).

**Interpretation.** Proactive general-foundations building was never funded as a first-class activity
here. The reuse mechanisms that *do* exist — `self-recon` ("CONSUME … reuse it") and the "does it
already exist? STOP" gate (`synth.md` l.657) — are **reactive**: they prevent re-derivation of what is
already banked; they do not fund generalizing beyond the current need.

---

## 3. Trend: did brick-narrowness increase as endgame pressure rose?

Commit-message language, normalized per-100-commits, over three phases (early = Jun 20–30, 1848
commits; mid = Jul 1–9, 675; endgame = Jul 10–15, 489):

| token | early | mid | endgame | reading |
|---|---:|---:|---:|---|
| `brick` | 2.0 | 1.6 | **16.3** | ~8× rise into the endgame |
| `labour` | 0.0 | 0.4 | **5.9** | "this is labour, not a wall" reframing spikes |
| `wall` | 4.9 | 5.1 | **12.2** | wall-encounters/checks double |
| `superseded` | 0.1 | 0.0 | **1.6** | endgame route-churn |
| `mountain` | 0.3 | 1.3 | 2.4 | rising |
| `reusable` | 0.8 | 0.2 | 0.6 | **flat/low — did NOT rise with "brick"** |
| `general` | 5.8 | **9.9** | 5.7 | peaks mid (after operator's "GO THE DISTANCE / fully general" push), falls back |

**Fact.** As endgame pressure rose, the vocabulary shifted decisively to `brick` + `labour` while
`reusable` stayed flat and `general` fell back from its mid-expedition peak. Route-supersession spiked;
the last three days carried three explicit route re-adjudications (`ROUTEFORK RESOLVED` route-B adopted
`ddba9079a`; `ROUTEVERIFY RESOLVED` incidence-direct `38f98e393`; then route-B declared **DEAD** in
priorities NOW/LATE-5). The expedition **never reached its close criterion**: the final commit
(`a30408dbb`, 2026-07-15) is mid-flight — "**Sole live lane: capstone**", `(□)` still undischarged.

**Confound (stated honestly).** Part of the `brick` rise is nomenclature: the endgame was *explicitly
organized* as a brick-decomposition of the `(□)` mountain (`endgame-lanes.md`), so the controller
adopted "brick" as the unit-word. The rise is therefore partly labelling, not purely narrowing. But the
**co-occurrence** — `brick`↑ with `reusable` flat, `labour`↑, `wall`↑, `superseded`↑, and no close —
supports the read that the narrow-brick + reactive-build approach **thrashed** near the end (bricks
built then superseded; route dead-ends) rather than converging.

---

## 4. Verdict and proposals

### 4a. The gradient, named

**The weakest-hypothesis / anti-treadmill gradient.** It is produced by the *conjunction* of four
individually-correct rules, whose vectors all point at "minimal, consumer-shaped brick":

1. **Anti-treadmill contract** (`brief.md`): every unit closes a named sorry; anything else is
   "scaffolding — stop and re-aim"; sorry-count must trend down. → beyond-brick machinery is *waste by
   definition of the metric*.
2. **Weakest-hypotheses + name-for-content** (`bedrock.md` 1.3, `precision.md`): a more-general
   statement carries unused hypotheses / risks overclaim. → shape to the exact consumer.
3. **Keep full clip** (`loop-prompt.md`, `lessons.md` 2026-07-10): refill the *critical path* after
   every landing. → no capacity is directed off the critical path.
4. **Fill-the-layer is interior-only** (`bedrock.md`): hardening within a staked boundary is funded;
   moving the boundary "needs direction." → generalization requires an operator/controller act.

**Which rules counteract it** (present but weaker): the hardener's "right extension → Just Do It"
(§1c), bedrock's "completion capacity is abundant" (interior-scoped), and `self-recon` (reactive
reuse). None competes with the per-landing brick-closure signal on frequency or authority.

**Why it yields the two symptoms in the question:**
- *Reactive, not proactive, library building:* general machinery is only ever built when a brick's
  proof *forces* it (§2a). It is a byproduct, discovered mid-proof, never planned — because the metric
  credits critical-path closure, and a planned library is not on any named sorry's path.
- *Hard-part avoidance:* the "wall vs labour" reframing + "keep full clip" + the scope-down reflex
  (§2b) together route *around* a hard general lemma by finding the minimal consumer-shaped brick that
  avoids it (cruxfin bypassing S3/coupled-residual; the ≤ needing only one-sided). Locally efficient;
  it leaves the general lemma unbuilt, and when the route shifts the avoided lemma resurfaces and the
  narrow bricks are superseded (§2a: waist SVD-qPeel; §3: route-B dead).

The gradient is **not a bug in any single rule.** It is the shadow of choosing "one headline theorem +
a sorry-skeleton whose count must trend down" as the organizing contract. The prior expedition failed
from no-stop-condition sprawl; `aoyagi-full` over-corrected to a stop-condition that credits *only*
critical-path closure.

### 4b. Minimal rule changes (fund general library-building in parallel without licensing scope-creep)

Each keeps the taste constraints intact — results named for what they prove, caveats beside claims, no
speculative sorry-farms — by **anchoring every generalization to a real, already-proven consumer**, so
it is never a guess.

1. **A bounded, taste-gated "foundations lane."** Allow a small standing fraction of pipeline capacity
   (one seat, or a ~10–15% tide budget) to generalize a lemma that a *critical-path brick just consumed
   as a special case* — to its natural statement, once. The trigger is not speculative: it is "a brick
   proved `X` for one instance and `X`-in-general is the natural/dual statement" (the Fubini-shift
   precedent, §2a). Same bedrock gates apply: named for content, weakest hypotheses *of the general
   fact*, an in-file non-vacuity witness, zero speculative sorries.

2. **Protect off-critical-path machinery from evaporation.** The #112-loss shows the process discards
   it. Gate: a lemma flagged "Mathlib-worthy" or "Core-reusable", once clean-three, is **integrated to
   canonical (or a `Core` module) immediately** — never left on a worktree branch — and BUILT-INDEX
   marks it a durable asset, not merely an index line. (Partially instituted after #112; make it a
   gate, not a lesson.)

3. **Amend the goal-distance check** so it reads: "on the critical path to a named sorry **OR** a
   clean-three general lemma banked in `Core` with an in-file non-vacuity witness." This carves a
   *narrow* exception to "scaffolding → stop and re-aim" so that generalizing a just-consumed special
   case is not reclassified as waste — while the clean-three + witness + Core-home requirement still
   forbids the free-floating wrapper/sorry-farm the anti-treadmill contract was built to stop.

4. **Give the hardener's "right extension" channel teeth at phase transitions.** At each integration of
   a brick that consumed a special case, the hardener names whether the general form is "the right
   extension" and "within reach"; a within-reach right-extension gets *at minimum* a roadmap entry (so
   it is never lost) and foundations-lane funding if a slot is free. This converts an advisory,
   easily-skipped signal into a logged decision.

**Net.** The bricks stay honest and minimal; the sea still rises inexorably over the one headline. But
it rises with reusable rock deliberately banked alongside the critical-path fill — instead of leaving
the general lemmas as byproducts that get lost (#112), superseded (SVD-qPeel), or stranded off-route
(Brick F) when the route inevitably shifts.
