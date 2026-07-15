# Facet diagnosis — hard-part avoidance in the `aoyagi-full` endgame

**Question.** Was the expedition's endgame dominated by "hard-part avoidance" — capacity
flowing into routes AROUND a named crux rather than into the crux — and if so, what did each
avoidance arc cost, and what does the record say drove it?

**Scope / method.** Branch `origin/expedition/aoyagi-full`, range since fork `413566b3`
(2026-06-20 14:36) to HEAD `a30408dbb` (2026-07-15 09:47); 3012 commits. Sources: the git log
(`%h|%cI|%s`), `expeditions/2026-06-20-aoyagi-full/{endgame-lanes.md, synthesis.md,
discuss-at-close.md, lessons.md}`. All timestamps UTC. **Facts** (log lines, timestamps, cert
verdicts) are separated from **interpretation** (classification, verdict) throughout.

---

## Verdict up front

**Yes — the terminal endgame (2026-07-13 23:40 → 2026-07-15 09:47, ~34 h of intense work) was
dominated by hard-part avoidance.** The named crux is the *shell-restricted coupled residual* —
the domination inequality for the shell-j stratum where the pivot energy is coupled to the
corank rows (step2's OBSTACLE-A, later the incidence estimate `(∗_T1)`). Between the crux being
isolated (2026-07-13 20:29) and being *proven on paper* (incidencepp, 2026-07-14/15), capacity
ran into **five successive routes around it**. Two were large: cruxfin's shell-0 full-block
(~3 dispatches) and the off-shell full-block-via-deep-floor arc
(t2adjud→pradial→finfin→shearfin→wallfin→flagpeel, ~7 dispatches). The latter was **certified
FALSE by an obstruction hunt** (thresholdhunt, witness (6,6,6)@u=4) one step before it would
have been built on. Three smaller detours (subset route → circular; brickd-design MC-to-T2 →
gate-caught; route B → operator-caught) followed.

**The sharp finding: the avoidance was not "building on unverified objects" — the objects were
often reviewed. It was that the reviews verified the wrong property.** Each detour's justifying
claim was *object-truth of a narrower object* (verified) standing in for *sufficiency/coverage of
the head-split* (never verified). cruxfin's shell-0 lemma passed a fidelity review while being
silently shell-0-only. The full-block threshold was called "design-confirmed ×3" when it was
a=b=1-confirmed. **The hard coupled object was explicitly set aside as unnecessary** ("the crux
does NOT need S3/coupled-residual", cruxfin, `d6010ef90`) — ~1.5 h after a decorrelated cert
(couplingfin) had ruled the opposite. That cert was vindicated ~17 h later by the witness that
killed the second full-block arc.

The honest counter-case (below) is real: the SD-7 "isolate the hard piece, build everything
above it" discipline produced genuine surviving machinery, the gates caught every false object
*before* the mint, and incidencepp ultimately proved the object bounded — so the "attempt it
math-first" instinct was right in the end. But the record itself names the pattern as *the
lesson* of the endgame (discuss-at-close, 2026-07-14: "a confident 'simplification' that skipped
the hard piece").

Note on end-state: **the record ends with the crux proven on paper and the charts built, but the
final Lean capstone still in flight** (the sole live lane at `a30408dbb`). The endgame did not
reach a sorry-free `(□)` within the record; it reached a *verified route* + a spawned capstone.

---

## FACTS — dated lineage of the coupled object

### Origin (July 13)

| When (UTC) | sha / marker | Event |
|---|---|---|
| 2026-07-13 (UPDATE-1024–1047) | synthesis | Endgame approach: Brick D (D-A/B/C) + Brick F landed clean-three; head-split `(a)`-chain assembled modulo two bricks: **F** `exists_headSplitFrame` + **D** `headSplit_domination`. |
| 2026-07-13 20:29 | `47975da7d` | step2 ISOLATES the head-split crux to `pivotPeel_domination` (1 sorry). *"exact crux = A_cor-coupling uniform-reorganization"*; **couplingfin** (decorrelated pen-and-paper) dispatched to adjudicate bounded-vs-wall. This is the first sharp naming of the coupled object. |
| 2026-07-13 22:50 | `43b84d7fa` | **couplingfin OBSTACLE-B RULING** — *"(B) thread the shell into pivotDomLHS (head-split is per-shell; **full-box was an over-drop by shellSpine_le_hsQ_box**)"*. couplingfin cert: the coupled-residual **diverges off-shell** (c'∈(3,3.5) at the anchor; off-shell threshold 5/2 < on-shell 3); the singular shell is **load-bearing**; the object is **bounded** but only shell-restricted. |

(The coupled-residual has ancestry in step2's own multi-turn grind of the D-A-radial / S3-corank
route; earlier "coupling" language in the log, 2026-06-24 onward, is the *separate* R1/hfin
coupled resolution, not this object.)

### Detour 1 — cruxfin's shell-0 "full-block" (July 13 23:40 → July 14, killed 11:57)

| When (UTC) | sha | Event |
|---|---|---|
| 2026-07-13 23:40 | `f05baf742` | cruxfin **relaunched on the S3/coupled-residual route** — step 4/5, "lemma (6) radial convergence". Still *attacking* the crux. |
| 2026-07-14 00:17 | `d6010ef90` | **DETOUR ADOPTED** — *"CRUX drastically SIMPLIFIED — cruxfin+Codex full-block route (row-Gram floor + pure-cube + divergence-forces-c'<N/2 via hpiv) bypasses [S3/coupled-residual]"*. Ledger (endgame-lanes §CURRENT LANES): *"the crux does NOT need S3/coupled-residual/radial (lemma 6) — the consumer needs only RHS<⊤⟹LHS<⊤ (not the tight RLCT comparator)"*. |
| 2026-07-14 00:24–01:38 | `e43eb54ef`…`07f88232d` | Cascade on the simplification: hcvg dropped, hole (d) complete, waist step-1, crux core done. |
| 2026-07-14 (rhsfin) | branch `genm-sj5-step2` `a2f57e57` | Crux closed **SORRY-FREE**; **cruxreview FIDELITY PASS** (+ Codex xhigh, forced recompile): "faithfully encodes the head-split domination … full-block route SOUND step-by-step … NON-VACUOUS". |
| 2026-07-14 11:57 | `1226aacf9` | **t2adjud KILLS it for j≥1** — `pivotPeel_domination` proves `∫_{matBox∩pivotShell}`; **pivotShell = {σ_min(hsQ)≥ε} = shell-0 exactly** (code-confirmed via its own docstring); cover shells j≥1 are DISJOINT ⟹ the bridge `shellSpine_le_hsQ_box` is FALSE for j≥1. Concrete refuter M₀=M₁=M₂=n=2, Z=I, j=1, c'=3/2 ⟹ ∞≤finite. *"Honest walk-back from 'mint imminent'."* The ledger claim "crux discharges (a)/(b)/(d)" is named an **OVERCLAIM (j=0 only)**. |

### Detour 2 — off-shell full-block via deep floor (July 14 ~12:00 → killed 16:49)

t2adjud §4 prescribed a route that **bridges the RHS to FULL matBox** (drops the shell) and
dominates via a deep-factor floor `hfloor` on Z_deep — i.e. exactly the "over-drop to full-box"
couplingfin had warned against 13 h earlier.

| When (UTC) | branch tip / sha | Event |
|---|---|---|
| 2026-07-14 12:36 | `genm-sj5-pradial` | **pradial** — "full-matBox deep-floor route is SOUND"; claims λ_full=(minAdm(redChain)+ab)/2 "EXACTLY (marginal)". couplingfin's off-shell degradation dismissed as "the PIVOT-ONLY sub-integral". |
| 2026-07-14 14:26 | `genm-sj5-finfin` | **finfin** — brick B done; hard content isolated to `pivotDomLHS_full_lt_top`; "This wall IS the original coupled-residual / OBSTACLE-A … CONVERGED, not ping-pong". |
| 2026-07-14 15:14 | `genm-sj5-shearfin` | **shearfin** — reduces to `frobSqBlockFull_lt_top`; "the last hard analytic brick … labour not Mathlib-gap"; Codex consult FAILED both attempts (no decorrelated check this round). |
| 2026-07-14 15:48 | `genm-sj5-wallfin` | **wallfin** — *"the wall is LABOUR, NOT a Mathlib wall (3-way corroborated)"*; terminal brick `stackedGram_flagPeel_le`. |
| 2026-07-14 15:57 | `d9b103ae2` | **wallreview ESCALATION** — "wall STRUCTURE sound (4 PASS) **but THRESHOLD (minAdm+ab)/2 confirmed ONLY at a=b=1**; my '×3 designs' was imprecise". flagpeel PAUSED. |
| 2026-07-14 16:49 | `0f70389e2` | **thresholdhunt DEGRADES → `frobSqBlockFull_lt_top` is FALSE.** Certified witness M=(6,6,6), u=4, c'=13.75 DIVERGES (codim-27, true rlct minAdm/2=13.5) while the wall claimed finite for c'<14; Codex independent (Wishart blow-up). The full-block LHS is **u-independent**, true λ=minAdm(M)/2; the claimed threshold overcharges at non-argmin cuts. **"shell load-bearing (couplingfin vindicated)."** flagpeel KILLED. |
| 2026-07-14 16:59 | `d392a7f57` | Re-scope to the shell-restricted coupled-residual (OBSTACLE-A) as the **sole priority**. |

### The re-scope arc — direct attack, with one embedded detour (July 14 evening → July 15)

| When (UTC) | sha / branch | Event |
|---|---|---|
| 2026-07-14 18:56 | `c0f4ca795` / `genm-sj5-rescopefin` | **DETOUR 3 — subset route.** `shellSpineIntegrand ≤ routeMLayerBoxIntegral M` landed sorry-free, but **CIRCULAR** for the recursion (box ≤ Σ shell ≤ (r+1)·box; closes finiteness, does not advance the descent). Self-flagged in the same landing; fidelity PASS-WITH-NOTES confirmed the circularity is honestly surfaced. |
| 2026-07-14 19:43 | `genm-sj5-brickdfin` | **brickdfin** — architecture SOUND + NON-CIRCULAR + BUILDABLE-AS-LABOUR (decorrelated Codex); landmine `deeperFlag_shell_le` (no upper bound) FIXED to T1. Direct, survives. |
| 2026-07-14 20:30 | `d8023a601` | **DETOUR 4 — brickd-design MC-to-T2.** Mechanism build-ready but claims finiteness to T2 via Monte-Carlo; **CONFLICTS with thresholdhunt's exact certificate**. Gate: "NOT building (∗) toward a disputed threshold." Retracted same arc (T1 wins); near-zero build cost. |
| 2026-07-14 ~23:08 | `genm-sj5-brickdbuild` | **brickdbuild** — (□) reduces to ONE estimate, decorrelated-flagged **candidate WALL** (missing mathematics). Binding corner (2,2,3) verified. Decision: attempt it math-first → incidencepp. |
| 2026-07-14/15 | incidencepp | **CRUX PROVEN** — the partial-shell transverse-Schur incidence estimate is TRUE (scope a+b≤M₂) via a joint (z,A_cor,front) incidence-rank resolution; exhaustive exponent sweep (332/332 binding cuts, 0 failures) + Codex xhigh. Explicit determinantal-big-cell atlas extracted (§3b) ⟹ bounded Lean labour, no wall. |
| 2026-07-15 00:54–01:04 | `genm-sj5-brickdcont`, `genm-sj5-chart5` | Incidence charts built sorry-free: `transverseSchurGram`, exponent gate, chart-4 polar, gluing core, chart-5 big-cell. |

### Detour 5 — route B (decoupling, again) (July 15 morning)

| When (UTC) | reference | Event |
|---|---|---|
| 2026-07-15 (LATE) | endgame-lanes §CAPSTONE ROUTE FORK | **capstonerecon** claimed capstone = "assembly + 2 mechanical fills" via a full-block Loewner tower. **REJECTED** — it "never checked the bridge's TRUTH"; controller **HELD, did not build**. |
| 2026-07-15 (LATE-3) | §ROUTEFORK RESOLVED | **routefork** adopts **route B (S3/deep-factor floor)** as the corrected route; **demotes the (verified, coupled) incidence charts to "off-route fallback"**. |
| 2026-07-15 (LATE-4) | §ROUTE B FLAGGED BROKEN (OPERATOR) | **Operator catches two errors** in routefork's construction: (1) hpiv FALSE on M₂>M₁ cuts; (2) route-B step 2→3 is a **TYPE ERROR** — decoupled floor can't compose; *"The coupling is ESSENTIAL = exactly what the incidence machinery was built for."* Controller: "I accepted routefork's construction UNVERIFIED — forward-guard applied to its refutation but not its own construction." |
| 2026-07-15 09:16 | `38f98e393` | **routeverify RESOLVES** — coupled incidence-direct route VERIFIED (Codex + exact identities); route B a dead type-error; incidence descent GENUINE + non-circular. Charts VINDICATED. |
| 2026-07-15 09:27 / 09:47 | `7e8157494` / `a30408dbb` | Capstone tide spawned; gaugelift (general-L gate) done. **Record ends — capstone in flight.** |

---

## FACTS — effort accounting

Wall-clock and dispatch counts (a "dispatch" = a named tide/pen-and-paper/reviewer thread). LoC
is not separable per arc because branches share the 2900+ commit common history; dispatch count +
wall-clock + the controller's own effort notes are the proxies.

| Arc | Attacked or routed around? | Dispatches | Wall-clock | Outcome | Surviving critical-path Lean |
|---|---|---|---|---|---|
| couplingfin adjudication | ATTACK (paper) | 1 (pp) | 07-13 20:29→22:50 | Cert: bounded, shell-restricted | — (its verdict; vindicated) |
| **Detour 1 — shell-0 full-block** | ROUTE AROUND | 3 (cruxfin, rhsfin, cruxreview) | ~12 h (07-13 23:40→07-14 11:57) | True but shell-0-only ⟹ insufficient | `pivotPeel_domination` kept as a valid shell-0 lemma |
| **Detour 2 — off-shell full-block/deep-floor** | ROUTE AROUND | 7 (t2adjud, pradial, finfin, shearfin, wallfin, wallreview, flagpeel) | ~5 h (07-14 ~12:00→16:49) | **Refuted with witness** (thresholdhunt) | Reduction plumbing (ratio-trick) reusable; central object FALSE |
| Detour 3 — subset route | ROUTE AROUND | 1 (rescopefin) | ~2 h | **Circular** (self-flagged) | `shellSpineIntegrand_le_layerBox` (L=0 base, sound) |
| Detour 4 — MC-to-T2 | ROUTE AROUND | ~0.5 (brickd-design) | minutes (gate) | Gate-caught, retracted | mechanism design (reused at T1) |
| Detour 5 — route B / capstonerecon | ROUTE AROUND | 2 (capstonerecon, routefork) | ~half-day (07-15 AM) | **Refuted** (operator + routeverify type-error) | charts un-deleted, re-promoted |
| brickdfin | ATTACK | 1 | 07-14 19:43 | Architecture validated | landmine fix (hcT to T1) |
| **incidencepp** | ATTACK (paper) | 1 (pp) | 07-14/15 | **CRUX PROVEN** | the resolution + explicit atlas |
| brickdbuild/brickdcont/chart5 | ATTACK (build) | 3 | 07-14 eve→07-15 01:04 | Charts banked sorry-free | `transverseSchurGram`, exponent gate, charts 4/5, gluing |

**Aggregate.** Of the terminal window's ~34 h: the two large full-block detours (~10 dispatches
combined) produced **no surviving critical-path Lean** (Detour 2's central object was false;
Detour 1's lemma survives only as an off-path shell-0 statement). The direct attacks
(couplingfin + brickdfin + incidencepp + the three chart tides, ~6 dispatches) produced the
proof and all the surviving machinery. Roughly **half the terminal-endgame dispatches went into
routes around the crux; those dispatches account for essentially none of the banked critical-path
progress.**

Separately banked and surviving (legitimate coverage work, not avoidance): `hsecfix` (j=0
sector), `jreqbuild` (j=r arity-IH), `waisthunt` (waist reversal-coverage, empty hunt),
`gaugelift` (general-L exponent gate), Brick F wiring, D-A/B/C.

---

## FACTS — what the record says DROVE each detour (quotes at decision points)

**The justifying language is consistently the "simpler / doesn't-need-the-hard-thing" register:**

- Detour 1 adoption (`d6010ef90`, endgame-lanes): *"CRUX drastically SIMPLIFIED … **bypasses**
  [S3/coupled-residual]"* / *"the crux **does NOT need** S3/coupled-residual/radial (lemma 6) —
  the consumer needs only RHS<⊤⟹LHS<⊤ (not the tight RLCT comparator)"* / *"4 clean lemmas …
  **replace** the from-scratch σ-coupled module."*
- Detour 2 framing (finfin, endgame-lanes): the isolated wall is *"the last hard analytic brick
  … **labour not Mathlib-gap**"*; (wallfin) *"the wall is **LABOUR, NOT a Mathlib wall**
  (3-way corroborated)"*.
- Detour 3 seed (shelljhunt→rescopefin): *"buildable via subset/mnp"* — later corrected: that
  was "for FINITENESS, not the recursion."
- Detour 5 (capstonerecon, endgame-lanes): capstone = *"assembly + 2 **mechanical** fills"* —
  a grep-recon that *"never checked the bridge's TRUTH."*

**Was the crux explicitly deprioritized while known? Yes.** At Detour 1 the coupled-residual was
under active grind (step2) and had a fresh decorrelated cert (couplingfin, `43b84d7fa`, 22:50).
~1.5 h later cruxfin's "MAJOR SIMPLIFICATION" (`d6010ef90`, 00:17) explicitly declared it
unnecessary. The SD-7 discipline ("build everything above the gap, isolate the hard piece to one
sorry") is the standing frame that made deferral the default posture across the whole arc.

**couplingfin's early warning (verified from the record).** couplingfin's OBSTACLE-B ruling
(`43b84d7fa`, 2026-07-13 22:50) stated three things that the two full-block arcs then violated:
(i) *"full-box was an over-drop"* — Detour 2 dropped to full-box; (ii) the coupled-residual
**diverges off-shell** — thresholdhunt's kill mechanism was exactly off-shell low-rank-W
divergence; (iii) the shell is **load-bearing** — thresholdhunt: "shell load-bearing (couplingfin
vindicated)." The synthesis FRONTIER block dates it precisely: *"couplingfin flagged the off-shell
degradation uρ/2→5/2 a DAY before the full-block route was adopted."* By the clock: couplingfin's
warning preceded pradial (the second-arc adoption) by ~14 h and preceded cruxfin's first
simplification by ~1.5 h.

**The controller's own retrospective (operator-facing, discuss-at-close.md):**
- 2026-07-14: *"The head-split's hard analytic core (the coupled-residual / shear-CoV finiteness)
  was isolated and re-isolated several times (step2 → cruxfin's full-block detour → pradial →
  finfin → shearfin), each tide reformulating it cleaner without closing it. I flagged this as a
  ping-pong risk and set a stop condition."*
- 2026-07-14 (later), **"The honest cost"**: *"The full-block 'simplification' (cruxfin's,
  **adopted to avoid the hard shell-restricted coupled-residual = step2's OBSTACLE-A**) was a
  mirage: it avoided the hard piece by going off-shell, where the object is false. Several tides'
  work is on a false object. It was caught before the mint — but that's real effort spent, and
  the pattern (a confident 'simplification' that skipped the hard piece) is the lesson."*
- synthesis FRONTIER (T2-obstruction): *"PROCESS LESSON (mine): I celebrated 'crux SORRY-FREE,
  the milestone' for several ticks without probing whether pivotShell covered j≥1 — the
  confident-headline trap; couplingfin + the pivotShell=shell-0 docstring had the confound in
  plain sight."*

**A prior ignored precedent (same class, 2 weeks earlier).** discuss-at-close Item 75
(2026-06-29): the controller's *"conj-smooth stack is AVOIDED"* framing was corrected by a
decorrelated read of the real object, with the explicit lesson: *"a 'this heavy thing is avoided'
framing must be verified against the ACTUAL construction, not a premise/inventory description of
it."* The endgame's detours are that same lesson recurring at scale.

---

## INTERPRETATION — classified verdict

The team-lead's honest test: a detour justified by a **verified simpler object** is a good bet
that lost; a detour justified by an **unverified paraphrase** is avoidance.

Applying it, the terminal detours are **avoidance**, but with a precise and important twist:
**they were not built on unverified objects — they were built on verified objects whose
*sufficiency for the goal* was an unverified paraphrase.** The reviews were real; they measured
object-truth. The load-bearing claim was coverage/descent. This is the "instrument measured the
wrong object" failure, which review structurally passes over.

| Arc | Justified by | Classification |
|---|---|---|
| **Detour 1 (shell-0 full-block)** | A verified-true lemma (cruxreview + Codex PASS) + an **unverified coverage claim** ("discharges (a)/(b)"). pivotShell=shell-0 was in the docstring; j≥1 coverage was never probed. | **Avoidance** (coverage overclaim). Object true, sufficiency false. |
| **Detour 2 (off-shell full-block)** | Threshold asserted "design-confirmed ×3" — actually a=b=1-only (wallreview), then FALSE (thresholdhunt). Adopted **against** couplingfin's standing off-shell-degradation warning. | **Avoidance, clearest and costliest** (unverified paraphrase against a live cert). ~7 dispatches, false object. |
| Detour 3 (subset route) | shelljhunt's "buildable via subset/mnp" — true for *finiteness*, conflated with the *recursion*. | **Avoidance, honestly caught** (circularity self-flagged at landing). |
| Detour 4 (MC-to-T2) | Monte-Carlo evidence (unverified) vs an exact certificate. | **Avoidance attempt, gate-caught pre-build** (near-zero cost — the gate working). |
| Detour 5 (route B / capstonerecon) | capstonerecon: grep-recon, "never checked the bridge's TRUTH". routefork: a decoupled construction adopted unverified. | **Avoidance** (unverified paraphrase), caught by operator + routeverify before Lean. |
| couplingfin, brickdfin, incidencepp, chart tides | Decorrelated proof / exhaustive verification / explicit atlas. | **Direct attacks** — the surviving progress; incidencepp is the solve. |

**No terminal detour was a "verified simpler object that honestly lost."** The closest candidates
to a good-bet-lost (brickdfin's architecture validation, incidencepp's proof) were direct attacks
on the crux, not routes around it. Every route *around* the crux rested on an unverified
sufficiency/coverage/threshold claim.

**Is "hard-part avoidance" the right diagnosis vs "reasonable bets ex ante"? Both, weighted toward
avoidance.** The ex-ante-reasonable case is genuine and should be stated:
1. **The gates worked.** thresholdhunt caught Detour 2 before the mint; the reconcile gate caught
   Detour 4; the operator + routeverify caught Detour 5. No false object reached canonical.
2. **The SD-7 discipline is legitimate** and produced real surviving machinery (Brick D/F, the
   incidence charts, the coverage hunts).
3. **incidencepp proved the object bounded**, vindicating "attempt it math-first before calling a
   wall" — the charter's stance.

But the avoidance reading is stronger on the evidence:
1. **The warning existed and was decorrelated and specific** (couplingfin, before the first
   detour) and was overridden by a "simplification" that named the hard object as unnecessary.
2. **The same avoidance shape recurred five times** in ~34 h — including *twice* into full-block
   routes and *twice* into decoupling (Detour 2 and route B), the exact move couplingfin and the
   incidence machinery existed to forbid. Recurrence is the signature of a systematic pull, not
   independent reasonable bets.
3. **The reviews that "passed" measured object-truth, not sufficiency** — so "verified" did not
   mean "verified to close the goal," and the confident-headline framing traveled ahead of the
   solid layer (the disposition's named trap).
4. **The controller itself classifies it this way** in the operator-facing close ("adopted to
   avoid the hard … coupled-residual"; "a confident 'simplification' that skipped the hard
   piece").

**Cost, plainly.** ~half the terminal-endgame dispatches (~10 of ~20) went into routes around the
crux and produced essentially none of the banked critical-path progress; the coupled object was
finally *proven by a single decorrelated pen-and-paper pass (incidencepp)* once it was attacked
head-on — the attack that couplingfin's cert had pointed at from the first hour. The endgame's
dominant cost was the interval between naming the hard part and attacking it, spent going around.
