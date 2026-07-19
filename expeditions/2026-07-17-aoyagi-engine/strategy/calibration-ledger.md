# Controller calibration ledger — predict, then check the territory

Instrument (operator steer, 2026-07-19): some ticks are the controller asking questions of the
codebase — the mathematical EXPECTATION written down FIRST, then checked against the actual
Lean, hit/miss recorded. Some questions route to the cartographer (map) and elder (direction).
Purpose: catch map-territory drift that no seat would surface (seats answer their own
questions), and calibrate the controller's picture against reality.

Format per entry: the QUESTION · the PREDICTION(S) with confidence, timestamped BEFORE the
check · the TERRITORY (what the code actually says, cited) · the VERDICT + what it changes.

---

## Entry 1 (tick 196): the divergence half's exact shape — the flip-audit preview

**Question.** The altitude note §3 conjectures that at the hbox flip we hold a TWO-SIDED
characterization of the box-integral's critical exponent (finiteness at C/2 + the banked
divergence below), potentially reducing cited_aoyagi_dln's residue to a Watanabe-side bridge.
That reading depends entirely on what `routeMCore_box_diverges_achiever_full'` ACTUALLY says.
What does it say?

**Predictions (written before looking):**
- P1a (conf 0.6): its box family is the SAME structure `RouteMBoxThresholdFinite` quantifies
  over (the shared cubeBox/box datatype), so the two halves compose without a family bridge.
- P1b (conf 0.7): it is stated for arbitrary M (∀ M, or parametric M with the achiever
  tStar M), not only a canonical instance.
- P1c (conf 0.5): divergence is formalized as ¬(the finiteness Prop at the off-threshold c')
  or an unbounded-below integral statement — NOT an independent Tendsto-to-∞ over a filter.
- P1d (conf 0.9): the threshold constant in it is the LEDGER quantity (minAdm M / the
  achiever's Mval), not an independently-defined geometric constant.

**Territory.** (filled after the check — see below)

**Verdict.** (below)
**Territory** (read tick 196):
- Divergence: `routeMCore_box_diverges_achiever_full' (M) (hpos : 1 ≤ minAdm M) (hMpos : ∀ s,
  0 < M s) (hne : deepestCoords nonempty) (c') (hc' : (minAdm M)/2 ≤ c') (ε) (hε : 0 < ε) :
  BoxDiverges M c' ε` where `BoxDiverges = ∫⁻ x in cubeBox (routeMAmbient M) ε,
  ofReal (|routeMCore M x| ^ (−c')) = ⊤` (RouteMAchieverFullHNoFree:40; Dispatch:47).
- Finiteness: `RouteMBoxThresholdFinite M = ∀ c' < (minAdm M)/2, routeMLayerBoxIntegral M c' 1
  < ⊤` where the integral is `∫⁻ A in paramsBoxM M 1, ofReal (frobSq (prod M A) ^ (−c'))`
  (RouteMBoxReduction:165,62). The hfin consumer (:168-171) dominates `∫_{routeMBaseNbhd}
  |routeMCore|^{−c'}` by the box integral via `routeMCore_le_matBox`.

**Verdicts:**
- P1a **MISS (instructive)**: the two halves are NOT over the same integral — divergence reads
  |routeMCore| over cubeBox ε; finiteness reads frobSq∘prod over paramsBoxM, meeting the
  routeMCore integral only THROUGH the reduction lemma. The two-sided reading survives but at
  the ROUTEMCORE LOCAL integral, and the flip-audit must check the domain bridge (cubeBox ε vs
  routeMBaseNbhd inclusion at small ε; the T=1 vs ε parameter mismatch) — two concrete lemmas
  to verify banked, else small new glue.
- P1b HIT (∀ M; note the divergence side DOES assume hMpos width-positivity — fine for DLN,
  but the spine's width-free generality does NOT extend to the divergence half; record).
- P1c ~HIT (= ⊤ of the lintegral — the "unbounded integral" form).
- P1d HIT (threshold = minAdm M / 2 on BOTH sides; divergence holds AT the threshold, ≥ not >).

**What it changes:** the altitude-§3 conjecture SURVIVES REFINED: at the flip we hold
finiteness (c' < C/2) + divergence (c' ≥ C/2) for the routeMCore local integral, modulo the
domain-bridge check. The cited_aoyagi_dln residue then = (a) localization glue (the DLN loss ↔
the routeMCore family — partially banked in R1ResolutionGeneral?) + (b) the zeta-bridge (local
integral threshold ↔ the RlctInterface's rlct). NEITHER is Aoyagi's resolution computation.
Flip-audit checklist seeded: the two bridge lemmas + the localization layer's scope + the
hMpos thread. Calibration score: 3/4 predictions, with the miss exactly where the picture was
too coarse (integrand/domain identity assumed where a reduction mediates).

---
## Entry 2 (tick 198): the flip-site positivity question — does hbox's ∀M survive o5's hMpos?

**Question.** The move-at-landing batch will thread hMpos through the attainment chain. Does
that condition reach hbox (∀ M, RouteMBoxThresholdFinite M — consumed by the payoff as a bare
∀M), and if so, is the zero-width case separately dischargeable or does the payoff already
exclude it?

**Predictions (written before looking):**
- P2a (conf 0.7): the DLN fit witness / EngineDriver forms route-M instances whose reduced
  widths are POSITIVE by construction (the route localization only makes sense for r strictly
  below the local widths), so the payoff side never needs zero-width instances.
- P2b (conf 0.6): hbox is nevertheless consumed as a literal ∀M (no positivity guard in the
  Prop), so IF engine_box_threshold_finite's discharge gains hMpos, the flip needs an explicit
  zero-width side-case.
- P2c (conf 0.65): RouteMBoxThresholdFinite at zero-width M is TRUE cheaply (Real.rpow
  convention: 0^(−c') = 0 for c' ≠ 0 ⟹ integrand ≡ 0 on the degenerate product ⟹ integral
  0 < ⊤) — a junk-value discharge, no engine needed.

**Territory.** (next)
**Territory** (read tick 198):
- `aoyagi_learning_coefficient_gen (H) (r) (B) (hB) (hr) (hL) (hL2) (hpos : ∀ s, r < H s)
  (hbox : RouteMBoxThresholdFinite (fun s => H s - r))` — HeadlineGenAssembly:55-59.
- The fit witness (EngineDriver:59-65) carries the SAME `hpos : ∀ s, r < H s` and instantiates
  `engine_box_threshold_finite (fun s => H s - r) hL`.
- engine_box_threshold_finite is per-M `(M) (hL)` — EngineDriver:44.

**Verdicts:**
- P2a HIT, stronger than predicted: the payoff doesn't just supply positive widths naturally —
  `hpos : ∀ s, r < H s` is ALREADY an explicit hypothesis of the _gen headline, and the hbox
  instance's widths are H s − r > 0 by exactly it.
- P2b **MISS (good news)**: hbox is NOT consumed as a literal ∀M — the _gen signature takes the
  SPECIFIC instance `RouteMBoxThresholdFinite (fun s => H s - r)`. There is no ∀M Prop to
  preserve and NO zero-width side-case anywhere. (The journal/memo's recurring "hbox = ∀M,
  RouteMBoxThresholdFinite M" shorthand is imprecise — the slot is parametric; correct the
  record where it matters.)
- P2c MOOT (the junk-value discharge is never needed).

**What it changes:** the move-at-landing batch is CONFIRMED SAFE: engine_box_threshold_finite
gains hMpos and the fit witness supplies it FREE from its existing hpos (r < H s ⟹
0 < H s − r) — zero new obligations, zero side-cases, the exact composition the tick-197
hypothesis-form ruling was chosen for. t06's decision-ask (b) is now definitively answered.
Score: 1 hit / 1 instructive miss / 1 moot — the miss again where the picture used a slogan
("∀M") in place of the actual signature.

### Entry 1 addendum (tick 200, elder-alt1's territory read — the check the entry skipped)
PROCESS MISS, recorded: entry 1's "What it changes" conclusion (the residue list) was written
WITHOUT reading cited_aoyagi_dln / rlctAt / the codim bridge — un-territory-checked inference
inside the calibration ledger itself. The elder read them: (i) codimRepCanonical(fibre) =
cCodim = minAdm is BANKED axiom-clean (Brick A + minAdm_eq_cCodim — STRONGER than the entry
assumed; staled a compass fork-11 parenthetical, now fixed); (ii) rlctAt (Foundations/Rlct:71)
is definitionally the critical exponent — "rlct = critical exponent" is not a theory to build
for the VALUE; (iii) the corrected residue: interface-instantiation + localization glue + nbhd
bookkeeping. DIRECTION CORRECTED: divergence = UPPER bound on rlct (single witness, easy);
hbox/finiteness = LOWER bound (whole-neighbourhood control, the hard singular-locus half) —
the entry (and altitude §3) had foregrounded the wrong half; the engine's coverage work IS the
runway's hard part. θ/order excluded (meromorphic continuation, not Mathlib-adjacent).
Ledger lesson #2 (same class as both prior misses): conclusions drawn past the last
territory-checked statement must be MARKED unchecked — the ledger now does so by convention.

---
## Entry 3 (tick 201, OFFICE-ROUTED — cartographer-4): the carrier-adjacent map, two SPLIT verdicts

**CQ1** (expectation: no fold-of-localSubs anywhere in Engine): **SPLIT.** HIT narrowly — the
construction-side accumulator is absent (leafOfState.chartMap := id; struck moot). MISS
literally — TWO proven fold-of-localSubs recursions exist as SPEC functions over a built tree:
leafPaths/edgesLeafPaths (ResolutionTree:218/223, `acc ∘ s.localSub`) and
leafPathImages/edgesImages (PivotCoverFold:57/61), both consumed by the cover proof.
RECALIBRATION: the carrier POPULATES the localSubs an EXISTING fold reads — it builds no fold.

**CQ2** (expectation: leafPaths enumerates root→leaf EDGE LISTS, the t_geo template): **SPLIT.**
HIT — it exists and its recursion SHAPE is the template. MISS — its payload is the COMPOSITE
fold (`List (LeafData M × (Params M → Params M))`), not edge lists; no root→leaf edge-path
enumerator exists (stepEdges gives flat pairs). geometricLeafPaths = the leafPaths recursion
shape with a DIFFERENT accumulator payload (edge/d_center data), not a verbatim reuse.

**Class note:** both misses are the same signature-vs-slogan class as entries 1-2's misses
(right object, wrong payload/quantifier). Three-for-three on the class — the convention
(check the SIGNATURE, not the name) is now the ledger's standing first question.

**Drift-risks banked by the office** (routed to owners): ShearReconcile.lean:6-18 docstring
still sells single-ψ (refuted; retire-note owed with coverage's next touch);
chartBridge_buildTree docstring (EngineObligations:35-52) describes the STRUCK spine-fold
carrier plan (rewrite owed at the move-at-landing batch); reuse-index sorry-count corrected.

---
## Entry 4 (tick 214, office-routed — pnp-slot): the slot-stability hypothesis

**Prediction (tick 208, written pre-check):** substitution-in-place ⟹ a divisor's flat
coordinate = its immutable birth corner ⟹ the mechanism = one immutable per-divisor field
with congruence maintenance (conf ~0.7 implied by commissioning the cheap-mechanism framing).
**Territory (the cert):** T-slot = YES — proved-by-page-read + exact-sim across every
transition kind; the ONLY u-slot writes are births into fresh corners. HIT, fully.
**The half I did NOT predict** (asked as a question, honestly): recoverability from divProfile
= NO — exact witness: the same profile born at different corners in different leaves (the
θ-multiplicity surfacing at the slot level!); so the field is NECESSARY, not just convenient.
**Coherence bonus:** the case-1(2) rescale-and-rename-in-place IS the R-b α_d gauge seen from
the slot side — two independent certs (ψ-mix, slot-stability) describing one object.
**What it changes:** the carrier remainder is now FULLY sized: divBirthCoord (immutable,
birth-corner arithmetic (layer,cleared,cleared), congruence maintenance) + qNodeOf assembly
per the spec — small + intricate-but-mapped. divCoord's real content finally lands as an
injective map (births at distinct diagonal corners). Score: hit on the mechanism; the
question-not-prediction on recoverability was the right epistemic posture (it was genuinely
open — and NO).

---
## Entry 5 (tick 219): the R5 mint-repoint mechanics — what does "repoint canonical" actually require?

**Question.** After chartBridge_buildTree fills and hbox flips clean-three, R5 says "repoint
canonical → _gen (+ the L=1 separate fold) + the ENFORCED axiom-gate". What does the code
actually require there?

**Predictions (written before looking):**
- P5a (conf 0.6): the canonical unsuffixed `aoyagi_learning_coefficient` exists in the
  RlctPayoff/Validate layer, stated via the CITED hypothesis (cited_aoyagi_dln), separate from
  `_gen`; the repoint = re-proving the canonical NAME via `_gen` + engine_box_threshold_finite,
  not editing `_gen`.
- P5b (conf 0.55): the L=1 case lives as a separate banked theorem in HeadlineL1Mint.lean
  (since `_gen` needs 2 ≤ L), and the repoint composes an L=1-vs-L≥2 case split.
- P5c (conf 0.7): the repoint needs NO new mathematics — composition + case split + hypothesis
  supply only, all pieces banked; the only NEW artifact is the #guard_msgs enforced gate.

**Territory.** (next)
**Territory** (read tick 219): the canonical `aoyagi_learning_coefficient` (Skeleton.lean:1685,
hL : 1 ≤ L + hpos) is PROVEN via the OLD L2 skeleton (deepest_point_reduction ▸
product_reduction) — the sorry-carrying route (the compass's "5 skeleton-rung sorryAx"); it
does NOT take cited_aoyagi_dln as a hypothesis (the cite lives apart, in RlctPayoff). The L=1
endpoint `aoyagi_learning_coefficient_L1` is banked UNCONDITIONAL sorry-free, AND the ∀L≥1
case-split wrapper `aoyagi_learning_coefficient_prestage` is ALREADY PRE-STAGED
(HeadlineL1Mint) — explicitly "flagged for the controller to re-point at mint" — but its L≥2
arm consumes `hDescent : DecoratedDescent` via _gen_of_descent (the PRE-TOMBSTONE route).

**Verdicts:**
- P5a PARTIAL MISS: canonical-exists + repoint-not-edit-_gen right; "stated via the CITED
  hypothesis" WRONG — it's +sorryAx via the old skeleton, the cite was never in its cone
  (which the compass says verbatim; the slogan-vs-signature class AGAIN, 4th instance).
- P5b HIT+: L1 banked AND the wrapper pre-staged beyond expectation.
- P5c HIT with a wrinkle THAT MATTERS: no new math, but the prestage's hDescent arm is STALE
  relative to compass fork 6's tombstone (DecoratedDescent route tombstoned at adoption; the
  direct fit is _gen + engine_box_threshold_finite, as the EngineDriver example already
  demonstrates). THE MINT THEREFORE = (i) rewrite the prestage's L≥2 arm to the direct engine
  route (do NOT resurrect DecoratedDescent), (ii) re-prove the canonical name by the wrapper,
  (iii) the #guard_msgs enforced gate. Slightly more than the file's advertised "one-exact
  fill", still zero mathematics.
**What it changes:** the R5 checklist gains the precise stale-arm item; recorded in priorities.
Score: the recurring miss-class (slogan for signature) now 4/4 across entries — the convention
is doing its job; conclusions stayed correct each time BECAUSE the check ran before execution.
