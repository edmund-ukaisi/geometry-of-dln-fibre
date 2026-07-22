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

---
## Entry 6 (tick 224): the cordon census — what does the live-sorry map look like NOW?

**Question.** The cordon (pre-PR) classifies every sorry LIVE-frontier vs fossil. After the o5
closures, what is the actual census?

**Predictions (written before looking):**
- P6a (conf 0.8): the Engine directory = EXACTLY 3 sorries — chartBridge_buildTree
  (EngineObligations), realizedProfiles_eq_clearableAdm (ClearableReify, R7), the
  canonicalResolution224 witness conjunct (CanonicalWitness224).
- P6b (conf 0.6): Skeleton.lean's old L2 route carries ~5 sorry-carrying rungs (the compass's
  "5 skeleton-rung sorryAx" the mint will orphan into fossils).
- P6c (conf 0.5): the repo-wide live-sorry total is 20-24 (the cartographer's earlier fossil
  census said 24 tree-wide; a few closed since).

**Territory.** (next)
**Territory** (tick 224): Engine = EXACTLY the 3 predicted (EngineObligations:53,
ClearableReify:78, CanonicalWitness224:135). Skeleton.lean live-sorry pattern = (checked
separately — see below). Repo-wide live pattern = 24 lines / 13 files.

**Verdicts:** P6a HIT exactly (3/3, named). P6c HIT (24, top of range — the cartographer's
fossil census figure holding steady). P6b: the naive string count (8) includes docstring
mentions; the live-pattern count on Skeleton.lean recorded alongside — the "5 rungs" claim is
the compass's own (sorryAx-cone, not raw sorries); VERIFY AT MINT with #print rather than grep
(the cone is the truth, grep is the approximation — the very slogan-vs-signature class again,
caught in-flight this time).
**What it changes:** the cordon's census base is CURRENT and small: 3 Engine (2 close with the
tide + the corollary; 1 = R7 owed), the Skeleton fossils orphan at mint, ~21 others enumerated
for LIVE-vs-fossil classification. No surprises; the cordon is a bounded pass.

---
## Entry 7 (tick 233): the (D)-landing shape — will "additive, no re-ripple" survive contact?

**Question.** Gate #10 requires clause (D) IN the ChartBridge type before the discharge. The
re-typing batch claimed adding (D) later is "a def-only touch: consumers project ChartBridge
opaquely... no re-ripple — VERIFIED by this build". Will that hold at the actual landing?

**Predictions (written before looking):**
- P7a (conf 0.75): (D) lands as a fourth conjunct pinning the atlas to the geometricLeafPaths
  fold (each piece's chartMap = a fold composite of t's edges — the fails-on-fake form).
- P7b (conf 0.7): the no-re-ripple claim holds ONLY IF region_glue_of_chartBridge's destructure
  is arity-robust — if the batch wrote an `obtain ⟨atlas, h1, h2, h3⟩`-style FIXED-ARITY
  pattern, adding a conjunct BREAKS it (one line, but a re-elaboration of the proven glue
  composition — exactly what the full-batch gate exists to catch). My guess: the destructure
  IS fixed-arity (anonymous-constructor style) and the landing will touch that one line.
- P7c (conf 0.6): gate #10's cordon check is greppable (the conjunct present in EngineDefs
  before EngineObligations:53's sorry is replaced).

**Territory.** (next)
**Territory** (tick 233): ChartBridge (EngineDefs:96) = ∃ atlas, (A) ∧ (B) ∧ (C) — a
THREE-conjunct existential body. region_glue_of_chartBridge's consumption
(RegionGlueAssembly:107) = `obtain ⟨atlas, ⟨U, hUopen, hUlocus, hUcover⟩, hleaf, hexp⟩` —
a FIXED-ARITY anonymous-constructor pattern.

**Verdicts:** P7b **HIT** — the destructure is fixed-arity, so the (D) landing WILL break that
one line (a trivial `, -⟩`-style edit + the glue's re-elaboration, which the full-batch gate
covers — but the batch should PLAN the line, not discover it as a build break). The re-typing
batch's "no re-ripple, VERIFIED by this build" was verified for a (D)-LESS world — the claim
quietly doesn't extend to the (D) landing (the slogan-vs-signature class, 5th instance: a
verification's scope inherited beyond its regime). P7a/P7c: OPEN — verify at the landing/cordon.
**What it changes:** one pre-staged line in coverage's (D) batch (both files are its — relayed);
zero schedule impact BECAUSE caught pre-landing.

---
## Entry 8 (tick 239, seat-surfaced): the per-edge/per-node q conflation — the first DESIGN-class miss

**Not a prediction entry — a miss POST-MORTEM (the ledger records misses wherever found).**
The seam-Q4 field-lock decided qNodeOf's factor is the PER-EDGE center dim; t06 built qEdgeOf
to it; the controller relayed it; coverage locked to it; gate-9's "per-edge partition"
amendment was ambiguous between EMISSION (per-edge, correct) and the COVER's q (per-NODE,
missed). Coverage's cover-assembly grounding caught it: node_pivotCover_of_atom takes ONE q
of dim d_center (the full family; cert-psi-mix's "⋃ over the FULL family sharing one q" —
the per-edge things are the GAUGES). Sibling edges' different-dim qEdgeOf's cannot feed one
cover atom; per-edge sub-covers reopen the exact mixed-sector gap R-b closed.
**Class:** NOT slogan-for-signature — a new class: TWO STRUCTURES ON THE SAME INDEX SET
(emission-partition vs cover-family) conflated because both are "per-edge-flavored". Four
parties missed it; the assembly's GROUNDING caught it (the verifier hierarchy again — certs <
gates < the build).
**Cost:** small — pieces 1-2 rework (a q-swap), qNodeOf = a new bounded wrapper (qOfCenter is
parametric — t06's design absorbs the fix without change), injectivity via DivBirthInv
(t07's invariant supplies exactly the u-corner-vs-block distinctness). No proof wasted; the
cover build was HELD pre-waste.
**Lesson:** when a design question asks "per-X or per-Y?", enumerate WHICH STRUCTURES ride
the answer (here: the emission, the gauges, the q, the counts — four structures, not one
answer) — a composite question answered as one bit is a conflation waiting to fire.

## Entry 9 (tick 258) — the dim-0 rollover discharge shape [self-checked]
QUESTION: how would t09 resolve the rollover edge case (dim-0 nodes, realCNode empty) in
the fidelity capstone?
EXPECTATION (relayed to t09 at assignment, ~70%): a dim-0 SHORT-CIRCUIT branch inside
cNodeOf_eq_realCNode (a vacuous-dim node names no coordinates — definitional), vs ~30% a
nodeOccMin = none discharge added to RealCNodeFacts.
TERRITORY (commit ee9c5934e): NEITHER exactly — t09 WEAKENED THE HYPOTHESIS instead:
cNodeOf_eq_realCNode now takes `Function.Injective (realCNode …)` directly, with TWO
suppliers (realCNode_injective_of_facts for case-1/case-2; a new vacuous
realCNode_injective_of_dCenterOfNode_zero for terminal/rollover). No branch added to the
capstone, no facts-side discharge; the remaining reachability supply shrinks to case-1 only.
VERDICT: partial hit (the vacuous-at-dim-0 INSIGHT was right; the LOCATION was wrong — I
put the case split inside the theorem, t09 moved it into the hypothesis).
WHAT IT CHANGES: prefer WEAKEST-HYPOTHESIS refactors over in-proof case discharges when an
edge case is vacuous — the theorem stays uniform, the case split lives in cheap suppliers,
and consumers pick the supplier per node class. Same lesson-family as the pointwise realCNode
crack: restructure the STATEMENT so the hard case dissolves, don't fight it in the proof.

## Entry 10 (tick 271) — the kill-condition's mechanics in the actual Lean [self-checked]
QUESTION: in the current geoChartMap, what determines which flat coordinate gets the u-role
(the ^(dCN−1) det factor)? (Load-bearing for the elder's charge-2 options: the cert's
diagnosis must be a chart-vs-ledger REFERENT mismatch for diagonal-normalization to be the
clean fix.)
EXPECTATION (~85%): the FAN PIVOT — geoChartMap conjugates pivotChart ⟨g.pivot⟩ through
qN g.node, landing the u-role on cNodeOf g.node ⟨g.pivot⟩; divBirthCoord (the state-level
diagonal) enters ONLY the ledger side (leafOfState.divCoord = birthFlatCoord ∘ …).
TERRITORY (GeoChart.lean:54-61 + the header): HIT — geoChartMap = q.symm ∘ Prod.map
(pivotChart ⟨g.pivot, hp⟩) id ∘ q inside the dite; the u-role is exactly the fan pivot; the
ledger references divBirthCoord independently. The cert's J_Φ = L·(z_diag/z_pivot)^b is
literally the gap between these two referents.
COROLLARY (for the elder, not a ruling): diagonal-normalization is mechanically LOCAL to
geoChartMap — conjugate by the (pivot ↔ diag-index) transposition inside the same dite
(|det swap| = 1; per-copy images stay distinct since the swap differs per copy, so the
cover's disjointness story should survive). The option is at least well-formed in the code.
WHAT IT CHANGES: nothing yet (the ruling is the elder's); confidence that the fix is a
small chart-side edit rather than an emission rewrite rises. Entry class: model-of-the-
construction verification — 1/1 this arc.

## Entry 11 (tick 286) — the design-correct / transcription-stale miss class [event-driven]
EVENT: t14's pre-grind provability check found the LOCKED fold headline FALSE at generic s
(witness: a terminal s with a pre-born divisor — chartMap = id, LHS = 1, RHS = 0 at w = 0).
WHAT THE LAYERS MISSED: finding-1's ruling, the addendum's own text, AND the docstring all
said conRoot — the DESIGN was right in three places; only the Lean binder (∀ s) drifted. My
tick-263 gate, the elder audits, and t11's lock all reviewed the DESIGN artifacts and passed;
none re-read the binder against them. Same family as the stale hDescent arm (a settled
ruling not transcribed) — but here the drift was INSIDE the freshly-written statement, not
legacy code.
WHAT IT CHANGES: (i) the statement gate must include a BINDER-vs-DESIGN diff (read the ∀s/
hypotheses against the design doc's scope line — 30 seconds); (ii) t14's habit — check
provability BEFORE grinding, hunt a witness for the negation at the boundary cases (terminal
states, empty folds) — is the correct last line and goes in the formaliser briefs as
standard; (iii) the sorry-mask pattern (tick 284) and this are the SAME week's lesson from
two sides: a sorried statement is invisible to green builds AND to design review — only
provability checks and integration gates see it.

## Entry 12 (coverage-t08 seat-surfaced): obligation-statement counter 7→8 — the elder's own unfillable gate form

**Obligation-statement instance #8** (the slogan-vs-signature family; this one owned by the
ELDER, per its charge-4 ruling). The gate-#10 form as ruled — "clause (D) must be a conjunct
IN `ChartBridge`'s type (`EngineDefs`), phrased against `geoChartMapNorm`/`diagTargetOf`" — is
UNFILLABLE: those names sit ABOVE `EngineDefs` in the import DAG (GeoChart → ShearReconcile →
PivotCoverFold → EngineDefs; QNodeCarrier → … → EngineConstruction → EngineDefs), and
`ChartBridge` is pinned low by `CanonicalResolution`. The obstruction was verified by
import-chain trace before any edit (the arity-edit charge-item falling out MOOT was the tell
the shared model had (D) as a literal EngineDefs conjunct).
**Elder's phrasing (quoted, charge-4 ruling):** the form "was ruled without checking the
imports; the intent survives via the projection" — the R-split makes the gate STRONGER than the
original: `chartBridge_buildTree` becomes the PROJECTION of `chartBridgeFaithful_buildTree`,
putting (D) on the payoff's proof CONE (undroppable), which the in-type conjunct never was.
**Class:** slogan-for-signature — a design GATE stated at the slogan level ("(D) in the type")
without checking the type's actual import position could carry the named geometry. Same family
as the earlier instances (a specification written to intent, refuted by the mechanical signature).
**Caught by:** the executor's pre-edit DAG check (verifier hierarchy again — the ruling < the
build's import graph). No proof wasted; surfaced before the first cycle.
**Lesson:** a gate that names WHERE a fidelity lands (a module/type) must be checked against the
import DAG at ruling time — "put X in type T" is unfillable if T sits below X's dependencies.

## Entry 13 (tick 339, 2026-07-20) — the LeafPullback seam: will it mate?
**Question.** When loss-t15 closes `leafDiagFrob_geoAtlasNorm` (GeoAlphaGauge:562), does
ChartBridgeFaithful:82 discharge by pure composition, or is there a statement-shape mismatch
(per-piece quantification, geoAtlas vs geoAtlasNorm, α-wrapper) needing new glue?
**Expectation (before reading).**
- 0.80: the :82 sorry supplies a per-piece `LeafPullback c` conjunct for pieces of the SAME
  atlas the buildTree walk emits; the chain is leafDiagFrob_geoAtlasNorm → per-piece
  `LeafDiagFrob` → `leafPullback_of_diagFrob` → `LeafPullback`.
- 0.75: mates with NO new glue beyond what GeoAlphaGauge already exports (geoAtlasNorm was
  defined there precisely as the α-composed atlas).
- 0.50: a small adapter (norm-piece ↔ emitted-piece identification) exists already; if not,
  it is a one-lemma gap, not a redesign.
**Risk probed.** The tick-284 class: a sorried statement going stale invisibly (here :82 has
been sorried since the R-split; loss-t15 builds against GeoAlphaGauge's frontier, not :82).
**Verdict (after reading).** PARTIAL MISS — and the miss is the product.
- The 0.75 "no new glue" clause: MISS. The seam does NOT mate purely. `geoAtlas t =
  leaves (tGeo id t)` (gauge pinned to id); `geoAtlasNorm alphaGauge t = leaves (tGeoG
  alphaGauge id t)` — DIFFERENT atlases (same images/ledgers; different chartMap/srcBox).
- Sharper than expected: t14's ENTIRE proven inventory (ledgerProps, ae_injOn,
  leafJacobian — no `tGeoG` anywhere in GeoFoldRegroup) is over the id atlas; LeafPullback
  arrives over the α atlas; clause (D) conjunct 1 pins `atlas = geoAtlas t` by `rfl`.
  LeafPullback at g = id is likely FALSE (the α gauge exists because the residual does not
  clear at id) — so the witness must move to the α atlas, which breaks (D)₁ as stated.
- The 0.50 "adapter named" clause: HIT — GeoAlphaGauge's pre-staged wiring note names the
  `geoAtlas`/`geoAtlasNorm alphaGauge` cover-transfer lemma, "landed after both lanes". But
  the note names only the COVER transfer; the ledger-props/ae-inj/LeafJacobian transfers +
  the (D)₁ amendment are unpriced.
**What it changes.** The assembly is not a plug: it needs (i) a (D)₁ statement amendment
(the cordoned, AxCheck-watched R-split gate — statement-first + elder eyes), (ii) a transfer
batch (cover image-invariance; ledger preservation through tGeoG — resRank-zero transfer
already proven, pattern exists; ae-inj through the det-1 shear — inj-t16's comp helpers;
Jacobian det-1-transparency — needs α to FIX the div coordinates, check). Charged the elder
NOW (tick 339) rather than at lane completion — the tick-284 lesson applied forward.

## Entry 14 (tick 350, 2026-07-20) — what does stepRollover do to the ledger? (serves Q2b, the frontier)
**Question.** The clearedOf frontier model needs rollover semantics. What does stepRollover
actually change, and does a layer complete at exactly cleared = widthMinUpto M (layer+1)?
**Expectation (before reading).**
- 0.80: stepRollover sets layer := layer+1, cleared := 0.
- 0.70: ALL divisor fields (numDiv, divExp, divTilde, divProfile / birth data) unchanged —
  consistent with t14's rollover-neutral det maintenance (ledgerMonomial_stepRollover).
- 0.75: the walk increments cleared by 1 per clearing step and re-checks the guard each
  node, so at rollover cleared = widthMinUpto M (layer+1) EXACTLY (first hit, no overshoot).
- Consequence if all hold: the running-total frontier IS ledger-expressible with no history:
  resolvedCount s = Σ_{ℓ' < s.layer} widthMinUpto M (ℓ'+1) + s.cleared — the completed-layer
  counts are M-derivable constants, not state history. This would hand loss-t15 a clean
  clearedOf candidate.
**Verdict (after reading).** 3/3 HITS + two construction facts worth more than the hits.
- stepRollover (EngineConstruction:197-198): ⟨layer+1, 0, numDiv, divExp, divProfile,
  numGen, genDivExp, divBirthCoord⟩ — full ledger carry, exactly as expected (0.80/0.70 ✓).
- The dispatch (:1926): rollover fires at widthMinUpto M (layer+1) ≤ cleared, checked per
  node; clearing steps advance cleared by exactly 1 from 0 — first hit is EQUALITY (0.75 ✓).
- FACT 1 (the nuance the frontier model must respect): case-11 does NOT advance cleared
  (t14's child literal keeps s.cleared) — the re-merge works at an EXISTING divisor's
  diagonal; only case-2/case-12 (stepAppendAdvance) advance the frontier.
- FACT 2: stepAppendAdvance snocs divBirthCoord with (s.layer, s.cleared) (:190-193) — the
  birth coordinate IS the (layer, within-layer-pivot) pair; and tildeOf(setTail layer
  cleared T) ≤ cleared (:146-148) — clearing levels are bounded by the birth-time frontier.
**What it changes.** The running-total candidate resolvedCount = Σ_{ℓ'<layer}
widthMinUpto(ℓ'+1) + cleared is ledger-expressible (no history needed) — BUT the map from
the count to WHICH Fin (M 0) positions (the reindexing) is the real remaining content, and
any model must respect fact 1. Facts handed to loss-t15 for the clearedOf derivation.

## Entry 15 (tick 353, 2026-07-20) — THE MISS: entry-wise-full InvVal ratified false (elder-directed entry)
**What happened.** At the value-walk design gate (~tick 340) I ruled the entry-wise steer
(b): "cleared cells of prod M (acc w) diagonal = bmon". The elder co-ratified; the leaf
discharge proved green; the shape survived TWO more gate rounds (payload def, option-C).
loss-t15's third-round provability check then showed it FALSE at intermediate states: the
paper's invariant is the three-factor form (worked.tex:478-479) with a RAW trailing
∏_{s>S}C factor, so full-product cleared rows are b_i·(trailing row), not diagonal —
diagonal only at the leaf (trailing empty), which is exactly where all prior verification
(the banked leaf discharge, the abstract battery's terminal reads) had looked. Worse (the
elder's Q3): the full product's residual region is CONTAMINATED by the trailing, so the
clearing's a,b reads were also aimed at the wrong object. Two unsoundnesses in a ratified
statement.
**Why it was missed.** Every instrument that touched the claim (leaf discharge, terminal
battery reads, my design ruling, the elder's confirm) evaluated it ONLY where the trailing
factor vanishes. The obligation-statement class: a statement that is true on the boundary
you tested and false in the interior you never entered. Same family as the tick-286
generic-s falsity (true at the tested scope, false one binder wider).
**What saved it.** The seat's own provability-check-before-grinding (entry-11 discipline)
— it derived the intermediate form from the cert BEFORE grinding case-2 against a false
target. Zero Lean wasted; the fix (prodPrefix re-base) is near-one-token on the defs.
**Lesson.** When ratifying an invariant, ask WHERE it has been evaluated: if every
verification sits at a degenerate boundary (empty trailing product, terminal state, zero
case), the interior is UNTESTED regardless of how many instruments agree. Add to statement
gates: "name the state at which each supporting verification was run; if all coincide,
demand one interior instance."

## Entry 16 (tick 360, 2026-07-20) — THE MISS: tick-341 keep-cube ruling REFUTED by pnp-cover
**What happened.** At t14's statement gate (tick 341) the disk showed tGeoG inheriting
srcBox = cube where fork-15's design said srcBox = g⁻¹(cube). I ruled KEEP-THE-DISK on two
grounds: (a) changing tGeoG collides with loss-t15's live walk; (b) "no math need — (B)'s
bound is trivially cube-satisfied". pnp-cover's exact hunt refuted the ruling: clause (A)
is FALSE over cube (open gap region around the diagonal; every pivot's preimage of
y=(t,t,t,t) needs a source coordinate of 2). The design clause was LOAD-BEARING — it
carried the image-invariance obligation the cover transfer needed; the disk's deviation
silently dropped it, and (b) looked only at the (B) bound, never asking what (A) needed.
**Why it was missed.** "Disk wins over design text" was applied as a default. The right
question was: which of design/disk carries a PROOF OBLIGATION consumed elsewhere? The
design's srcBox = g⁻¹(cube) existed precisely to make the cover g-image-invariant (fork 15
says so verbatim); overriding it required re-deriving the cover, which the elder's
too-glib open-homeo pricing (its own recorded miss) appeared to supply. Grounds (a) was
also over-priced (the elder later showed the walk core is domain-agnostic).
**What saved it.** The layered instruments: t14's stop-and-surface (the ρ-shrink failing),
the elder's refutation of the spectator route + its demand for a decorrelated hunt, and
pnp-cover's exact witness — all BEFORE any cover code was written. Cost: a bounded re-bank
of 2b/2c; zero wasted cover-grind.
**Lesson.** When disk deviates from design, neither wins by default: enumerate the proof
obligations each side carries (grep the design clause's WHY — fork 15 stated it) and check
who consumes them. A deviation that "only" changes a definition can silently drop an
invariant another clause was designed to provide.
**Entry 16 addendum (tick 363, elder-directed multi-party record).** The same deviation
defeated TWO independent ratifications: the controller's tick-341 keep-cube AND the elder's
charge-2 open-homeo/shrunken-U' — neither instrument caught the dropped image-invariance
obligation; the DECORRELATED HUNT did. The compass counsel (coverage's cover = a universal
claim; the gate reads a decorrelated hunt, never an in-house witness) is not redundancy —
it is the only instrument class that fired. Corollary now applied forward: the collection
lemma's gate refuses the shallow (2,2,2)/single-α confirmation for the same reason.

## Entry 17 (tick 367, 2026-07-20) — the terminal-frontier subtlety (controller construction read)
**Question.** With t14 silent on clearedOf (4 asks), derive the frontier semantics myself.
Expectation walking in: the elder's reset-per-layer + loss-t15's leaf discharge (hall = all
rows resolved at a leaf) compose cleanly.
**Finding.** They DON'T compose naively: the terminal state arrives via rollover with
cleared = 0 (dispatch checks layer = L first; matrices are 0..L-1), so a current-layer
frontier marks NOTHING cleared at every leaf — hall unsatisfiable. The rescue is a
distinction neither prior ruling named: CONTAMINATING vs NON-CONTAMINATING rollovers. A
mid-walk rollover S→S+1 (S+1 < L) brings matrix S+1 into the prefix and honestly resets
the frontier (the elder's precision-2, leg-ii verified). The TERMINAL rollover into layer
L brings no new matrix (prefixCol caps at L) — layer L-1's completed frontier
(= widthMinUpto M L = the all-widths running min) honestly PERSISTS into the leaf.
**Action.** Candidate set (A/B/C) + a full state-trace battery protocol handed to
loss-t15, self-serve — the lane unblocks without waiting on t14. widthMinUpto's inclusive
≤ pinned from the def (EngineDefs:154) en route.
**Lesson (provisional until the battery rules).** Two individually-correct rulings (reset
semantics; leaf-discharge shape) can still fail to COMPOSE at a boundary state neither was
examined at — the boundary here being the terminal rollover. Same family as entry 15
(boundary-only verification), dual direction: there the interior was untested; here the
final boundary was.

## Entry 18 (tick 380, 2026-07-20) — the cordon census: what sorries remain after the two owed close?
**Question.** When leafDiagFrob_geoAtlasNorm + geoAtlasNorm_imageCover close, what sorries
remain in DLNFibre/DLN/RLCT/, and is every one accounted for by the cordon plan?
**Expectation (before grep).**
- ENGINE cone (must be fully accounted): ClearableReify:78 (R7 completeness, owed
  post-spine — reifies now, proof later) + CanonicalWitness224:135 (off-cone (2,2,4)
  witness) = 2, both PLANNED. Confidence 0.85.
- SKELETON: 3 fossils (:1094/:1140/:1197) — die at the mint relocation (mint-t19's plan).
  Confidence 0.9.
- VALIDATE: MANY (the L2/RouteM/Deepest scaffolds — exploratory, off the payoff cone) —
  guess ~20-25 files. These do NOT block the λ theorem (not on its cone); the cordon names
  them as pre-existing scaffold, not expedition-introduced. Confidence 0.6 on the count.
- Net after the two close: the payoff cone (aoyagi_learning_coefficient_gen + its deps) is
  sorry-FREE; the remaining sorries are all either owed-post-spine (R7), off-cone (224 +
  Validate scaffolds), or fossils (Skeleton, die at mint). Confidence 0.8.
**Verdict (after grep).** Cleaner than feared — census fully accounted.
- ENGINE: 4 sorries now (CanonicalWitness224, ClearableReify, GeoAlphaGauge =
  leafDiagFrob_geoAtlasNorm [loss-t15 owed], GeoAtlasTransfer = geoAtlasNorm_imageCover
  [t14 owed]). After the two owed close → EXACTLY 2 (ClearableReify + CanonicalWitness224),
  both planned. HIT (0.85). 
- SKELETON: 3 fossils. HIT (0.9).
- VALIDATE: 9 files (not 20-25 — I over-counted; the tick-341 census counted docstring
  "sorry" mentions, not terms). Downward miss, benign — fewer to cordon.
- DECISIVE off-cone proof already in hand: aoyagi_learning_coefficient_gen is gate-verified
  CLEAN-THREE, so NONE of the Validate/Skeleton/224 sorries are on the λ cone (else it would
  carry sorryAx). The payoff cone is provably sorry-free modulo the two owed. HIT (0.8).
**Action.** The cordon census (PR-time) enumerates: 2 Engine owed-post-spine/off-cone + 3
Skeleton fossils (die at mint relocation) + 9 Validate scaffold files (pre-existing,
off-cone). The PR body's "owed" paragraph names R7 (ClearableReify) + the (2,2,4) witness;
the Validate/Skeleton items are pre-existing-scaffold / fossil, not expedition-introduced.
Pre-staged so the census is a checklist, not a discovery, at PR time.

## Entry 19 (tick 385, 2026-07-20) — THE α GAP: ratified-faithful but under-implemented; the biggest endgame miss
**What happened.** alphaGauge was ratified as "Aoyagi's normalized integration chart" at the
atlas-seam ruling (fork 15, tick 340) and re-affirmed through the witness-swap, transfers,
and rev-jac's fidelity PASS on the Jacobian. But the Lean α (residualSchurShear) implements
only the INTERIOR Schur complement — it omits the pivot-column Lg-remainder and the pivot-row
Rg of the paper's full Q,P. So it does NOT reach the exactly-diagonal leaf; residualCore can
hit 0 (the LeafPullback lower bound is false over it). pnp-diag caught it (mechanism ii,
exact witness at (2,2,2)) only when loss-t15's value-walk build forced the concrete question
"does α actually clear the pivot cross?"
**Why it stayed latent through FOUR ratification/review passes.** The two missing factors are
unipotent DET-1. Every consumer built before the value lane is BLIND to them: the Jacobian
(det-based — walk-t20 + rev-jac PASS), the cover (image-based — pnp-cover), the ledger
props/ae-inj (structural). The ONLY consumer that sees the gap is the LeafPullback LOWER
bound — the value lane, built last. So "α = Aoyagi's chart" passed every gate whose
instrument couldn't distinguish the incomplete α from the complete one.
**The miss (mine + the elder's + rev-jac's).** We verified "α is faithful" against the
FIRST/cheapest consumers (det, image), not against the consumer most SENSITIVE to what α
must do (the value lower bound). rev-jac's CHECK-4 "α = Aoyagi's chart" confirmed the NAME
and the interior-Schur, not the full Q,P — it couldn't, from the Jacobian.
**Lesson.** When a construction is ratified "faithful to X," identify the consumer most
sensitive to X and verify the IMPLEMENTATION against THAT, not the first/cheapest one. A
det-1 omission is invisible to every det/measure/image consumer and visible only to a
value/lower-bound consumer — so a gauge's faithfulness must be gated by a value witness,
not a Jacobian one. (Ties to threads 18/19 W1/W3 which SAID the math needs the Q,P — the
gap was Lean-implementation vs stated-math, undetected because the sensitive consumer came
last.) Bounded fix (construction completion, conclusions survive, proofs redo) — but a real
setback, named plainly.

## Entry 20 (tick 392, 2026-07-20) — VINDICATION: the discipline caught a wrong-RLCT before it shipped green
**The event.** Two nested structural findings (α gap → order kill) surfaced from the VALUE
lane's concrete build, both invisible to the det/cover/image consumers. The order kill is the
sharpest: the Lean tree (leaf-first) with even a completed α computes a genuinely WRONG RLCT
(different b-chain — the Schur complements depend on Aoyagi's coupled root-first order,
worked.tex:375-390). The DET lane is order-blind — geoAtlas_fold_det would have shipped GREEN,
clean-three, over a wrong-RLCT spine. AxCheck would have passed. rev-jac's Jacobian fidelity
PASS was real but det-scoped.
**Why it was caught.** The value lane (loss-t15) reads the OBJECT (the RLCT via the loss
lower bound), not a green light; and the decorrelated pnp seats (pnp-diag α gap, pnp-rg order
kill) adjudicated the truth-values the det/image instruments were structurally blind to.
**The lesson, now demonstrated not just asserted.** "A green build is necessary, never
sufficient" (bedrock.md) and "coverage's cover is a universal claim requiring a decorrelated
hunt, never an in-house witness" (compass) — these are not process ceremony; they are the
ONLY instruments that could catch an order-dependent fidelity error under an order-blind
headline. The controller's earlier calibration misses (15/16/19 — all "verified against the
first/cheapest consumer, not the value-sensitive one") were the SAME class; entry 20 is the
payoff of finally routing every fidelity claim through the value-sensitive consumer + the
decorrelated hunt. A PROCESS SUCCESS: the fidelity error was caught before it shipped, at the
cost of a bounded rework, not after a false "done."
**Forward.** The fix is faithful-mandatory + bounded (re-thread root-first, elder-ruled);
whether it lands this expedition is navigator-7's cost call (gated on t14's cocycle-flip
mirror-vs-rebuild probe). Either way the corrected fold + value lane are the real deliverable.

## Entry 21 (tick 404, 2026-07-20) — ISSUE #3: the chart-diagonalization CATEGORY ERROR (the deepest fidelity lesson)
**The finding (pnp-full, exact, both orders, 4 M's).** Completing α to Aoyagi's full Q,P AS
A CHART is a CATEGORY ERROR: to diagonalize the loss you must zero the pivot cross, but that
cell IS the shear coefficient, and clearing it needs a COORDINATE-DEPENDENT (ratio)
coefficient — so the CHART map's Jacobian degenerates (|det D chartMap| = 0, a
dimension-reducing projection). Diagonalization ⊥ chart-validity (det-1 + a.e.-inj) for this
α-family. Aoyagi's Q,P are unimodular as IDEAL-level operations (SL over the function field),
NOT as diffeomorphisms of parameter space. So the RLCT LOWER bound (residualCore ≥ 1) is NOT
obtainable by any det-1 chart-gauge diagonalization — it needs the ideal structure or extra
blow-ups.
**Why it matters / what it retired.** The entire α-completion + root-first re-thread arc
(ticks 385-401) was chasing a chart-fix for something that is not a chart operation. #3b
confirmed the corollary: leaf-first was CORRECT for the det (root-first breaks it) — so the
root-first re-thread was a symptom-chase. The banked leaf-first engine/Jacobian/cover STAY
correct; the REBUILD-L cocycle cost EVAPORATES. The value lane's design (four-case
maintenance) is sound AS A REDUCTION (Q1, all 4 M's) — the target structure is known; only the
chart-free realization is open.
**The lesson (deepest of the run, generalizes the 15/16/19/20 family).** The prior misses were
"verified against the cheapest consumer." This is one level deeper: the whole APPROACH
(diagonalize-the-loss-via-a-chart-gauge) was CATEGORY-wrong, and no consumer-level check would
have caught it — only asking "is this object even a chart?" (the det-0 probe) does. When a
construction imports an operation from the source mathematics (Aoyagi's Q,P), verify it lives
in the SAME CATEGORY as the target slot (chart / diffeomorphism), not just that it "does the
right thing" algebraically. Ideal-unimodular ≠ chart-unimodular. The decorrelated exact-algebra
hunt (does the Jacobian vanish?) is the instrument that exposes a category error; no green build
or consumer-fidelity pass can.
**Forward.** Conditional spine (banked, verified) is the honest deliverable, untouched. The
follow-up narrows to the RLCT lower-bound MECHANISM (ideal / blow-ups) — elder ruling in flight
= its central question. Cleaner in structure (no re-thread, no cone re-open) but deeper in
content (a real new mechanism). Re-scope is now not just right but the ONLY correct path.

## Entry 22 (tick 406, 2026-07-20) — the VACUITY catch + the ideal-level resolution + the runway reframe
**The vacuity catch (navigator-8, time-sensitive).** The conditional spine mint-t19 banked
(tick 402) conditioned on hCBF = chartBridgeFaithful_buildTree — the SPECIFIC α-atlas
satisfies ChartBridgeFaithful, incl. LeafPullback over it. #3a proves LeafPullback-over-α is
category-FALSE. So hCBF is a REFUTED hypothesis; `hCBF → aoyagi` is vacuously true (ex-falso),
and the "one exact away" seam is DEAD (chartBridgeFaithful_buildTree is unprovable-as-stated).
I had represented it to the operator as "the durable deliverable, one exact from
unconditional" — WRONG; corrected. The honest bank conditions on the ABSTRACT Prop
(hbox / generic ChartBridge — satisfiable by a FUTURE atlas), which is aoyagi_gen essentially.
Re-base in flight (mint-t19).
**Why it matters (the meta-lesson, deeper than "cheapest consumer").** A conditional whose
hypothesis is known-false is not progress — it's the visible-progress trap wearing a
clean-three badge. Banking `refuted → goal` LOOKS like "the engine minus one lemma" but the
lemma is category-impossible for the named object. RULE: before banking a conditional as
"near-complete," check the hypothesis is SATISFIABLE (by the named object, or honestly by a
future one) — a clean-three conditional on an unsatisfiable hypothesis is vacuous.
**The ideal-level resolution (elder, page-grounded).** The RLCT lower bound is Lemma 1
(worked.tex:153-158) — ideal-RLCT-invariance; the Q,P are ideal-preserving unimodular
reductions, NOT charts. Chart-diagonalization is category-wrong (pnp-full). The lower bound is
IDEAL-level (⟨∏C⟩=⟨b_i⟩ → rlct⟨b_i⟩ → ½·min M_{s,k}), not chart-coverage.
**RUNWAY REFRAME (overturns the runway memory).** rlct-runway-target.md said "coverage / the
singular-locus lower bound IS the runway's hard part." OVERTURNED: the lower bound is
IDEAL-LEVEL (Lemma 1 + monomial ideal), NOT chart-coverage — a det-1 chart is a smooth reparam
and structurally CANNOT manufacture a lower bound on the singularity (Watanabe's chart route
gives only the UPPER bound). The runway's true hard part = the ideal-RLCT machinery (Lemma 1,
Mathlib-absent, + ⟨∏C⟩=⟨b_i⟩ + monomial RLCT). Recorded in-repo (authoritative); the global
memory is superseded (not edited, per policy). The runway-target kill-condition PREDICTED this
("lower bound needs singular structure; smooth/chart gives only upper") — confirmed, then the
LOCATION corrected from chart-coverage to ideal.

**CORRECTION (same tick, elder self-corrected).** "Runway OVERTURNED / lower bound is ideal
NOT coverage" is TOO STRONG — the elder over-corrected in its #3 message and retracted. The
accurate reframe: the cover/resolution is KEPT (the structural half — the current leaf-first
tree IS the resolution, monomializing to the b_i); Lemma 1 (ideal domination) is the NEW half
that the chart-diagonalization was a category-wrong stand-in for. So the runway is EXTENDED,
not overturned: cover-kept + Lemma-1-added + divisibility-chain-toric-trivial (no extra
blow-ups). And the honest bank conditions on the ABSTRACT hbox (satisfiable via Lemma 1), NOT
a chart-CoV ChartBridge — pnp-full's no-go is GOAL-level, so chart-CoV LeafPullback is refuted
for ALL charts, making any chart-CoV-conditioned bank vacuous (the vacuity sits one level above
where navigator first placed it). Meta-note: I propagated the elder's over-correction into this
entry before it retracted — a reminder to mark office rulings provisional until the office
confirms, especially mid-reckoning.

## Entry 23 (2026-07-20, tick 416) — the depth-3 ideal-reduction probe: TELESCOPE-vs-WALL + the verification meta
**The load-bearing question** (the make-or-break gate): does the per-chart IDEAL reduction
`⟨∏C∘chart⟩=⟨b_i⟩` telescope through the layers at depth 3 (M=(2,2,2,2)), or WALL at the
SchurCore depth-≥3 boundary the navigator flagged?
**Expectation written BEFORE reading the verdict** (my prior, honestly): ~60% telescopes /
~40% walls. Lean-to-telescope because the LOSS-level depth recursion (verify-r1-shortcut,
Codex-corroborated) already worked and unimodular ideal ops are "easier" than loss
diagonalization; but the navigator's flagged SchurCore wall was real evidence toward a wall,
and I'd been burned by found-late faults twice this run (α under-implementation, leaf-first
order), so I held genuine uncertainty and refused to pre-commit the follow-up.
Second expectation: the cert would be internally clean (trusted seat, batteries committed
exit-0) — I'd relay the headline after a light read (~85% confidence it was clean).
**Actual**: TELESCOPES, cleanly, depth-blind. The wall was a ONE-SHOT artifact (naive
iterated-block-elim + one blow-up, already refuted L≥3); the depth recursion sidesteps it —
each peel is an EXACT single-layer symbolic matrix identity, corner a fresh unit at every
depth. AND: the cert was NOT internally clean — `ideal_equality_rigorous.py` (exit-0) prints
the OPPOSITE of the headline (a superseded free-δ intermediate the seat fixed 3 min later but
left in the dir + folded into "5 batteries all exit-0").
**HIT / MISS**:
- HIT (telescope prior, ~60%): leaned the right way; the mechanism is CLEANER than I expected
  (an exact depth-blind identity, not a case-by-case grind). The SchurCore-wall fear was
  miscalibrated — it was never a wall for the recursion, only for the one-shot.
- MISS (cert-internally-clean prior, ~85%): the cert had an unreconciled internal
  contradiction. Caught ONLY because I read the battery CONTENT, not the exit codes — the
  make-or-break stakes + the operator's found-late concern forced observe-before-theorise.
**What it changes**:
1. The follow-up is TRACTABLE (route i telescopes), not a slog. The concrete cul-de-sac
   evidence: NOT avoiding the hard part — the ideal reframe was the CORRECT response to the
   α-chart category no-go, and the depth-≥3 hard part is now MAPPED (all-widths-≤2 clean;
   width≥3 = Aoyagi coupled diag(b), monomializes, heavier, does NOT wall). Boundary located,
   not dodged.
2. Verification discipline REINFORCED (this is altitude-07-20's meta-lesson recurring):
   green-build ≠ correct becomes EXIT-0 ≠ battery-content-TRUE. Even a trusted decorrelated
   seat's cert needs a battery-CONTENT read on a make-or-break verdict — the exit code is the
   floor, the printed True/False is the claim, and the two diverged here. The decisive check
   was the EXACT symbolic peel identity (not the composed numeric checks), because it proved
   the δ=ρ tie is DERIVED from the blow-up (not reverse-engineered to force divisibility — the
   confound I was hunting). Prefer the most-adversarial exact check (the mechanism identity)
   over the aggregate pass-count.

## Entry 24 (2026-07-20, tick 419) — the deliverable/follow-up MIS-FRAMING (operator-caught): re-derived work sold as new, follow-up over-scoped
**The question I should have asked (but didn't) before framing the deliverable + follow-up**:
what is the axiom footprint of the TOP headline `aoyagi_learning_coefficient`, and what is its
SOLE open rung? I never wrote this expectation down — I reasoned from the recent expedition's
local frame instead. That omission IS the miss.
**Implicit belief I was carrying** (~high confidence, unexamined): the L2-unconditional corollary
I banked was a real deliverable ("the floor / teeth"), and the follow-up was "build the general
RLCT-ideal library" (a large new build).
**Actual** (operator-flagged, confirmed against the territory): (a) the FULL L=2 headline was
already clean-three weeks ago (HeadlineL2Assembly.lean:88, 2026-06-30/07-06) — my
`_L2_unconditional` (HeadlineConditionalSpine.lean:93) proves the IDENTICAL statement, a
re-derivation; (b) the general-L UPPER bound was already unconditional weeks ago
(HeadlineGenBounds.lean:143, 2026-07-09); (c) the full headline is assembled and reduces to ONE
open rung — the general-L LOWER bound = `RouteMBoxThresholdFinite` at L≥3 (proven at L=2). The
"library" is ~built; the gap is one rung.
**MISS (large, and the operator caught it, not me or an office)**: I sold re-derived / already-
built content as the achievement and over-scoped the remainder. This is the visible-progress /
name-results-for-what-they-are trap in its purest form — the exact disposition failure CLAUDE.md
foregrounds, and the exact shape of the operator's repeated cul-de-sac question (which I kept
answering at the strategy level while committing the error at the object level).
**Root cause**: no re-grounding in the FULL banked state before framing. The comprehension
cadence's own instrument (read the actual Lean, write the expectation first) would have caught it
— I ran calibration entries on the ideal-probe territory but never on "what does the top headline
actually still owe." Local-frame reasoning under a long expedition drifts from the global state.
**What it changes**:
1. Follow-up RE-SCOPED: formalize the ONE open rung (L≥3 box-finiteness via the ideal
   peel-identity telescoping), riding banked infra — NOT a library build. Likely a focused
   formalisation, maybe not even a full new expedition.
2. Deliverable RE-NAMED honestly: this expedition's real output is (a) the chart-route category
   no-go (proven), (b) the ideal reframe + the L=3 telescoping cert (on paper). The L2
   "teeth" is a re-derivation, not the floor. The floor is the weeks-old banked headline.
3. STANDING CHECK added: before framing any "deliverable" or "follow-up scope," run
   `#print axioms <top-headline>` (force-recompiled) + identify its sole open rung(s). Re-ground
   globally, not from the active thread. (Pairs with entry 23's exit-0≠content-true: verify the
   kernel truth of the HEADLINE state, not just the local artifact.)

## 2026-07-21 (controller, autonomous stretch) — lane-4 carrier-bridge calibration
Q (load-bearing for lane 4): does banked GlobalBridge give the carrier bridge coreReduction needs, or is
the ℝ≥0∞ gap real? EXPECTATION (pre-read): global_rlctAt_eq is an ℝ↔ℝ equality under mild hypotheses
(0.75); the ENNReal/rlctAtOn bridge is NOT banked and remains lane-4's new content (0.7).
ACTUAL: HIT + stronger — global_rlctAt_eq is DEFINITIONAL (rfl, no hypotheses; GlobalBridge.lean:41).
HIT — no rlctAtOn↔rlctAt bridge exists anywhere banked; the ℝ≥0∞ hop is confirmed the one genuinely-new
lane-4 piece. BONUS: rlctAtOn_comp_homeomorph is banked (Case222Lemma2) — the flatten transport is
already available once codex-fix (e) packages the flatten as a homeomorphism; lane 4 = ONE carrier hop +
adapters, smaller than budgeted. Strategy delta: lane 4 may be the SHORTEST lane, not a long one —
re-rank at strike opening.

## 2026-07-21 (controller, autonomous stretch) — leaf-1 seam calibration (post-split)
Q (load-bearing for the wave): does the LANDED RegionRepresents match what the ratified
StepInv/terminal_bezout split produces at leaf 1? EXPECTATION (pre-read): one predicate carrying BOTH
directions on nbhd (0.8); ContinuousOn cofactors, vanishing allowed, pointwise-on-V not germ (0.85);
lead = the bexp monomial (0.7).
ACTUAL (IdealInvariance.lean:84 + ProductResolution.lean:112–116): PARTIAL MISS on shape —
RegionRepresents is SINGLE-direction (G repr. by F, coefficient matrix a i j); the record carries TWO
fields (hideal_fwd/hideal_bwd). HIT on the region form (ContinuousOn + ∀ u ∈ V pointwise). NUANCE
CAUGHT (the entry's real yield): the record's identity is against `monomialFam bexp` — the FULL
M-family diag(b), not the single b_{k₀} that StepInv tracks. The bridge: fwd needs only ONE family
member (a i k₀ = q_i, rest 0 — divisibility by b_{k₀} suffices); bwd needs monomial_j = (b_j/b_{k₀})
· (terminal-Bézout combination), where b_j/b_{k₀} is polynomial BY THE CHAIN — so the chain hypothesis
in StepInv is exactly what makes hideal_bwd feed, independently re-deriving the elder's leaf-1-feed
check against the actual Lean. Strategy delta: leaf 1 is honestly TWO lemmas (fwd trivial-embed from
divisibility; bwd = terminal_bezout × chain-division); the b_{k₀}-vs-family seam goes in the L1 seat
brief so a wave seat doesn't trip on it.

## Entry 25 (2026-07-21, navigator #12 — controller-filed) — rung (C) reification: one tide that absorbed two pnp verdicts + D1–D4 mid-tide [event-driven]
FORECAST (pre-tide): rung C = one arch-C reification tide (type + wire the 8-leaf skeleton toward the
driver; gate = elaboration + cone + no landed statement changed).
ACTUAL: HIT on the landing (merge clean; driver cone = exactly the 8 leaves; batch-341 + cordon green;
gate passed — navigator verified against git), but the tide ABSORBED THREE mid-tide statement reshapes
without a re-spin: the pnp-case1 split (per-step PrincipalInv is FALSE interior → StepInv
divisibility-only + terminal_bezout), the pnp-cover confirm (L7 stronger-inclusion), and the elder
D1–D4 shaping. arch-C stopped-on-suspect at the L3/L4/L5 leaf shapes and reshaped in place.
WHAT IT CHANGES / LESSON: a reification tide's cost is dominated not by the TYPING but by the
statement-CORRECTNESS reshapes it absorbs — and those were cheap HERE only because the pnp
pre-adjudications ran FIRST (the split was known before arch-C reified). The interior-state mandate
(navigator #11 ledger counsel: "boundary-only verification most likely to fire on L3/L4/L5") PAID
EXACTLY — it caught the false per-step PrincipalInv before the skeleton reified it. True cost model
forward: reification tide + N decorrelated pnp pre-adjudications = the reshape-safe reify; price a
reify by how many statement-shapes are still UN-pre-adjudicated, not by binder count. Residual: the
reify banked TWO under-adjudicated statement-shapes that pass #12 caught (terminal_bezout
ContinuousAt-vs-ContinuousOn — controller re-confirmed vs the Lean text, PLUS a controller-found
missing IsOpen V / 0 ∈ V pair in the same statement; the D3-gap driver-hypothesis accounting) — the
reification gate should have included a hypothesis-suffices check per leaf (do each leaf's hypotheses
discharge its conclusion?) and a driver-signature-vs-canonical diff.

## Entry 26 (2026-07-21, controller) — pre-landing check: does the tree expose center/pivot?
Q (load-bearing for the imminent foldState render landing): does the salvaged combinatorial tree
carry the coordinate-level center/pivot data the elder's locked TreeEdge interface declares, or must
the render DERIVE them? EXPECTATION (pre-read): ConState is combinatorial-only (widths/layer/cleared/
ledgers), no center/pivot Finset — derivation required, via the flatten indexing (0.75).
ACTUAL: HIT — ConState = {layer S, cleared J, numDiv, divExp, divProfile, numGen, genDivExp}
(EngineConstruction.lean:43). No coordinate data. So ed.center : Finset (Fin (flatDim d)) and
ed.pivot are RENDER-DEFINED from (S, J, d) — the ONE implementation-owned piece the locked text does
not pin, hence the one drift-capable spot in an otherwise verbatim landing.
STRATEGY DELTA: the integration gate gains an explicit check — the rendered ed.center.card/pivot
along the (3,3,4) traversal must reproduce the traversal battery's center-codim table (codims
9/4/1 at S=1; the 1×2 codim-2 at S=2; pivot kinds per case). Sharpener sent to arch-C mid-gate.
The general lesson repeats entry-25's: locked TEXT pins statements; DERIVED DATA in the
implementation still needs its own regression witness.

## Entry 27 (2026-07-21, navigator #13 — controller-filed) — statement-risk dominates proof-risk in a foldState monument
FORECAST (Entry 25, rung C): a reification tide + N pnp pre-adjudications, then the leaf-proving
WAVE. ACTUAL: the wave never launched as planned — the statement-hardening arc ran a full day
(round-5 → seven severance classes → the (A′) reversal, FALSIFIED after a "final" ruling → repair
bake → FIX-1/FIX-2 → the L7 bridge-dependence scare → the canonCenter checkpoint). The wall's PROOF,
once its statement was locked, landed in ONE seat (StepInvShearChild, sorry-free). WHAT IT TEACHES:
for a quantified-skeleton monument the cost meter is the count of UN-AUDITED FREE FIELDS on
quantified structures (the per-field severance axis), not sorry-count or binder-count. Each
severance axis cost ≈ one render+gate cycle; the proving was the cheap tail. Extends Entry 25 one
level: price by un-audited free fields; the (A′) reversal proves even a post-"final-ruling"
statement can hide an un-audited axis (CENTER-SIZE, after CONTENT was closed). FORWARD PRICING
RULE: budget the decorrelated per-field audit as the DOMINANT line item of any foldState/skeleton
leaf; treat "minutes to wire" as the honest cost of the PROOF only, never of the leaf, until every
free field has a regression witness.

## Entry 28 (2026-07-21, heartbeat tick) — guard dischargeability at the oracle

**Question (load-bearing):** is fix (a)'s guard `ed.nextState.layer < N` dischargeable at L5's
fold — i.e. does the engine's oracle keep case-1/case-2 children at the parent's layer, with only
rollover advancing it?

**Expectation (written before reading):** case children keep `layer` unchanged (cleared+1);
`layer + 1` happens only in the rollover branch. Confidence 85% (elder "by construction" + nav
"only rollover advances" — neither personally verified until now).

**Territory:** EngineConstruction.lean — the case-step constructor (≈:190) is
`⟨s.layer, s.cleared + 1, …⟩` (layer LITERALLY unchanged); `ConState.stepRollover` (:198) is the
sole `s.layer + 1` site (cleared reset to 0). **HIT.**

**What it changes:** the guard's discharge at L5 is `rfl`-adjacent (case child's layer = parent's;
parent liveness by fold induction) — fix (a) costs the consumer essentially nothing, confirming
the elder's "dischargeable by construction" and removing the last pricing uncertainty on the
guards half of the locked round. The guard remains genuinely load-bearing on the FREE TreeEdge
(the defect was real); it is only its supply that is cheap.

## 2026-07-22 tick — Q: exact live sorry census on the value path?

**Expectation (written first, conf ~70%):** exactly 9 — 8 leaves all inside MonumentAtlas.lean +
the 1 summit sorry (LearningCoefficient.lean:287); no strays in merged modules; raw census ≈ live
census.

**Actual (scripts/sorries):** raw census = 34 sorries across 19 files. LIVE cone = 9 ✓ — but
distributed 7 in MonumentAtlas + 1 in Case2Delta0.lean (the δ=0 leaf lives in its OWN module, task
#19) + 1 summit. And ~25 FOSSIL tokens I failed to recall: Validate/* 17 (RouteMInteriorLDUContract
alone 9), Skeleton.lean 3, Engine/{GeoAlphaGauge,ClearableReify} ~2 (+2 comment-only mentions).

**Verdict: HIT on the live total (9), MISS on distribution (Case2Delta0 is a separate cone module,
not an atlas leaf) and MISS on the fossil load (I conflated "value path" with "the census" — the
raw number is 3.8× the live number).**

**What it changes:** (1) the close-phase fossil prune is a REAL work item — ~25 tokens / 12 files
(Validate 17, Skeleton 3, Engine 2+), not "a few stragglers"; queue it explicitly in the close
checklist. (2) Any "sorry-free" close claim must be cone-aware AND then census-clean after the
prune — the two numbers converge only at the very end. (3) Post-bake the cone goes 8→10 named;
the census should read 10+1 live + fossils until the prune.

## Entry 29 (2026-07-22, navigator — endgame first full pass) — the redirect round: free-field skeletons price at their statement-collapse, and elaborate-then-render is the fix

**The question (position at the phase juncture):** with the monument's statement architecture
redirecting from 7 per-field hypotheses to 1 IsRealBranch construction-conditioning, what did the
free-edge leaf design actually cost, and what is the correct pricing meter forward?

**Actual (journal 2026-07-22, ground-truthed):** the monument spent ~10 statement rounds this run,
each the SAME event — a free TreeEdge field admits a non-construction instance; a constraint of
Aoyagi's recursion is re-derived as a bolted-on hypothesis. The wall's MATH (StepInvShearChild,
exists_graded_decomp, BlockDivision) landed in one seat each; the STATEMENTS took the ten rounds.
Four of the defects were authored-form (∀ℓ over-reach, parent-supportAt direction, region token,
ShearWithinCarve (II) scope); two were in the elder's own rendered sentences; one was a silent
catch-all (canonCenterOf `| _ =>` mis-firing case-11 — a NEW defect class). The discriminator that
ended the descent dispute was a kernel-checked invariant (DivBirthInv), not a battery — a proof beat
an empirical sweep.

**The controlled comparison (the decisive datum):** the E-lane carried the #42 ELABORATED cert up
front → three tracks, zero rework, closed clean. The monument had no template → ten reactive rounds.
pnp-elab retrofitted the template mid-endgame and its mechanical diff found ZERO mismatches — the
first POSITIVE statement-fidelity evidence of the expedition (vs. absence-of-caught-defects).

**Pricing lesson (extends Entries 25/27):** a free-field skeleton's cost is dominated by its
statement-collapse rounds, and the correct meter is whether an EXACT-ALGEBRA-CERTIFIED CONSTRUCTION
TEMPLATE exists before the leaves are typed. Price a leaf-set by that; if the template is absent,
BUILD IT FIRST (the elaborate-then-render discipline, now operator-standing). The construction-
conditioning collapse (per-field → derived-lemmas off one IsRealBranch hypothesis) is the structural
end-state a free-field skeleton converges to — reaching it via ten reactive rounds vs one template
is the whole delta. Corollary for the gate: a def with a catch-all branch needs a def-level
EXHAUSTIVENESS check; the sim validates reached cases, never def completeness (canonCenterOf's
class).

## Entry 30 (2026-07-22 ~18:40, controller tick) — live-cone calibration at the cascade's peak

**Question:** after 4 bakes + 5 stub closures + 3 leaf closures in one day, does my carried
picture of the live cone match the tool? **Expectation (written first):** census 36 = 11 live
(MonumentAtlas 8 + LearningCoefficient 1 + Case2Delta0 1 + Case2Wire 1) + 25 fossil.
**Actual:** LIVE 11 — HIT, exactly, file-by-file. Census tool 36 ✓. (My quick python parser
reads 37 — its known +1 comment-line bias vs scripts/sorries; the tool stays canonical, the
parser is for file attribution only.) **What it changes:** nothing — the picture is current.
The miss-risk zone was Case2Wire's tracked conjB (new today) and the stub closures landing
faster than the memo updates; both were carried correctly. Confidence in the memo's census
line: high. Next calibration due after the node-form + Assembly land (the cone shape changes:
MonumentAtlas 8 → 7 + Assembly primed-driver sources appear).

## Entry 31 (2026-07-22 ~15:55 UTC, phase transition: statement layer → proof cascade)

**Question:** enumerate the 10 live sorries BY DECLARATION from carried state, before looking.
**Expectation (written first):** MonumentAtlas 8 = multiAffine_step, lastLayer_clear_preserves,
case1/case2_preserves_stepInv stubs, leafPath_chartGeometry, leafPath_realizesExponents, "an L5
fold anchor" (~70%), "the monument driver" (~60%); Case1Wire 1 = boostReady; LearningCoefficient
1 = :287. **Actual:** 8/10 exact HITS + the L5 anchor is `leaf_stepInv_of_path` (half-credit —
right role, name not carried) + ONE MISS: the 8th atlas sorry is `leafPath_compactCover` (the L7
anchor), NOT the driver — the salvage adapter carries NO sorry of its own (its header says so;
the sorryAx cone is exactly the leaf set). **What it changes:** (i) the summit swap is PURE
leaf-closure — no driver work exists, which shortens the endgame model; (ii) L7 is a first-class
on-cone anchor, corroborating nav-13's "L7 commissioning startable" — it should not wait for L5;
(iii) the carried live-set is otherwise current. Census 35 ✓, live 10 = 8+1+1 ✓.

## Entry 32 (2026-07-22 ~23:30, controller — a MISS, recorded plainly)

**Prediction:** boostReady's assembly = "execute a banked inductive design" (I cited seat-L4B's Codex
answer §1-2 as the banked P(p) invariant + step discharge, and briefed seat-L4C to read it).
**Actual (seat-L4C ground-truth, controller-verified):** the cited file does not exist; NO invariant
def is banked (only the ingredients). boostReady is a genuine CONSTRUCTION seat-L4C must design.
**Miss type:** un-verified pass-through of a teammate's artifact-CONTENT reading + a false-positive
shell existence-check (`git show|head && echo FOUND` keyed off head, not git show).
**What it changes:** (i) boostReady scale ↑ (invariant design + induction, the wall's heart — not
assembly); route unchanged (3 Codex converge, within-leaf-scope). (ii) Discipline: verify artifact
CONTENT before citing it in a brief; never gate existence on a piped `head`/`tail`. (iii) Added a
SPECIFY-checkpoint gate before seat-L4C's heavy build. Confidence in "banked ingredient" claims: recalibrate
— check the DEF exists, not just a referenced filename.
