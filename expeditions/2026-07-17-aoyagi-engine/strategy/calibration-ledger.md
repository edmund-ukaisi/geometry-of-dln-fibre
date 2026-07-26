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

## 2026-07-23 (~06:25, phase transition: diagnostic arc → render/merge) — the render-target def
Q: Does canonical MonumentAtlas branch-(ii) carry the UNSCOPED all-i≠col sum in the Q₁⁻¹ (+γ)
direction — the exact pre-fix form every instrument modeled (and REBAKE inherited at :940-942)?
EXPECTATION (written first, confidence 0.95): YES — `∑ i ∈ range (d castSucc), if i = q.2 then 0
else readEntry(S,i,b)·readEntry(S+1,row,i)`, no cleared-bound, comment naming A_{S+1}·Q₁⁻¹.
ACTUAL (read :875-885): exact match, including the docstring's "(ii) layer-(S+1) recoord:
`(A_{S+1}·Q₁⁻¹ − A_{S+1})`" — the def names the very direction the arc diagnosed as the
conversion error. VERDICT: HIT. WHAT IT CHANGES: nothing — and that is the point at a phase
transition: the instruments' shared model of the render-target site is faithful to the
territory; the render's two changes (direction + scope) land on exactly the modeled lines.

## 2026-07-23 ~14:30 — Q: is the summit re-point (#74/GM's Q2 surface) mechanical?

**EXPECTATION (written before the read):** the summit `leaf_stepInv_of_path'` does a path
induction OVER FoldStepInvAt (base = root invariant, step = case1''/case2''), so the re-point =
swap the invariant + the two case-lemma names; risk sites = the root base case (dissolves — the
cleared root = raw root by sourceClearedResid_root rfl), the payoff read-off (one (iv)-bridge
rewrite), hidden he-pins. Confidence: 65% mechanical-with-known-risks / 25% one statement-level
surprise (most likely where the payoff consumes the summit) / 10% worse.

**READ (MonumentAssembly.lean:27-80, MonumentAtlas.lean:1753+):** PARTIAL MISS, informative.
(1) The summit STATEMENT is INVARIANT-FREE — FoldStepInvAt appears nowhere in
`leaf_stepInv_of_path'`'s type; its conclusion is `∃ atlas : GeoAtlasData, FoldProduced ∧
FoldRealizes ∧ ∀ c, PrincipalInv (coreGen d e) (atlas.gmap c) …`. The invariant chain is the
PROOF SCAFFOLD of the still-sorried L5 fold body; the case-lemma `have _hc1/_hc2` lines are
cone-registration devices, not consumption. So "swap the invariant in the summit" was the wrong
mental model — the summit re-point is (a) trivial cone-reference swaps + (b) the REAL question:
does the ATLAS-PROVENANCE layer (GeoAtlasData / FoldProduced / FoldRealizes / the leaf
PrincipalInv shape) survive raw or re-state on C? That layer is in NEITHER of §8's lists — an
unclaimed zone between the survive-set and the re-state-set. (2) REASSURING:
sourceClearedResid_root = coreGen (rfl, CAPR's file) ⟹ the resolved function is unchanged —
`Resolution (coreGen d e)` stays type-stable under any answer; the divergence is confined to
chart-map provenance, not the resolution target. (3) The full-build cascade GM gates on is
CHEAPER than feared: the summit type doesn't change, the known red is the wall type-error alone.

**WHAT IT CHANGES:** pre-flagged to seat-GM as a mandatory SPECIFY position (survive-vs-restate
on the provenance layer, elder delta rules it) — converts a likely mid-grind stop-and-surface
into a SPECIFY-time decision. The 25%-surprise branch fired, but at the layer BELOW where I
placed it (provenance predicates, not the payoff consumption). Miss recorded plainly: I modeled
the summit as invariant-parametric; it is invariant-silent.

## 2026-07-23 ~17:26 — Q: will the four render lanes COMPOSE at the #73 integration merge?

EXPECTATION (written before the git read): four lanes touch overlapping capstone files, and
#73 must merge them build-green. My model of the per-file ownership + conflict surface:
- INV lane (-INV): SourceClearedResid.lean + MergeBoostSplit.lean (12 commits). Owns the INV
  spine + the read-off + CanonicalPivots.
- GM/CFF lane (-CFF off -GM): ClearedFold.lean (new) + Case1Wire deletion + CaseStepAssembly/
  LastLayerWire/MonumentAssembly re-points.
- CAPF/CX lane (-CX off -CAPF): CapDescent.lean (new) + the shared continuous_canonNormalizationOf.
- BAKE lane (-BAKE off canonical): MonumentAtlas.lean IsRealBranch one-clause pin.
EXPECTED CONFLICT SURFACE, ranked: (1) BAKE's IsRealBranch pin is the RISKIEST — it strengthens
a def that INV's proofs destructure AND CFF's fix-lemma destructures AND CAPF's #4/#3 consume;
every lane needs a rebase-onto-BAKE + re-verify (INV flagged this; CFF cherry-picks it; CAPF's
#4 built pre-pin). (2) the shared continuous_canonNormalizationOf will exist in BOTH CAPF's
CapDescent and (if CFF needed it) CFF's module — a dedup at merge. (3) ClearedFold consumes
INV's sourceClearedResid_stepMap_eq_pivot_mul + CanonicalPivots BY NAME — a cross-lane
name-resolution that only works once both are on canonical. (4) SourceClearedResid.lean:242's
sorry gets swapped to CX's #6-twin := — a controller edit at merge. Confidence: 60% the merge
is "rebase-all-onto-BAKE-first, then topological-order the lane merges (BAKE → INV → CAPF/CX →
CFF), then the 2 sorry-swaps + the aggregator wire, all build-green in one pass"; 30% one lane
needs a non-trivial re-verify after the BAKE rebase (a destructure pattern or an import cycle);
10% a genuine statement-level surprise (some consumed name's signature moved under a lane).

READ (git topology): merge-bases — INV∩GM = 1388f6192, INV∩CAPF = bbb3f924d, GM∩CAPF = 1388f6192
(all a common CAPR prefix). DECISIVE FACT: GM's commits past the base touching
SourceClearedResid/MergeBoostSplit = ZERO; CAPF's = only CAPR's OWN inherited commits (585f75fb9
ROOT(a), 1ebce70ce skeleton, the 2 docstring fixes) — NOT independent edits; INV's = 16 (the full
spine + read-off + CanonicalPivots). So the "+202 / +270" diffs in GM's/CAPF's shared files are
INHERITED CAPR-prefix, not divergence.

HIT / MISS: HIT — BAKE's IsRealBranch pin IS the real #1 (the only genuinely cross-cutting edit;
every lane rebases onto it). MISS-THAT-RESOLVED-FAVORABLY — I feared a three-way reconciliation
of the shared substrate files; it DISSOLVES because the single-writer discipline HELD: GM and
CAPF consumed sourceClearedResid_*/CanonicalPivots BY NAME and never edited INV's two files. The
discipline I enforced all window is exactly what makes #73 tractable — the integration topology
is the dividend of the ownership rule.

WHAT IT CHANGES: the #73 merge plan is now DERIVED (baked into the task), not to be re-discovered
at merge time. TOPOLOGY: (0) BAKE lands first (MonumentAtlas pin) → becomes the rebase base for
all; (1) INV's lane defines SourceClearedResid.lean + MergeBoostSplit.lean (single lineage, NO
reconciliation) — merge it onto BAKE, re-verify INV's destructures against the strengthened
IsRealBranch; (2) CAPF/CX's CapDescent.lean = additive new file (+ the shared
continuous_canonNormalizationOf: dedup vs any other copy) — merge, rebase-verify; (3) GM/CFF's
ClearedFold.lean (additive new) + the Case1Wire DELETION (CAPF cherry-picked the SAME commit
104d701d1 → patch-id-equal, trivial dedup) + the CaseStepAssembly/LastLayerWire/MonumentAssembly
re-points — merge last (it consumes INV's names, which must be on canonical first); (4) the 2
sorry-swaps (SourceClearedResid:242 ← CX's #6-twin; the wall ← the content lemma) + the aggregator
wire + the (b)/δ=1 named-frontier closes that CFF held. Residual risk lives ONLY at (1)/(3)'s
rebase-onto-BAKE re-verify (destructure patterns), which BAKE's consumer sweep already enumerated.

## 2026-07-23 ~18:26 (phase transition: global-move-render → cap+integration endgame) —
Q: what does L1-clean-three MEAN for the destination? (don't steer by an unverified headline)

EXPECTATION (before the read): aoyagi_learning_coefficient_L1 is a NAMED INTERMEDIATE, not the
full charter endpoint. My model: (1) L1's statement is the learning-coefficient value along the
"L1" route (likely the codim-side or a chart-level piece), NOT the full λ=C/2 headline. (2) L1
clean-three [propext, Classical.choice, Quot.sound] means L1 does NOT route through
cited_aoyagi_lower_ax — but I EXPECT the FULL payoff (the charter's "aoyagi_learning_coefficient
with NO Aoyagi axiom") is a DIFFERENT root that still cites, OR L1 IS cite-free by avoiding the
lower-bound (only the upper/smooth-locus half, per the RLCT-runway memory: "smooth locus only
gives an upper bound; the kill-condition = a singular-locus LOWER bound"). (3) The named
frontiers (the KILL, the δ-transport arm, the wall content lemma) gate FULL-DLNFibre-green +ONE
of the cited-axiom's deletion, NOT L1's current clean-three (which is already off their cone —
CFF verified). Confidence: 55% L1 is a cite-free intermediate that does NOT by itself discharge
the charter's DELETE-the-cite endpoint / 30% L1 IS closer to the endpoint than I think / 15% I've
mis-mapped which root is the payoff. THE RISK I'm probing: treating "L1 clean-three" as "the
payoff is axiom-clean" when L1 might be a scaffold that's clean precisely because it doesn't yet
carry the lower-bound content the cite supplies.

READ (AxCheck:191 + the kill-path comment:1391 + Skeleton:1680/1105): the destination model,
corrected. (1) L1 = the genuine L=1 SINGLE-LAYER endpoint (unconditional, clean-three, off the
frontier cone) — NOT a codim scaffold. My "codim-piece" guess = MISS (it's the honest depth-1
theorem). (2) THE CITE IS DODGED — cited_aoyagi_lower_ax is EXPLICITLY "NOT invoked (the
kill-path)"; the engine summit (aoyagi_learning_coefficient_via_engine) carries sorryAx from
EXACTLY ONE monument (exists_coreResolution), never the cite. My expectation #2 ("full payoff
still cites") = MISS, FAVORABLY: the charter's hard half of "delete the cite" (payoff not
depending on it) is ACHIEVED structurally; only the physical axiom-decl deletion remains
(close-phase operator ceremony). (3) HIT: the frontiers I track (KILL/wall/transport/cap) are
the leaves of exists_coreResolution = R1 resolution_charts.

THE GAP THE CALIBRATION SURFACED (the real product): AxCheck:191 says the GENERAL
aoyagi_learning_coefficient carries sorryAx "until the 5 Skeleton rungs (L2 product_reduction,
D1 deepest_point_reduction-≥, R1 resolution_charts, A1 ×2) are proven." I have been tracking
ONLY R1 (the engine/frontier leaves). The status of L2 / D1 / A1×2 (the Karamata closed-form +
the two reduction-bookkeeping rungs) I have NOT been tracking — if any is OPEN, there is
remaining headline-gating work OUTSIDE the cleared-chain/cap frontiers, an ETA/scope MISS. The
charter §1 says "R0/R1 reductions BUILT (bookkeeping)" + Objects A/C LANDED, which SUGGESTS
L2/D1 are proven and A1 (lambdaCore_eq_clean Karamata) may be the one to check — but SUGGESTS is
not VERIFIED. WHAT IT CHANGES: convene the navigator (phase-transition-mandatory) to verify the
COMPLETE open-dependency set of the general theorem — is {the frontiers via R1} the WHOLE
remaining open set, or are L2/D1/A1 also open? Steering the endgame as "just close the frontiers"
is only right if L2/D1/A1 are proven; the navigator confirms or finds the untracked rung.

NAVIGATOR VERDICT (the gap CONFIRMED — a two-theorem conflation, not untracked math on MY headline):
- CITE-DODGE: YES, genuinely — cited_aoyagi_lower_ax invoked ONLY in the RlctInterface struct
  (AoyagiCited:80), absent from BOTH via_engine's cone AND the Skeleton route; cordon = CITED. The
  charter's "delete the cite" hard half is achieved on both routes.
- TWO DISTINCT LEAN THEOREMS: (B) aoyagi_learning_coefficient_via_engine (LearningCoefficient:323,
  THIS expedition's Objects-A/B/C/D route) — ONLY sorry = exists_coreResolution = my cap/KILL/
  transport/wall frontiers; "close frontiers → theorem" EXACTLY complete for it. (A) the LITERALLY-
  named aoyagi_learning_coefficient (Skeleton:1680) — a DIFFERENT object, cone = 2 legacy bare
  sorries (L2 product_reduction's normal-form 1094 + D1≥ 1140), NEVER references
  exists_coreResolution; its close = the pre-staged #108 re-point (RouteMSJMint) + hbox
  (=DecoratedDescent, the aoyagi-full (□) box-finiteness mountain) + L=1 fold-in — a SEPARATE
  programme, NOT closable by my frontiers. A1 (lambdaCore_eq_clean) PROVEN.
- HIT/MISS: the calibration's gap-hypothesis (untracked Skeleton rungs) CONFIRMED REAL — L2/D1≥ are
  open bare sorries, untracked in aoyagi-engine's list — BUT they belong to the OTHER theorem/
  programme, so it's a DESTINATION-IDENTITY question, not missing work on the engine headline.
- WHAT IT CHANGES: the endgame is COMPLETE-as-modeled IFF the destination = via_engine (path B).
  IFF the destination = the literal Skeleton theorem (path A / unconditional _gen), a further
  re-point (#108) + hbox disposition is ALSO owed — surfaced to the operator (definition-of-done,
  wait-for-explicit-go) + the elder (charter/compass reading). The heartbeat frame ("path B
  replaces the cite; hbox=adapter path A default; DITCH the hole if B prices shorter") suggests B
  is the substantive goal + the re-point folds it into the headline — but that's the operator's
  definition-of-done to confirm, not silently assumed.

## 2026-07-23 — diff-read under-observes a live co-author's late append
Committing an elder-authored shared doc (elder writes to the controller's cwd): a `git diff | head -N`
verification read BEFORE `git add` can miss content the co-author appends between the read and the add
(`git add <file>` stages the final file, not the read snapshot). Here f5f840b65 captured §9.11 AND the
§9.11 ADDENDUM though I'd claimed "§9.11 only." No soundness impact (co-author content, correct) — but
the commit provenance was mis-stated. FIX: when committing a doc a live co-author may still be editing,
verify with `git diff --cached` AFTER staging (or full `git diff`, not truncated), and let the commit
message name what's actually staged.

## 2026-07-23 — controller over-optimism on render difficulty ("simp chain"), decorrelated-corrected
I twice under-specified the #92 KILL V3 render: "trivial termwise" then "stays a simp chain, no
difficulty bump." A fresh render seat (seat-KILL) flagged a concrete gap (escaped coeff reads uncleared
cols couplingClear misses); I routed a decorrelated re-derivation rather than collapse to the earlier
answer (correct instinct). pnp-cap confirmed (A)-termwise; pnp-transport's independent re-derivation
(31be65e54, re-ran exit 0) refined it to MULTI-LAYER product-chain descent (single-layer kill FALSE on
wide pairing layers) — back at #92's original ≥foldResid_layerHomogeneous' scale. The math conclusion
never changed (KILL Gröbner-true, full-diagonal load-bearing); only my render-COST framing was wrong.
LESSON: "this render is cheap" is the visible-progress instinct applied to difficulty; a difficulty
downgrade is a claim to verify (render-seat skepticism + decorrelated re-derivation + re-run the
scripts), not a headline to bank. Damp render-optimism the way we damp result-optimism.

## 2026-07-25 — the (3,3,4) flat-fan cover: COVERAGE ≠ RESOLUTION; 5 optimism-corrections, then dead
Phase-transition entry (the flat-fan cover phase ended in a decisive re-scope). EXPECTATION (mine,
across ~8 ticks): the flat (3,3,4) gWrapFan cover closes cleanly — successive "clean route" framings:
(1) "finish line = wire"; (2) "generic transport, numC=288, one lemma"; (3) "chartAtPivot-generic
sidesteps the count"; (4) route (B) K-orbit covers (blessed on decomp-5b's MC); (5) V1 fixed-center-80
covers. REALITY: the flat fan is NOT a resolution — sector-count's EXACT algebra (real shear) found
MONOMIALIZATION ⊥ COVERAGE (chart334/p1=20 is terminal but doesn't cover; the 117/118 covering charts
are non-terminal). Each of (1)-(5) was corrected by a decorrelated seat; (4) I actually BLESSED as
"adopted" on a numeric MC before the exact seat finished — premature (owned; routeP-p1 owned the
parallel over-trust).
THE MISS (root cause): I treated "does it COVER" (an MC-checkable set-cover) as the resolution gate and
UNDER-WEIGHTED TERMINALITY (each chart must monomialize / be normal-crossings). A set-cover is a weaker
object than a resolution atlas; a numeric coverage-MC CANNOT distinguish "covers" from "covers with
terminal charts" — so the MC read 100% while the atlas was hollow. The exact seat caught what the
numeric masked.
LESSONS: (a) for a RESOLUTION claim, the load-bearing sensor is EXACT algebra (monomialization), not a
coverage MC — commission the exact seat BEFORE blessing a cover route, not after. (b) Don't bless a
route ("adopted") on a numeric while a decorrelated EXACT seat is mid-adjudication — wait for the exact.
(c) The "clean route" optimism is the SAME visible-progress instinct as the render-cost optimism above,
now on a cover architecture; the damping (decorrelated exact hunt) worked 5x, but I should have front-
loaded the exact monomialization check at route-B adoption, saving cycles. NOT wasted: chart334 + 5a/5b/
part-C STAND (a genuine terminal branch); the digging surfaced theta(3,3,4)=1 (the possible #111 bypass)
+ the exact fact that the (3,3,4) resolution is intrinsically RECURSIVE (buildTree) — both load-bearing
for the endgame. NEXT: the theta=1 bypass (#111) is now itself a "clean route" candidate — being priced
HARD + decorrelated (pen-and-paper #146, mirage-check) BEFORE adoption, applying lessons (a)/(b).

## 2026-07-25 — MISS: grounded the mechanisms, over-read the economy (the decorrelated audit caught it)

**Load-bearing question:** does the operator's route-B ("resolve representatives only; transport collapses
the monument") hold — i.e. does the transport reduce the per-node build?

**My EXPECTATION (grounding, reported to operator as "every piece of §§1-3 checks out"), confidence ~0.8:**
the transport (`transportChart` + `Corank2CoreGenEquivar`) + the equal-b-run legality mean you resolve
representatives only and transport the rest, collapsing the per-node hideal work.

**ACTUAL (decorrelated audit `audit-routeB`, exact algebra + Codex, both agreeing — I verified the
catalogue myself):** MISS on the economy. `transportChart` consumes coreGen (not the stage family), so it
needs a coreGen SYMMETRY; the parent stabilizer is NOT transitive on node pivots (d=(2,2,2)); so transport
is a per-K-ORBIT-of-leaves dedup, NOT a per-node collapse. Each orbit-rep still needs the from-scratch
general-d L-A/L-B/L-C spine. Plus a NEW cover-vs-cert coherence obligation (O2). Equal-b DID hold (my one
correct sub-claim) — but my STOP-conditions gated on equal-b → FALSE-GREEN.

**What it changes in strategy:** (1) route-B re-priced UP to the substantial general-d monument (transport =
leaf-count reduction, cover-collapse holds, hideal-collapse refuted). (2) The build now carries a named O2
coherence theorem. (3) STOP-conditions re-pointed to O1/O2.

**The lesson (the miss is the product):** when grounding an ARCHITECTURE (not just a lemma), verify the
COMPOSITION-ECONOMY — the transitivity of the symmetry group on the objects being deduped, and that the
transport lemma's consumed FAMILY matches the object you claim to transport — not just that the mechanisms
EXIST. Mechanism-existence ✓ is necessary, not sufficient; I reported "checks out" on mechanism-existence and
inherited the operator's economy framing without probing it. The decorrelated obstruction seat is the
sensor that caught it — fire it BEFORE reporting an architecture "grounded", not only before the build.

---

## 2026-07-25 — CALIBRATION (idle-slot, grounding my own operator-surface): the P-fallback cite boundary + the upper/lower asymmetry

**Load-bearing question:** I surfaced to the operator "if the monument can't be closed, cite JUST the
single-chain principality — a clean, smaller cite than objects-only." Is that P-fallback genuinely STATABLE
at a clean interface boundary, or was it another over-read (the economy-miss recurring)?

**Expectation written first (confidence):** the single-chain principality is consumed at the per-leaf
ideal-identity, so a clean cite ought to exist at the `Chart.hideal_bwd` field granularity (one general
axiom quantified over terminal leaves, everything else built cite-free around it). Confidence MEDIUM-HIGH
that a field-level boundary exists; LOW-confidence on whether it's ONE axiom or a per-leaf family.

**Actual (read `ProductResolution.lean:62-139` + `Corank2UpperBound334.lean:55-77`):** HIT, and sharper.
- `Chart` carries `hideal_fwd` (⟨(∏C)∘g⟩ ⊆ ⟨diag b⟩) and `hideal_bwd` (⟨diag b⟩ ⊆ ⟨(∏C)∘g⟩) as SEPARATE
  named fields. The P-fallback = provide `hideal_bwd` (or the single-chain principality it derives from) as
  a cited general lemma at terminal leaves; `hideal_fwd`, `jac`, `unit`, the cover, and the fold are all
  cite-free around it. Clean field-level boundary — CONFIRMED.
- SHARPENING I did not expect: the UPPER bound is ALREADY principality-free. `rlctAt_coreGen334_le_four_forward`
  proves `rlct ≤ ½·minAdm` consuming ONLY `hideal_fwd` (one-directional Object A) + Object C + a WEAK
  null-guard `lossNull_of_hideal_bwd` (strictly weaker than the reverse inclusion). So the monument lives
  ENTIRELY in the LOWER direction (`hideal_bwd`, reverse inclusion) — matching memory [[rlct-runway-target]]
  (smooth locus → upper bound; singular-locus lower bound is the hard kill-condition).
- DOVETAIL with the elder verdict (same tick): the elder's V = `⟨b_{k₀}⟩ ⊆ ⟨(∏C)∘g⟩` is precisely a
  SINGLE-DIVISOR, one-sided weakening of `hideal_bwd`. So the three arms line up on ONE axis — the reverse
  inclusion at the minimising branch: V (single-divisor containment, coupling-assisted) ⊂ P (full two-sided
  equality every leaf) ⊂ objects-only (the whole `cited_aoyagi_lower_ax`). The probe now tests the two
  weaker points on that axis.

**What it changes:** the operator-surface recommendation is GROUNDED, not another economy-over-read — this
time I read the interface before asserting the boundary. The P-fallback is a strictly narrower cite than
objects-only (a per-leaf reverse-inclusion lemma, not the whole rlct=½codim). Records a HIT against the prior
economy-MISS: the correction (read the code before reporting an architecture grounded) held here.

---

## 2026-07-25 — CALIBRATION MISS (caught by the decorrelated R2 fidelity review + Codex): hnull ≠ #172

**The miss:** across several ticks I framed the R2 cover atom's `hnull` (Lebesgue-nullity of {X=0}={R=0}) as
"backed by / discharged by the #172 recursion WITNESS" — and the R2 formaliser's `volume_commonZero_eq_zero_
of_residualNull` docstring inherited it. The fidelity reviewer (r2build-review) + a decorrelated Codex both
flagged it: **these are two DIFFERENT obligations on the same set.**
- `hnull` = "{R=0} is Lebesgue-null" = CHEAP, codim≥1 (one non-vanishing generator ⟹ null zero-set); captured
  by `volume_commonZero_eq_zero_of_single`. Elementary.
- #172 = "the loss doesn't blow up worse than ½·minAdm as points APPROACH {R=0}" = the recursion / divisor-
  ratio = the VALUE-side integrability obligation. A different, downstream thing.

**Why I missed it:** I let the shared SET ({R=0}) collapse two distinct obligations (nullity vs
approach-integrability) into one "backed by #172" phrase — a chunking error (over-merging), exactly the
"elementary, precisely" failure. Compounded by amplifying the seat's own docstring conflation instead of
catching it. The Lean was sound throughout (both lemmas are true); the slop was CONCEPTUAL/framing — which a
green build never defeats, and which the decorrelated review is precisely the sensor for.

**What it changes:** (1) the R2 cover atom is the MEASURE-BOOKKEEPING layer, NOT "the cover half of the RLCT
bound" — don't over-credit it; the RLCT lower bound still needs per-chart integrability (the R>0 sandwich
holding) + #172-approach. (2) The value-side rung scoping: the value rung owns #172 + per-chart integrability;
the cover atom's hnull is cheap and independent. (3) Corrected in memo + the docstrings (routed to the seat);
compass F10 did not carry the explicit conflation (checked).

**Process HIT:** the decorrelated fidelity review earned its keep — it SURVIVED the Lean (bedrock) yet caught
conceptual framing slop the green build + my own re-verify (which only checks form/axioms) could not. Keep
gating integration on the decorrelated review, not just the axiom re-check. (The prior economy-miss lesson
generalizes: re-derived form ✓ is necessary, not sufficient; the content/framing needs the decorrelated seat.)

---

## 2026-07-25 — PROCESS MISS (×2, seat-caught): merging on an intermediate SHA before all fixes landed

Twice I merged/verified a formaliser branch at a SHA that was NOT the final all-fixes-in commit:
(1) re-verified 8ee1df617 (9 roots) when the merge target had advanced to dab3cb308 (11 roots); (2) FF-merged
3470c1361 (#1/#2/#3) before the Q5 fix landed as 54c8ede35, so the reviewer's Q5 reword wasn't actually on
trunk. Both caught by the SEAT (reroute-R2build), not me. Both docstring/wiring-level (no soundness impact),
fixed by re-point / cherry-pick.

**Root cause:** I treated a mid-stream "fixes done @ SHA" report as the final merge-ready state and acted on
it, while more fixes (routed in a crossing message) were still in flight — a race between my merge and the
seat's follow-up pushes.

**Durable fix (adopt as merge discipline):** before ANY merge/verify, (a) require the seat's EXPLICIT "final,
all-findings-in, merge-ready SHA = X" (not just "fixes done"); (b) `git fetch` + confirm the branch tip == X
immediately before merging; (c) if I've routed a NEW finding after the seat's last push, that push is NOT
final — wait for the re-push. Cheap, and it closes the crossing-race that bit twice. (Generalizes the
calibrate-the-sensor rule to the MERGE boundary: confirm the artifact identity, not just its greenness.)

---

## 2026-07-26 — PROCESS WIN: a SEPARATE decorrelated seat caught a de-risk's framing error

The #177 hchart-derisk (one seat) framed hchart as the OUTPUT-generator survivor cover (ι = 12 coreGen
entries). The corr-derisk (#180) — a SEPARATE decorrelated seat I fired for the correspondence, NOT a
re-engage of #177 — found ι=12 is the WRONG index family for a NODE (hchart is false for any many-to-one
output-gen→pivot map; the node cover is the pivot-COORDINATE full-cover, 2↔2). Had I re-engaged the #177 seat
for the correspondence, it would likely have carried its own output-generator framing; the fresh decorrelated
seat caught it. LESSON (reinforces decorrelated-gating): for a de-risk that REFINES a prior de-risk's framing,
use a FRESH seat, not a re-engage — the decorrelation is the sensor, and same-seat continuation correlates the
error. Cost: one extra spawn. Value: caught a wrong-index-family build before the builder specified it.

---

## 2026-07-26 — MISS (reviewer-caught): dispatched a build for a brick that already existed in our OWN Core

I steered the (b) poly-null build ("zero-set of a nonzero multivariate poly is null — confirmed NOT in
Mathlib"). The builder grepped MATHLIB (correctly absent) + built it green. But it ALREADY EXISTED sorry-free
in OUR Core (`MvPolynomial.volume_zeroSet_eq_zero`, Core/MeasureTheory/PolynomialZeroSet.lean, 13 importers).
The decorrelated review caught the duplicate before merge. ROOT CAUSE: I (and the builder) verified absence in
Mathlib but NOT in our own Core — the exact half of the verify-before-building discipline (lean/CLAUDE.md:
"check our own Foundations/ before concluding Mathlib/we lack it") that I skipped when dispatching. DURABLE
FIX: before dispatching ANY "build brick X, not in Mathlib" task, grep OUR Core/Foundations for X first (or
mandate the builder do so as step 0) — a nonzero-cost build was spent re-deriving banked Core API. Cheap check,
avoids a duplicate. (The review is the backstop; the grep is the front-stop.) Not a soundness issue — a
reuse/efficiency one — but exactly the Core-bedrock discipline (stand on it, don't re-open it).

### Green center-agnostic cover ≠ correct geometry (2026-07-26, R3 first brick; reviewer + Codex xhigh)
The R3 first-brick reviewer flagged (load-bearing): `node_cover_334`'s green build is CENTER-AGNOSTIC — the
block-blowup argmax atom covers `closedBall 0 R` for ANY nonempty center (every point has an argmax coord
among the center; non-center coords are spectators). So the theorem is EQUALLY TRUE with center `{0}`,
`{0,1,2,3,20}`, or the full `{0..7,20}`. CONSEQUENCE: a green cover build certifies NOTHING about whether the
center is the geometrically-correct one — center/node-structure fidelity is a SEPARATE atlas-identity matter
(#183), NOT evidenced by the cover's green. LESSON (calibrate the sensor): a passing cover-existence build is
a WEAK sensor for geometric fidelity; do NOT read "the cover compiles" as "the geometry is right". The real
sensor is the value/atlas-identity side (does `buildTree`'s `conOracle` produce this center + the right
pullback). Gate integration-fidelity on the atlas-identity check, never on the center-agnostic cover's green.
Also sharpened: the center fixes the whole ATLAS IDENTITY / value pullback (which coords blown up vs
spectators), not merely a Jacobian exponent — my first framing ("Jacobian-monomial concern") understated it.

### CALIBRATION (2026-07-26, idle-pulse slot) — R3 value-side readiness: how much does the engine already provide?
**Q (load-bearing):** after the fold re-routes to flatCube, how much of R3's value side is already in the engine
vs still to-build, and is any of it a monument?
**EXPECTATION (locked before reading):** value side largely TO-BUILD from scratch (sandwich + #172 recursion +
G2 additivity + a chart→RLCT-value bridge); cover done via flatCube (HIGH); #109 V-lower done, #110/#111 pending
(LOW-MED); NO monument (MED-HIGH).
**FINDING (read AxCheck.lean:1385-1421 + engine grep):**
- The VALUE MACHINERY is LANDED: `rlctAt_sumSqFam_eq_iInf_charts` (atlas change-of-variables) is gated clean-three;
  `two_mul_rlctAt_eq_divisorMin` (Core.Aoyagi.Resolution: a Resolution ⟹ 2·rlct = divisorMin) exists. So
  "Resolution ⟹ value" is BUILT.
- The cite-free payoff `aoyagi_learning_coefficient_via_engine` ALREADY EXISTS and per AxCheck's recorded
  footprint carries `sorryAx` from EXACTLY ONE remaining piece — `exists_coreResolution` (the full two-sided
  Resolution atlas, Object-B monument); the DLN cites are NOT invoked (kill-path). "Summit goes clean-three the
  day exists_coreResolution lands."
- The reroute's (A) V-wire is precisely the BYPASS of exists_coreResolution: the R>0-sandwich lower (#109) +
  V-upper (#110) + Object D (#111). So R3's cover+value (flatCube ✓ + R>0 sandwich + #172 {R=0} recursion + G2
  superadditivity) IS the construction of the V-LOWER that bypasses the monument — NOT a from-scratch value side.
- ChartBridgeFaithful (8+ clauses over buildTree, clause A = the flatCube cover) is the engine's fidelity assembly.
**HIT/MISS:** MISS on "value side to-build from scratch" — the value machinery (Resolution⟹value, atlas CoV) is
LANDED; the gap is specifically the Resolution-EXISTENCE monument, which the reroute BYPASSES. HIT on "no monument
to build" (exists_coreResolution is bypassed, not built — the whole point of (A)/the V-wire).
**WHAT-IT-CHANGES:** my controller model of R3 corrected: R3 = build the V-LOWER (flatCube-cover ✓ + sandwich +
#172 + G2) → then V-upper (#110, elder: COMPLETE-GENERAL/bankable) + wire (#111) → the cite-free payoff goes
clean-three (bypassing exists_coreResolution). NARROWER + better-positioned than "build everything," but still
real labour (the sandwich-over-flatCube-leaves + G2 + #172 + wire) — NOT "nearly done." OPEN (for the elder /
cartographer): reconcile #109's board-"completed" (the OLD ideal-route lower?) vs the reroute building a NEW
flatCube-sandwich lower — is #109 superseded, or the same object? CAVEAT: the exists_coreResolution-is-the-only-gap
claim is AxCheck's recorded comment (a fresh `#print axioms _via_engine` would confirm; it's in the
informational-DIRTY section, known to carry sorryAx).

### F1 CHECK caught a resurrection RISK (2026-07-26; reviewer kernel #print axioms + Codex xhigh; the elder's mandated contingency paid off)
The elder mandated a decorrelated F1-hole-free check on the value substrate before the value build relies on it.
VERDICT: the elder's structural read CONFIRMED (F1 inapplicable to a monomial blow-up — pivotChart det =
monomial VANISHING on the divisor, not det-1; value rides the sandwich, not diagonalisation), BUT a precision +
a live risk:
- The COVER (flatCube_subset_leafPathImages / cubeBox_subset_iUnion_pivotChart_image / flatCubeLeafData_
  perLeafClause) is genuinely CLEAN-THREE (kernel-verified). ✓
- BUT leafPullback_geoAtlasNorm / chartBridgeFaithful_buildTree / leafDiagFrob_geoAtlasNorm (a `by sorry`,
  category-FALSE for det-1) / GeoInvVal ARE the RETIRED F1 α-atlas hole — they carry sorryAx. Dead-isolated
  (⛔ "DO NOT FILL" header, not aggregator-imported; the live deliverable uses the ideal-level route). A
  declared frontier, not a hidden live hole.
- RESURRECTION RISK: the ONLY built discharge of LeafPullback today is the F1 one (sorryAx). If #184 reaches for
  leafPullback_geoAtlasNorm / chartBridgeFaithful_buildTree instead of proving the sandwich FRESH, it resurrects
  the hole (Codex: "regardless of later blow-up terminology"). Correct posture (FlatCubeLeaf already follows):
  keep LeafPullback OPEN until the blow-up-sandwich discharge is built from R2 (SurvivorFanCover.sumSq_residual).
**MISS (mine + the elder's, mild):** I/the elder framed "the value substrate" loosely as flatCube/pivotChart/
ChartBridgeFaithful, and my prior idle-tick calibration said "value machinery landed." PRECISE truth: the COVER
+ the value SPINE (rlctAt_sumSqFam_eq_iInf_charts etc.) are landed/clean, but the per-chart LeafPullback
DISCHARGE (the sandwich) is NOT built — the only existing discharge is the F1 sorry, and #184 must build it
FRESH. **HIT:** the mandated decorrelated F1 check caught this BEFORE the value build wired the hole in — the
"hunt precedes trust" discipline working; a green cover ≠ a clean value discharge.
**WHAT-IT-CHANGES:** #184 acceptance GATE adopted — the value headline #print axioms must be clean-three AND NOT
route through {leafPullback_geoAtlasNorm, chartBridgeFaithful_buildTree, leafDiagFrob_geoAtlasNorm}. That single
kernel check catches any accidental F1 re-wiring. Relayed to the builder (build (i)(a) fresh, never reuse those).

### CALIBRATION (2026-07-26, idle slot) — the V-lower WIRE: how does the per-chart atom compose to rlct ≥ ½minAdm?
**Q:** after (i)(a) lands, how does rlctAt_sumSqFam_eq_iInf_charts + the per-chart atom compose, and what must the wire supply?
**EXPECTATION (locked):** it's an EQUALITY rlctAt(∑Fᵢ²) 0 = ⨅_charts (per-chart wrlctAt), consuming the cover +
chart family; the wire plugs the per-chart ≥ ½chartMin under the inf; min_c chartMin = minAdm (atlasRealizes).
**FINDING (read ProductResolution.lean:630 + docstring):** HIT. rlctAt_sumSqFam_eq_iInf_charts IS the equality
(rlct = min/inf over the per-chart weighted values). Docstring makes the load-bearing point explicit: "the
single point 0 of ONE chart only gives an UPPER bound; the COVERING FAMILY gives EQUALITY." So the flatCube
COVER is load-bearing for the EQUALITY itself (not merely the bound) — this is precisely why the value must ride
the same pivotChart family (the elder's natural-W1 marriage). Each chart is a `Chart` structure (g, hg0,
hg_cont, + Aoyagi's hypotheses as propositional fields).
**WHAT-IT-CHANGES:** confirms the wire is well-scoped + all pieces in place — rlctAt_sumSqFam_eq_iInf_charts
(equality, banked) + per-chart atom (i)(b), merged @2c947b0fd) + (i)(a) (building) + atlasRealizes (min=minAdm,
banked). The wire = composition once (i)(a) lands; the cover (flatCube) supplies the family for the equality. No
re-plan. Prep for gating/briefing the wire fast. NOTE for the wire build: the Chart-structure fields (Aoyagi's
per-chart hypotheses) must be supplied for EACH flatCube chart — the "over ALL charts" watch-item is that the
covering family (not one chart) inhabits the equality.

### A tracked-open skeleton can TYPECHECK yet be FALSE — the early API-check caught it (2026-07-26, wire #187)
The builder statement-locked the V-lower wire (`rlctAt_ge_iInf_threshold_of_sandwich_cover` @e195fb436) — it
TYPECHECKED + banked tracked-open. The fresh formaliser's MANDATED early API-check (before filling) found it
FALSE: missing `BddAbove`. Counterexample (D=1, g=id, x₀=5, F 0 = ·0 so loss = w₀²): all hypotheses hold, but
near x₀=5 the loss ≈ 25 > 0, so localAdmissible = [0,∞) (NOT BddAbove), sSup = junk = 0, rlct = 0 — conclusion
"½ ≤ 0" FALSE. ROOT: the sandwich is a LOWER bound only; it can't force x₀ to be a genuine pole. "rlct finite /
BddAbove" = the V-UPPER content (#110), which this wire bypasses — so the honest V-lower MUST take BddAbove as a
hypothesis (load-bearing, discharged downstream by V-upper). FIX: +hbdd (load-bearing — counterexample-proven,
NOT a weakest-hypotheses violation), −hunit1 (unused with the monomialThreshold conclusion; moves to the
downstream conversion).
**LESSON (reinforces "fix wrong statements first", lean/CLAUDE.md):** a typechecking tracked-open skeleton is
NOT a correct statement — Lean checks types, not truth. The P6 statement-lock discipline MUST pair with an
early SEMANTIC/counterexample check, especially for a durable Core API. The fresh-context formaliser + the
"quick-review the record BEFORE filling" instruction caught a FALSE target before the ~85-line fill was built
on it — the strongest vindication yet of statement-lock-then-early-check + fresh-context review.
**Math note:** the V-lower ≥-half genuinely DEPENDS on V-upper's finiteness (BddAbove) — the two halves are NOT
fully independent; the ≥ direction needs the pole to be finite (one-directional: V-upper doesn't depend on
V-lower, no circularity).

### CALIBRATION (2026-07-26, idle slot) — V-upper (#110) status: is the wire's hbdd source proven?
**Q:** the wire's new hbdd (BddAbove) is discharged by V-upper — is V-upper proven in-repo, and is hbdd available?
**EXPECTATION (locked):** V-upper's core (rlct ≤ ½chartMin ⟹ BddAbove) likely proven in-repo (forward lemma),
#110 the reroute wiring; hbdd available. Confidence MED.
**FINDING:** HIT. `rlctAt_sumSqFam_le_chartMin_half` (Corank2UpperBound334.lean:25) = the (3,3,4) V-upper,
0 sorries. `Chart.rlctAt_le_chartMin_half_forward` (ProductResolution.lean:501) = the general forward lemma
(rlct ≤ ½chartMin) whose proof establishes localAdmissible ⊆ [0,½chartMin) = exactly the wire's hbdd/BddAbove.
So the elder's "V-upper complete-general/bankable" is confirmed, AND the wire's hbdd is dischargeable from the
existing V-upper (the missing-BddAbove fix has a ready source).
**WHAT-IT-CHANGES:** the post-wire assembly is well-positioned — V-lower (wire, in-flight, +hbdd) + V-upper
(proven) + Object D (neq_cCodim) + hbdd (from the forward lemma) are ALL present; the 2rlct=cCodim assembly is
composition once the wire fill + the concrete hpull discharge land. NOTE: #110 board-"pending" may be stale (the
core is proven) or = the reroute-charts wiring residual — confirm at the wire landing / assembly.

- **2026-07-26 wire-structurally-excludes-Morse (bedrock gate).** The V-lower wire applies to a flatCube leaf IFF it is unit-residual (resRank=0): the hsandwich needs residualCore ≥ a positive constant (only residualBaseForm=1/UNIT supplies it), and a Morse leaf (resRank>0, ‖z‖²) fails two ways — no kept-1-pivot (hf0) + folding breaks hchain's divisibility chain. So the whole (3,3,4) discharge route reduces to ONE gate: is every buildTree leaf resRank=0? (Evidence YES: canonical resRank=0 + terminalExponents≥minAdm=8 ⟹ no Morse leaf; exhaustive enumeration in flight.) Insight: the wire's hypotheses SELF-SELECT the unit-residual leaves — the resRank>0 contingency is the only place hidden work (a #172 refinement, or an unbuilt Morse-folding brick) could live; front-loaded it as the pre-delegation gate.

- **2026-07-26 resRank=0-all PROVEN (the discharge unblocked).** The load-bearing gate came back the cleanest possible: every (3,3,4) geoAtlas leaf is resRank=0 (unit-residual), kernel-proven axiom-clean as a UNIVERSAL (leafOfState hardcodes resRank:=0; the engine fully monomializes into the divisor ledger). Zero Morse ⟹ #172 drops out of BOTH residual and cover (exact containment) — the discharge simplifies to survivor + exact cover + per-leaf chart algebra, no recursion. Insight: the risk MOVED from "is there a Morse leaf?" (no, ledger-proven) to "does hpull hold per leaf?" (the concrete K=monomial²·survivor algebra — canonical proven via gWrap, others = the pre-mortem gate). Front-loaded hpull as the formaliser's first internal gate + surface-on-wall. The resRank=0 field is necessary-but-not-sufficient (faithfulness lives in hpull) — didn't over-trust the ledger field.

- **2026-07-26 the fidelity gate CAUGHT the wall (closed loop worked) — but the wall is real.** The hpull pre-mortem, front-loaded precisely because elder+controller+scout flagged resRank=0 as ledger-not-geometry, hit a genuine WALL: the transport-free geoAtlas chartMap is shear-free and the pointwise det-1 diagonalization is refuted (the F1 hole), so the wire's pointwise hpull hypothesis CANNOT be discharged transport-free — per-leaf = the Corank2*Proto monument. WIN: the gate + the formaliser's stop-condition prevented a monument-grind; the "resRank=0 ⟹ survivor" inference was unsound (vacuous ledger field), exactly as flagged. RECALIBRATION: the (A) sandwich-bypass premise may be false at the COVER level (pointwise hpull per leaf ≈ the monument it was meant to bypass) — the merged wire may be vacuous-for-our-cover (a spike). Elder adjudicates Option-C (ideal-level via Lemma 1/#109) vs the STOP-FALLBACK. Lesson: a merged abstract wire whose hypotheses can't be discharged is a spike; the discharge (not the wire) is the real gate — front-load the hpull pre-mortem was right.

- **2026-07-26 the wall was mis-priced — verdict 3a (headline TRUE, value = detail-at-scale via the born shear).** The claimed discharge wall (STOP-FALLBACK-in-view) was NOT real: the pnp's exact computation confirmed the elder's mis-pricing catch (factorization [dead F1] ≠ the from-below inequality [the wire's need, achievable]) AND sharpened it — the inequality is achievable but MUST ride the born incidence shear (shear-free R-α refuted: the singularity has a hidden vanishing branch off every coordinate hyperplane, so no shear-free coordinate monomial lower-bounds the loss). rlct=4=½·codim CONFIRMED for (3,3,4). Lesson: a wall-diagnosis reasoning STRUCTURALLY ("proven-result-rides-shear + F1-refutes-the-normal-form") can be right about the dead route (normal form) yet wrong about the live need (inequality) — only the exact computation separated them; and even the reroute (R-α) needed correction (shear load-bearing, not droppable). The remaining labour = fill the born per-leaf α (route P's realization residual, detail-at-scale, NOT a wall). Twice the decorrelated seats (elder mis-pricing catch + pnp exact) corrected the controller's over-amplified wall — the value of NOT surfacing a destination call on a structural argument.

- **2026-07-26 the last monument-gate CLEARED (general-d born-α generalizes).** The general-d probe returned YES: the born-α value bound is corank-INSENSITIVE because the single survivor entry Pmat[0][0] hits only the pivot cross, never the coupled residual block where the monument-hardness lives. Exact r=2..5 + Codex; construction uniform (no per-corank insight). So the (A) cite-free value headline is reachable at FULL generality, detail-at-scale — the two-sided normal form (the actual monument) is never needed for the VALUE bound. Insight: the mis-priced-wall lesson generalizes — the monument is in the RESIDUAL (two-sided clearing), the value bound rides ONE pivot-cross entry that avoids it entirely. Residual risk = a BOUNDED fed-form-preservation invariant (verified at 2 instances), NOT a monument. The controller's earlier over-amplified wall (STOP-FALLBACK-in-view) is now doubly-corrected: mis-priced at (3,3,4) AND the general-d version dissolves the same way.

- **2026-07-26 the LAST monument cleared (general-d cover = detail-at-scale).** The general-d sheared cover — the one remaining monument-question (F11's "biggest monument-adjacent rung", the L7/MonumentAtlas frontier) — priced DETAIL-AT-SCALE by two decorrelated derivations: the born shear is always a triangular QUADRATIC block-shear (polynomial/det-1, because Aoyagi recurses ONE scalar pivot per node, never a whole-block inverse), C_* ≤ W(d) depth-independent, and the 3 monument-flags (cert-psi-mix/#145/non-uniform-C) are all artifacts of the RETIRED ambient-gauge chart-route, not the engine's block-blowup-outer/shear-inner model. Path A (reparam_image reduces the sheared cover to the landed shear-free cover) makes it ~90% landed. NET: (A) is MONUMENT-FREE at full generality — value monument bypassed (pivot-cross) + cover monument cleared (quadratic block-shear + box-inflation engine). The whole (A) map is now priced: no monument anywhere; remaining = construction labor + the shared resolution condition (next-center-coordinate-block, paper-resolved + instance-green). The expedition's central bet — cite-free RLCT lower bound bypassing exists_coreResolution — is priced SOUND end-to-end.

## 2026-07-26 — steering imprecision (my steer, caught by decorrelated review)
CONTEXT: steering the reduction reviewer on rlctAt_coreGen334_ge_four_of_family, I said the ≥4 read-off is 'honest
ONLY via divisorMin=8 EXACTLY, NOT merely ≥8.' IMPRECISE (reviewer + Codex): for the LOWER bound 4 ≤ rlctAt,
divisorMin ≥ 8 already suffices (v≥8 ⟹ v/2≥4); the ≤8 belongs to the SEPARATE V-upper. The theorem uses the equality
(Object-D exact =8), correct + satisfiable — NOT a defect, but 'ONLY via =8' overstated necessity. LESSON: when
steering a reviewer on a ONE-SIDED bound, name the load-bearing DIRECTION (≥ for a lower bound), not the two-sided
equality, unless the equality is genuinely needed. ≥8-fallback relayed to the born-α seat.

## 2026-07-26 — CALIBRATION (phase-transition de-risk→build): sizing piece (4), the summit re-point
QUESTION: does the summit/headline route through exists_coreResolution (the monument), and how big is piece (4)
[via_engine re-point → exists_coreResolution DEAD in the headline cone]?
EXPECTATION (first): (i) the payoff (LearningCoefficient/via_engine) EXISTS + currently routes through
exists_coreResolution — conf MEDIUM-HIGH; (ii) the re-point to the cite-free V-lower+V-upper is MOSTLY bookkeeping —
conf MEDIUM.
ACTUAL (grep @aoyagi-r3wire): exists_coreResolution in ~9 files incl. LearningCoefficient.lean (the payoff) +
RecursionAdapter / Corank2Realize334 / MonumentAssembly / MonumentAtlas / GeometricAtlasD12 / Corank2GeoAtlas +
Core/BlowupResolution (def site). HIT on (i): the payoff file references the monument.
REFINEMENT on (ii): 'mostly bookkeeping' is UNVERIFIED — exists_coreResolution threads through MULTIPLE
headline-adjacent files, so the re-point may be a genuine dependency-cone RE-WIRE (re-point LearningCoefficient's path
onto the cite-free wire + verify #print axioms drops exists_coreResolution from the headline cone), not a one-liner.
Exact size needs a #print axioms on the current headline (how DEEP the monument sits in the cone) — deferred
(summit rung is downstream of #188; proportionate).
WHAT IT CHANGES: scope piece (4) as a real (monument-free) re-wiring integration task, not a trivial flip; at the
summit rung FIRST #print axioms the current headline to size the cone, THEN re-point. (Retired monument-route files
MonumentAtlas/Assembly/GeoAtlas likely OUT of the headline cone — the #print axioms confirms which are load-bearing.)

## 2026-07-26 — build-vs-cite discriminator: 'monument' (builder) → detail-at-scale (decorrelated) CAUGHT
The assembly formaliser flagged the ×9 hentry entry-algebra as a 'genuine monument.' Controller read = DETAIL-AT-SCALE
(pnp F5-F9 exact-certified ⟹ insight FOUND; patient Lean construction of certified math). Routed to the elder for a
decorrelated read: elder CONFIRMED detail-at-scale + did a confound check (no hidden hard general lemma in the σ_p
construction). LESSON: a builder's 'monument/too-hard-to-land' flag is often timidity-disguised-as-rigor (the disposition's
named failure); the discriminator is FOUND-vs-UNFOUND insight, never in-Mathlib-vs-not or Lean-landed-vs-not. When a
builder flags a monument, apply the discriminator + confound-check the CONSTRUCTION before believing it — build-the-buildable.

## 2026-07-26 — CALIBRATION (idle, assembly-completeness): all reduction hyps assigned to A/B/C, NO orphan
QUESTION: are ALL hypotheses of rlctAt_coreGen334_ge_four_of_survivor_entries assigned to A/B/C or landed, or is there
an ORPHAN that would strand the assembly?
EXPECTATION (first): all assigned (hentry→B, area-data + hcover→A, divisorMin→C, hunit_mult/hbind def-level); conf HIGH;
risk = a non-routine area-data field.
ACTUAL (read the signature @r2assembly): full hyp list —
  (A) fan def + analytic fields: g/dom/nbhd/excep/unit/jac + hgdiff/hdomcpt/hnbhd_open/hdom_sub/hexcep_meas/hexcep_null/
      hg_inj/hunit_cont/hunit_ne/hjac + hU/hcover.
  (B) hentry (∀ c w, coreGen(k0 c)(g c w) = ∏ w^ek₀).
  (C) hdivisorMin (⨅=8) + hbind (binding axes nonempty) + hunit_mult (ek₀=1 on binding axes) + the jac exponents.
RESULT: HIT — every hyp maps to A/B/C or def-level; NO ORPHAN. Assembly-complete.
REFINEMENTS: (i) hunit_mult (ek₀ d=1 on binding axes) is the load-bearing G1 fact (kexp=1 ⟹ divisorMin the right
threshold; k≥2=red-flip) — covered by (C)/ek₀-def per the pnp cert (unit folded as exponent-1); (ii) hjac (|jacDet g|
= jacWeight jac × |unit|) needs (A)/(C) to compute the born-native 3-node blow-up Jacobian → jac exponents → the
multi-node divisorMin=8 (detail-at-scale, blow-up Jacobians landed); (iii) the entry's unit=1 (exact hentry) is SEPARATE
from the Jacobian's unit (in hjac, nontrivial) — no conflict. CHANGES: assembly de-risked (no orphan); at (C) ensure
hunit_mult (G1) + the 3-node jac; the assembly = pure wiring once A/B/C land.
