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
