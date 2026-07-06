# genm-d1l2close2 — LEAF-2 close BLOCKED at the concrete `q₂`: needs a new explicit-core producer

Charged to CLOSE the L=2 D1 `≥`-leg by binding `q`/`q₂` to the CONCRETE residual that
`d1ge_L2_rect_two_peel_hrank_closed` constructs and discharging the 4 gates for that `q`
(gatesclose2's proposed re-architecture), reaching sorry-free `aoyagi_learning_coefficient_L2`.

Per "FRONT-LOAD the crux; if it genuinely resists, isolate the precise obstruction + report — do
NOT launder", this tide front-loaded the crux `degraded_slice_rlct_eq_lambdaCore` (the model
identification `R₂ = unit·(dlnLoss M' 0)∘φ`). The verdict (my analysis + decorrelated Codex xhigh,
`codex/crux-answer.md`): **binding to the concrete `q₂` is ALSO insufficient — the value gate is
blocked at a deeper level than gatesclose2's "∀-`q`" finding.** The single LEAF-2 `sorry` is
retained (green-with-one-sorry); its comment now carries the sharpened finding + the corrected
roadmap. **No wall was laundered** (gatesclose2 reverted a green-but-misleading plug; this held that
line — comment/card only, no code-logic change).

Branch `origin/genm-d1l2close2` (from `origin/genm-gatesclose2` @ `70a415a2`). One code change: the
LEAF-2 comment in `HeadlineL2Assembly.lean`; build unchanged (green, one `sorry` at line 78/123).

## The sharpened obstruction (why the concrete `q₂` cannot support the value identity)

The concrete `q₂` that `d1ge_L2_rect_two_peel_hrank_closed` constructs (via
`secondPeel_hchart_residual` ∘ `residJacobian_rank_eq`) is the ABSTRACT IFT-peel residual. Both peels
route through `rlctAtOn_eq_of_contDiff_chart_rinv` (`D1HChartInverse.lean`), whose output REPLACES the
explicit DLN polynomial loss `f` by `f ∘ Ψsymm`, where `Ψsymm` is an EXISTENCE-ONLY IFT inverse
(`exists_boundedUnit_chart_of_contDiffAt` — no closed form, no retained algebraic tie to `dlnLoss`).
After two peels, `q₂ = (bump-globalisation of) [ (h ∘ Ψsymm₂), selected components zeroed ] ∘
splitHomeo⁻¹` — defined purely through `Ψsymm`, `Ψsymm₂`, and bump cutoffs.

* What survives: FIRST-ORDER data. `D1ResidualDerivExpose` exposes the slice derivative; b3 gives
  `rank(jacResid) = extraCountRect`. This is enough for `hRne` (slice a.e.-nonzero — a positive-rank
  `C¹` zero-set is measure-zero) but NOTHING higher-order.
* What is discarded: the higher-order germ that PINS the RLCT value. Codex's precise diagnosis:
  "insufficient germ data" (not literally "nothing algebraic survives"). The prior `R = x² + u⁴`
  counterexample lives at exactly this level — it peels to slice `u⁴`, `rlctAtOn = 1/4`, and NO
  first-order data distinguishes it from a genuine core, so the value is unpinned.
* Consequence: `rlctAtOn(slice-of-q₂) t0₂ = ofReal(lambdaCore(M'))` (the `hInterface`/`hDegraded`
  value gate) is UNPROVABLE from what the producer retains. **The one-sided lower bound
  `lambdaCore(M') ≤ rlctAtOn(slice-of-q₂)` is EQUALLY blocked** (Codex confirmed): any nonzero handle
  on the abstract residual's value is absent. Strengthening `rlctAtOn_eq_of_contDiff_chart_rinv` to
  return more derivatives does NOT help — finite-jet data do not pin the RLCT.

So the 4-lemma runway gatesclose2 proposed is dead for gate (b): lemmas 2/3/4 all feed `hInterface`,
which is fundamentally blocked through THIS `q₂`. Only lemma 1-class first-order facts (`hRne`) are
reachable, and they alone cannot close LEAF-2.

## The corrected roadmap (Codex-recommended, matches `genm-d1reduce-aoyagi`)

Retire the two-IFT-peel producer for this leg; route through the EXPLICIT homogeneous core. Two
BANKED pieces reduce the WHOLE leg to ONE new producer:

* `deepest_le_of_optimal_via_L2_ge` (`DeepestMinRlct`, PROVEN) — the abstract bridge:
  `Ldeepest = nReg/2 + coreDeepest`, `nReg/2 + coreV ≤ Lv`, `coreDeepest ≤ coreV` ⟹ `Ldeepest ≤ Lv`.
* `deepest_le_of_homogeneous_core` (`DeepestMinRlct`, PROVEN, HYPOTHESIS-FREE) — measurable +
  degree-`D` homogeneous ⟹ `rlctAtOn F 0 ≤ rlctAtOn F v`. This discharges `hCore` DIRECTLY when
  `coreDeepest = rlctAtOn (dlnLoss (H−r) 0) 0` and `coreV = rlctAtOn (dlnLoss (H−r) 0) corePoint_v`
  (the SAME explicit homogeneous core `dlnLoss (H−r) 0`, evaluated at two points).

The single remaining OPEN obligation:

    hAtV : (nRegL2 H r)/2 + rlctAtOn (dlnLoss (H−r) 0) corePoint_v ≤ rlctAt H (dlnLoss H B') v

— the Aoyagi Step-1 explicit iterated corner-elimination BLOCK REDUCTION, landing `rlctAt v` on the
EXPLICIT DLN core `dlnLoss (H−r) 0` at an explicit reduced-core point `corePoint_v`. Because it lands
on the explicit polynomial core (not an abstract residual), its RLCT/homogeneity IS accessible (R1
`r1_resolution_general` for the value at `0`; `deepest_le_of_homogeneous_core` for the comparison),
and NO residual-value identity / R1-at-`M'` interface is ever needed. Prerequisite lemma the producer
also needs: `dlnLoss (H−r) 0` is homogeneous of a fixed degree in the reduced parameters (to feed
`deepest_le_of_homogeneous_core`) — verify/bank this alongside.

**This is a fresh ~600–1500-line tide** (the de-risk's estimate for Aoyagi's explicit block
reduction) — a NEW producer, NOT a gate-discharge for the existing `q₂`. It is the same producer the
∀-L Skeleton sorry `rlctAt_deepest_le_of_optimal` (Skeleton:1172) needs (this L=2 instance is its base
case), so the design lifts.

## Why this supersedes gatesclose2's recommendation

gatesclose2 concluded "the closing must construct `q`/`q₂` internally and discharge the gates for
those." This tide establishes that the internally-constructed concrete `q₂` STILL cannot support gate
(b), because the IFT-peel construction (`rlctAtOn_eq_of_contDiff_chart_rinv`) discards the germ data
the value identity needs. The fix is not "discharge gates for the concrete `q₂`" but "produce a
DIFFERENT residual that IS the explicit DLN core" — Aoyagi's explicit block reduction. This corrects
the leg's direction: no further effort on the two-peel `hInterface` gate; the next tide builds the
explicit-core producer.

## Build status

`HeadlineL2Assembly` green, one `sorry` (LEAF 2, `aoyagi_learning_coefficient_L2`, line 78/123) —
unchanged from `origin/genm-gatesclose2`, comment updated with the finding. Core-geometry (b3 +
`hrank₂`, `d1ge_L2_rect_two_peel_hrank_closed`) remains DONE and green. `aoyagi_learning_coefficient_L2`
is NOT yet sorry-free (blocked on the explicit-core producer `hAtV` above).

## Artefacts

- `codex/crux-prompt.md`, `codex/crux-answer.md` — the decorrelated verdict (PARTIALLY =
  blocked-conclusion-correct, reason "insufficient germ data"; lower bound equally blocked; minimal
  fix = new explicit-residual producer, not a chart-lemma strengthening).
