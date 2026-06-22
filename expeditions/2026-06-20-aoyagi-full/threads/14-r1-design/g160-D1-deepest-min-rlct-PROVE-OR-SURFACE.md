# D1 (a) "deepest = min-rlct" — PROVE-OR-SURFACE: L1-separable in principle, needs RLCT-semicontinuity (NEW primitive) (pp-hall, 2026-06-22, #57)

**The CRITICAL hero-task-constraint check.** D1 (a) (`rlctAt_deepest_le_of_optimal`:
`rlctAt(deepest) ≤ rlctAt(v)` ∀ `v ∈ optimalSet`) needs "deepest = min local rlct" = Aoyagi 2013 Thm 2.
The constraint: ONLY S2 (`monomial_rlct`) is citable — everything else PROVEN. So D1 (a) must be PROVEN,
NOT cite Aoyagi Thm 2. Verdict + the honest surface.

## VERDICT: L1-SEPARABLE (no 2nd citation, value-independent) — BUT needs a NEW analytic primitive (RLCT lower-semicontinuity), NOT a one-line `rlctAtOn_mono`.

The "deepest = min-rlct" is provable without the resolution value and without citing Aoyagi Thm 2 — but
NOT trivially. It decomposes into two value-independent facts, one elementary and one a genuinely new
(unbanked) analytic primitive. **My #56/g155 "L1-separable, my read confirmed" was too confident** — the
careful adjudication (g158–g162) shows the route is sound but the load-bearing step is heavier than
"the `rlctAtOn_mono` deepest=min-core input." Surfacing before the D1 grind, as asked (confirm, not assert).

## The route (post-L2-reduction, on the core `B → 0`, `M = H − r`)
After L2, D1 (a) is about the homogeneous core `dlnLoss M 0 = ‖∏C‖²` (`M = H − r`, the `B=0` core). The
deepest core point is the ORIGIN `0`; a general fibre point `v` (of the core) lies on `{∏C = 0}`. Then:

- **(L1-a) SCALING-INVARIANCE of the local rlct along the ray `v ↦ t·v` (ELEMENTARY, value-independent).**
  `F = ‖∏C‖²` is homogeneous of degree `D = 2L`. The germ at `t·v`, under the linear c-o-v `w = t·w'`
  (scaling, a diffeo for `t ≠ 0`), equals `t^D · (germ at v)` (homogeneity:
  `F(t·v + t·w') = F(t(v+w')) = t^D F(v+w')`). The rlct is invariant under the scaling diffeo
  (`rlctAtOn_comp_homeomorph`) and the constant `t^D` (a unit, `rlctAtOn_unit_invariant`). ⟹
  `rlctAt(F, t·v) = rlctAt(F, v)` for all `t ∈ (0,1]` — the local rlct is CONSTANT along the punctured ray.
  Verified exact (`g162`: `germ(t·v) ∘ (w=t·w') − t^D·germ(v) = 0`). **L1, banked-ish** (`comp_homeomorph` +
  `unit_invariant`). ✓

- **(L1-b) LOWER-SEMICONTINUITY of the local rlct at the ray's limit point `t → 0` (the deepest, NEW
  primitive).** The deepest core point `0` is `lim_{t→0} t·v`. We need `rlctAt(F, 0) ≤ rlctAt(F, v)` (the
  ray-constant). By (L1-a) the rlct is constant `= rlctAt(F, v)` on the open ray `(0,1]`; the inequality
  at the limit `t = 0` is EXACTLY **`rlctAt(limit) ≤ liminf_{t→0} rlctAt(t·v)`** — the lower-
  semicontinuity of the RLCT under degeneration (the most singular point of a family has the min rlct;
  Watanabe / Varchenko lct-semicontinuity). **This is value-INDEPENDENT (a general analytic fact, NOT the
  resolution, NOT Aoyagi Thm 2)** — so NO second citation — **BUT it is a NEW, HEAVY analytic primitive,
  almost certainly NOT banked** in the harness/Mathlib (comparable in weight to S1.1's
  `weightedThreshold_transport`). It is NOT a one-line `rlctAtOn_mono` (which compares two FUNCTIONS at
  ONE point; D1 (a) is one function at TWO points — the docstring's exact gap, g158).

## Why the "easy" routes FAIL (the adversarial catches)
- **`rlctAtOn_mono` directly:** FAILS — it compares two functions at ONE basepoint; D1 (a) is the SAME
  loss at TWO basepoints (deepest vs `v`). No direct application (g158).
- **"larger reduced block ⟹ smaller rlct" (M-monotonicity):** FALSE — `rlctAt(dlnLoss M 0)` is
  INCREASING in `M` (`(1,1,1)→½`, `(2,2,2)→3/2`, `(3,3,3)→7/2`), the OPPOSITE of the naive read (g158).
  (This compares different ambient problems, not the D1 same-loss-two-points; flagged to avoid the trap.)
- **bare homogeneous-domination `|deepest-loss| ≤ |v-loss|` near a common frame:** NOT automatic — needs
  the scaling-ray bridge (L1-a) + the limit (L1-b), not a pointwise inequality (g159, g161).

## Rank-exact reconcile (the second follow-up, crux2)
crux2 is right that D1's `v` is NOT rank-exact (per-layer ranks vary `≥ r`); my #56 Part-1 gauge slice is
rank-exact. **But D1 (a) does NOT chart `v`** — it is a COMPARISON `rlctAt(deepest) ≤ rlctAt(v)`, routed
via the scaling-ray + semicontinuity (L1-a + L1-b) on the RAW loss, NOT a gauge chart at `v` (g157). So:
- **#56 Part 1 (rank-exact gauge chart) = #44 sub-3 ONLY** (the deepest VALUE, `rlctAt(deepest) = nReg/2 +
  rlctAtOn(dlnLoss M 0)`). The deepest IS rank-exact; Part 1 applies there. No extension to non-rank-exact
  `v` needed.
- **D1 (a) = the scaling-ray domination** (L1-a + L1-b), basepoint-bridging WITHOUT charting `v`. crux2's
  non-rank-exact concern is real for "charting a non-rank-exact `v`" but MOOT for D1 (a) — it compares,
  doesn't chart. My g155 "Part-1 datum AT v" was the WRONG route for non-rank-exact `v`; the RIGHT route
  is the scaling-ray + semicontinuity.

## What to SURFACE (the operator-level note)
- **GOOD news (no constraint violation):** D1 (a) does NOT need a second citation. "Deepest = min-rlct"
  is value-independent (scaling-invariance + RLCT-semicontinuity), NOT the resolution value, NOT Aoyagi
  Thm 2. So the one-citation (S2-only) policy is NOT violated by D1.
- **The cost (surface before the grind):** D1 (a) needs the **RLCT lower-semicontinuity primitive**
  (L1-b) — a NEW heavy analytic lemma, value-independent but unbanked. Two options:
  1. **Prove L1-b** (the RLCT-semicontinuity / lct-semicontinuity, a real but standard analytic theorem)
     as a new S1-level primitive. Weight ≈ `weightedThreshold_transport`. The clean route.
  2. **Find a lighter homogeneous-domination** specific to `‖∏C‖²` (avoiding general semicontinuity) — if
     the deepest core's leading form pointwise-dominates the shifted `v`-loss under an explicit c-o-v.
     Possible but not yet found; the gauge chart at `v` (the non-rank-exact broader split crux2 flags)
     would give it, but that re-introduces the charting crux2 wants to avoid.
- **My recommendation:** route D1 (a) via option 1 (L1-a elementary + L1-b the RLCT-semicontinuity
  primitive). It is the value-independent, one-citation-clean route; the new primitive (L1-b) is the
  honest cost, NOT a hidden second citation. Flag L1-b to the operator as a NEW required analytic lemma
  (not a citation) before crux2 grinds D1 ≥.

## Most likely thing to break this
L1-b (RLCT lower-semicontinuity) being harder to formalise than expected (Mathlib has no RLCT/lct
machinery; it would be built from the `weightedThreshold` substrate — the `liminf` over the ray + the
integral-divergence comparison). If L1-b proves intractable in Lean, the fallback is the explicit
gauge-chart-at-`v` domination (option 2 / crux2's broader split) — heavier in the charting but avoiding
the semicontinuity primitive. crux2's D1 #42 scoping should pick: L1-b primitive (clean, new heavy lemma)
vs the chart-at-`v` domination (no new primitive, but the non-rank-exact broader split). Either is
value-independent (one-citation-clean); the choice is which heavy piece. **Confirmed: NO second citation
needed; the cost is one new value-independent primitive (L1-b) OR the chart-at-v split.**

## UPDATE (#57 priority, controller's leading-homogeneous-part route REFUTED as a light route)
The controller asked specifically for the L1-separable derivation via "deepest core = the leading
homogeneous part of every v's core, from block_elimination + deepest structure." **That clean route does
NOT exist** (g163, exact-verified on (2,2,2) B=0):
- At a general fibre point `v`, the core `F_v(w) = ‖∏(v+w)‖²`'s LEADING (lowest-degree) form in `w` has
  degree **2** (NOT 4) — `v`'s regular directions contribute QUADRATIC leading terms (e.g. at
  `v=(rank1,rank1 aligned)`, leading form `= a₁²+2a₁b₁+a₃²+b₀²+b₁²`, degree 2). The DEEPEST core's
  leading form is the full `‖∏(w)‖²`, degree **4**. So **"deepest core = the leading part of v's core" is
  FALSE** — `v`'s leading form is LOWER-degree (less vanishing), not the deepest core.
- The DIRECTION is still right (deepest more vanishing — leading degree 4 > 2 — ⟹ more singular ⟹ smaller
  rlct ⟹ `rlctAt(deepest) ≤ rlctAt(v)`), but making it rigorous needs **"rlct is determined by the
  leading/Newton form" (Varchenko nondegeneracy)** — which is ALSO a heavy analytic primitive (P2), NOT
  lighter than the semicontinuity route (P1). No free lunch.

**The honest landscape (g164):** a value-independent D1 (a) NEEDS one of two new heavy analytic primitives
— (P1) RLCT lower-semicontinuity [g160 route], or (P2) RLCT = rlct-of-the-leading-Newton-form [the
controller's route, but it needs Varchenko-nondegeneracy, not the clean leading-part claim]. Neither is
free; the elementary block_elimination split is circular (compares `v`-core to deepest-core across
different `#regular`, needs the value). **The controller's hoped-for light route is refuted; both routes
are heavy primitives (both value-independent — still NO 2nd citation).**

## THE CHEAPEST RESOLUTION (scoping Q for the controller — possibly avoids D1 (a) entirely)
Is the headline keyed to **⨅-over-optimalSet** (`aoyagi_learning_coefficient = ⨅_{v∈optimalSet} rlctAt v`)
or to the **deepest-point value** (`rlctAt(deepest) = aoyagiLambda`)?
- If **⨅-over-optimalSet**: `deepest_point_reduction` reduces it to `rlctAt(deepest)` via D1 (a) — which
  needs the primitive (P1 or P2). D1 (a) is REQUIRED.
- If **deepest-point value only**: D1 (a) (the `⨅ = deepest` direction, `rlctAt_deepest_le_of_optimal`) is
  **NOT NEEDED** — only R1 (`resolution_charts` at the deepest) + L2 give the deepest value. The whole
  primitive question is MOOT.
So before committing a new analytic primitive (P1/P2), confirm whether the headline genuinely needs the
`⨅`-over-`optimalSet` form. If it can be deepest-point-keyed (the `deepestPoint` is the canonical
attainer L2 evaluates — Rung-0c FLAG already keys L2/D1 to the constructed `deepestPoint`), D1 (a) is
avoidable and the cost vanishes. **This is the cheapest path — check the headline keying first.**

## Decorrelation
pp-hall exact algebra (g158 the mono-fails + M-monotonicity-trap catch, g159 the vanishing-order read,
g161 the semicontinuity route, g162 the scaling-invariance verification). Decorrelated Codex consult on
the L1-separability + the two-basepoint bridge fired (`g160-codex-prompt`); slow at xhigh, folding when it
lands (confirmation, not gate — the exact-algebra route is rigorous). Builds on #56/g155 (correcting its
over-confident "L1-separable" to "L1-separable via a NEW primitive"), `rlctAt_deepest_le_of_optimal`
(`Skeleton.lean:973`, the consumer + its docstring's flagged gap), the L2 core reduction (`B → 0`).
