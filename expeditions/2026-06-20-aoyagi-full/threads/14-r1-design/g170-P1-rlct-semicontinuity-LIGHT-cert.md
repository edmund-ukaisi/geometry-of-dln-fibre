# P1 cert: RLCT lower-semicontinuity for D1 (a) — LIGHT (from the rlctAt def), not a heavy primitive (pp-hall, 2026-06-22, #60)

**The P1 design (controller-directed, keying = ⨅-over-optimalSet, D1 (a) load-bearing).** Major
simplification of g160's "heavy analytic primitive" verdict: the controller's hint — `rlctAt` is the
team's OWN `sSup`-of-admissible-down-set def, semicontinuity may follow from THAT, not absent Mathlib
analysis — is CONFIRMED. **P1 (the core D1) is LIGHT.** Pins the exact statement + what it needs (small,
from the def); crux2 assesses the Lean from `rlctAt`/`weightedThreshold`.

## The `rlctAt` structure (the whole point)
`rlctAt(F, p) = sSup A(p)`, `A(p) = { c' ≥ 0 : ∃ U ∈ 𝓝 p, IntegrableOn |F|^{-c'} U volume }`
(`Rlct.lean:71`). The supremum of the **admissible-exponent set**, with admissibility existential over
NEIGHBOURHOODS of `p`. This `∃ U ∈ 𝓝 p` structure is exactly what makes the semicontinuity elementary.

## P1 (the CORE D1, B=0, homogeneous) — LIGHT, provable from the def
On the `B = 0` core `F = ‖∏C‖²` (homogeneous of degree `2L`), deepest = origin `0`. For any fibre point
`v` (of the core, `∏(v) = 0`):

    rlctAt(F, 0)  ≤  rlctAt(F, v).

**Proof (two ingredients, both light):**
- **(L1-a) SCALING-INVARIANCE** `rlctAt(F, s·v) = rlctAt(F, v)` for `s ∈ (0,1]` (homogeneity: the c-o-v
  `w = s·w'` + the `s^{2L}` unit; `rlctAtOn_comp_homeomorph` + `rlctAtOn_unit_invariant_aux`, banked).
  Verified exact (g162). The local rlct is CONSTANT along the scaling ray `s·v`.
- **(P1-core) NBHD-MONOTONICITY of `rlctAt`** (NEW but LIGHT, ~10 lines from the def): for `c' ∈ A(0)`,
  pick `U₀ ∈ 𝓝 0` (WLOG open) with `IntegrableOn |F|^{-c'} U₀`. Since `s·v → 0` (`s→0⁺`), for small `s`
  the point `s·v ∈ U₀`; `U₀` open ⟹ `U₀ ∈ 𝓝 (s·v)` ⟹ `c' ∈ A(s·v)` ⟹ `c' ≤ rlctAt(s·v) = rlctAt(v)`
  (by L1-a). `sSup` over `c' ∈ A(0)`: `rlctAt(0) = sSup A(0) ≤ rlctAt(v)`.

**The mechanism (the controller's hint, confirmed):** `A(0) ∋ c'` ⟹ the admissible nbhd `U₀ ∈ 𝓝 0`
also lies in `𝓝(s·v)` for `s` small (`s·v` enters `U₀`), so `c' ∈ A(s·v)`. This is the
**nbhd-monotonicity of `rlctAt`** — immediate from the `∃ U ∈ 𝓝` existential — combined with the ray
collapsing to the deepest. **NO Fatou, NO Varchenko nondegeneracy, NO general lct-semicontinuity
theorem, NO absent Mathlib analysis.** Airtight (g168): the five steps (`s·v ∈ U₀` from `U₀ ⊇` a ball;
`U₀ ∈ 𝓝(s·v)` from openness; `c' ∈ A(s·v)` from the integral; L1-a; `sSup_le`) are all elementary.

## Why g160 OVERESTIMATED P1 (the correction)
g160 routed P1 via "general RLCT lower-semicontinuity (Watanabe/Varchenko)" — a heavy unbanked analytic
primitive. **That was an overestimate.** We do NOT need general semicontinuity in the basepoint; we need
it ONLY along the scaling ray `s·v → 0`, where the `∃ U ∈ 𝓝` structure of `rlctAt` gives it directly
(the admissible nbhd of `0` swallows the nearby ray points). The honest weight: a ~10-line lemma from the
team's own def + the banked L1-a. **P1 is LIGHT.**

## The FULL-B D1 (a) scope — the one wrapper (for the controller/crux2)
`rlctAt_deepest_le_of_optimal` (`Skeleton.lean:973`) is on the **full** `dlnLoss H B` (`B ≠ 0`, NOT
homogeneous — the `−B` breaks scaling; the docstring flags this "L2-downstream"). So the light P1 (core,
`B=0`) does NOT directly prove the full-B statement. The bridge:
- **L2 at every fibre point:** `rlctAt(dlnLoss H B)(p) = n_p/2 + rlctAt(core)(p-core)` (`product_reduction`'s
  per-point form). The regular shift `n_p/2 = r(H_0+H_L−r)/2` depends only on `r = rank B` (CONSTANT on
  optimalSet — every fibre point has product rank `r`), so `n_v = n_{deepest}`. ⟹ full-B D1 (a) reduces
  to the **CORE D1** `rlctAt(core)(0) ≤ rlctAt(core)(v-core)` = the light P1 (B=0, homogeneous). ✓
- **The cost:** L2-at-every-v needs L2's reduction at a GENERAL (possibly non-rank-exact) `v` — the
  broader-split / non-rank-exact charting crux2 flagged. That is the L2-downstream wrapper, NOT P1.

**Two routes for D1 (a), for the spine to pick:**
1. **Core-level D1 (cleanest):** if the spine can apply D1 at the CORE level (post-L2, `B=0`), then P1
   (light) suffices — `rlctAt(core)(0) ≤ rlctAt(core)(v-core)`, the homogeneous core, via the
   nbhd-monotonicity + L1-a. NO non-rank-exact wrapper. **Recommended if the assembly allows it.**
2. **Full-B D1 (a) directly:** P1 (the core D1) + L2-at-every-fibre-point (the regular shift constant) +
   the per-`v` core reduction (the non-rank-exact L2 charting). Heavier — the wrapper is the
   L2-at-every-v, NOT P1.

## crux2's tractability read (the fork the controller surfaces to the operator)
- **P1 (the core D1, B=0):** `rlctAt(core)(0) ≤ rlctAt(core)(v-core)` via (i) the nbhd-monotonicity lemma
  (NEW, ~10 lines from `rlctAt`'s `sSup`/`∃U∈𝓝` def — `sSup_le` + `IsOpen.mem_nhds` + `mono_set` of the
  integral) + (ii) L1-a (banked `comp_homeomorph` + `unit_invariant`). **GREEN tractability expected** —
  small, from the team's own def, no new analytic import. This is NOT the heavy primitive g160 feared.
- **The full-B wrapper (L2-at-every-v):** the genuine remaining weight, and it's L2's per-point reduction
  at non-rank-exact `v` (crux2's broader-split). crux2's `product_reduction` is at the deepest; extending
  it to a general fibre point is the wrapper to assess.

So the operator note (crisp fork): **NO second citation needed (the only-S2 policy holds).** P1 (the core
semicontinuity) is LIGHT (from the rlctAt def). The remaining weight is the L2-at-every-fibre-point lift
(IF D1 must be full-B) — and that is reused L2 machinery, not a new analytic primitive. If D1 can be
core-level, even that vanishes. **D1 (a) is NOT gated on a heavy new primitive** — g160's "heavy P1"
was the overestimate; the controller's rlctAt-def hint dissolves it.

## Most likely thing to break this
The nbhd-monotonicity (P1-core) needs `s·v ∈ U₀` for small `s` — i.e. `s·v → 0` (true: `‖s·v‖ = s‖v‖ → 0`)
and `U₀` a genuine nbhd of `0` (true by def). The one care: `rlctAt`'s `U ∈ 𝓝` is a nbhd (not nec. open);
WLOG shrink to its open interior (integrability inherited by `IntegrableOn.mono_set`), then
`s·v ∈ interior ⟹ U₀ ∈ 𝓝(s·v)`. Elementary. The genuine residual is the full-B wrapper (L2-at-every-v),
not P1. If the spine pins D1 core-level, P1 is the whole story and it's light.

## Decorrelation
pp-hall exact algebra + def-reading (g166 the structure, g167 the adversarial "structural route doesn't
close" + the elementary semicontinuity, g168 the airtight 5-step + the exact lemma, g169 the full-B
scope). This CORRECTS g160's "heavy primitive" overestimate (the controller's rlctAt-def hint was the
key). A Codex pass on the nbhd-monotonicity-from-the-def is optional (the argument is elementary and
self-checked); the previous D1 Codex consult didn't land (CLI flaky). Builds on g160 (the prove-or-surface
landscape, now refined), g162 (L1-a scaling-invariance), `Rlct.lean:71` (the `rlctAt` def),
`rlctAt_deepest_le_of_optimal` (`Skeleton.lean:973`), `product_reduction` (the L2 per-point reduction).
