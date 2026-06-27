# R1 chart-existence FIDELITY: does the faithful datum need `χ 0 = 0` and `u ≠ 0` near 0? (pp-hall, 2026-06-22, #130)

**Extension to #129 (the chart-existence form).** crux2 surfaced that the locked `IsSchurStraighten`
(`GeneralR1Recursion.lean:84`) does **not** require `χ 0 = 0` (so the rlct transport's base point is not
pinned to the deepest point) nor `u` nonvanishing (it carries only `umeas : Measurable u`). Sound for the
packaging lemma `schur_straighten_exists`, but does the **faithful** chart-existence datum — the one the
cover's RLCT transport consumes — NEED (i) `χ 0 = 0` and (ii) `u ≠ 0` near 0?

## VERDICT: YES to BOTH. Both are required for downstream RLCT-transport soundness, and both are currently MISSING from the locked datum. Fix the chart-existence statement once by adding them as fields.

This is read straight off the two transport lemmas the recursion step calls; no new math, exact lemma
tracing (`g129-scripts/g130_fidelity_check.py`). The #129 squeeze verdict makes both pins **more** acute,
not less.

## (i) `χ 0 = 0` — REQUIRED (the chart must fix the deepest point)

The consumer `schur_recursion_step_sound` (`GeneralR1Recursion.lean:228`) concludes
`rlctAtOn (dlnLoss M 0) (chart (0,0)) = nReg/2 + rlctAtOn (G²) 0`. The base point of the transported
RLCT is **`chart (0,0)`**, forced by `rlctAtOn_comp_homeomorph` (`S1Fubini.lean:54`):

    rlctAtOn (fun w => F (e w)) w0 = rlctAtOn F (e w0)          -- w0 = (0,0) ⟹ base point = chart (0,0)

The entire RLCT programme is anchored at the **deepest point** `w* = deepestPoint H r B` — the singular
zero of the loss; L2 (`deepest_point_reduction`), D1, and R1 all compute `rlctAt … w*`, and the L2
docstring (`Skeleton.lean:948`) states plainly: *"the local RLCT varies over the fibre, equalling the
closed form at the deepest point."* For the recursion step's output to be the rlct **at the deepest
point**, we need `chart (0,0) = w*`. In the flat post-blow-up per-node coordinates the deepest point is
the origin, so the obligation is exactly:

    χ (0,0) = 0   (= the flat deepest point)

**Without it:** `chart (0,0)` is some other point of the fibre; `rlctAtOn (dlnLoss M 0) (chart (0,0))` is
a sound equation about the **wrong point**. Because the local RLCT genuinely varies over the fibre, that
value is in general **not** the Aoyagi `λ`, and the cover — which must chain rlct **at the deepest
point** across nodes — cannot use it. So `χ 0 = 0` is load-bearing for the transport to land on the
deepest point.

## (ii) `u ≠ 0` near 0 — REQUIRED (the factor must be a genuine unit, not merely measurable)

The unit-strip `rlctAtOn_unit_invariant_aux` (`S1Local.lean:139`) demands

    ∃ U ∈ 𝓝 wstar, ∀ w ∈ U, a ≤ |u w| ∧ |u w| ≤ b,   with a > 0

and its proof uses `|u|^{−c'} ≤ a^{−c'}` (forward, **needs `a > 0`**: bounded **away from 0**) and
`|u|^{c'} ≤ b^{c'}` (backward, needs `b < ∞`) inside `Integrable.bdd_mul`. If `u` is not bounded below by
some `a > 0` near the base point (`u(0) = 0`, or `u → 0` in every neighbourhood), `a^{−c'}` is vacuous
and the strip is **false** — a factor that vanishes is a genuine zero of the integrand and *changes* the
RLCT (it is not a unit). `schur_recursion_step_sound` accordingly takes the explicit `hu` bounded-unit
hypothesis (`a ≤ |u| ≤ b`, `a > 0`), **not** mere `Measurable u`.

**The gap:** `IsSchurStraighten`/`schur_straighten_exists` carry only `umeas : Measurable u`.
Measurability does **not** prevent `u(0) = 0` or `u → 0`. So the locked datum **cannot discharge `hu`** —
exactly crux2's finding. The faithful datum must record the local bound `∃ U ∈ 𝓝 0, ∀ w ∈ U, a ≤ |u w| ∧
|u w| ≤ b` with `a > 0` (equivalently: `u` germ-nonvanishing + locally bounded near 0).

## The wiring gap, named precisely

`schur_recursion_step_sound` does **not** consume an `IsSchurStraighten`; it takes the stronger
hypotheses (`hu`, and a conclusion at `chart (0,0)`) **freshly**. When the cover wires the locked datum
into the transport, the datum (`Measurable u`, no `χ 0 = 0`) is **strictly weaker** than the consumer's
ask (`a ≤ |u| ≤ b`, `a > 0`; `chart (0,0) = w*`). So the two are not currently composable for a sound
deepest-point chain — the gap is real, not cosmetic.

## The corrected chart-existence statement (add THREE fields, fix once)

`IsSchurStraighten` should additionally require (names indicative):

1. `chart_fixes_deepest : χ 0 = 0` — the chart maps the source origin to the flat deepest point. Pins the
   transport's base point `chart (0,0)` to `w* = 0`. (Field (i).)
2. `unit_bddBelow : ∃ U ∈ 𝓝 0, ∃ a > 0, ∀ w ∈ U, a ≤ |u w|` — `u` bounded away from 0 near the deepest
   point (genuine unit, lower half). (Field (ii), the load-bearing half.)
3. `unit_bddAbove : ∃ U ∈ 𝓝 0, ∃ b, ∀ w ∈ U, |u w| ≤ b` — `u` locally bounded above. (Field (ii), upper
   half; can be merged with 2 into one `a ≤ |u| ≤ b` field matching `hu`'s shape exactly.)

With these three the datum **exactly** supplies `schur_recursion_step_sound`'s `hu` and the
`chart (0,0) = w*` anchoring; `redCore_eq` + `factor` already supply the germ. `measure_drops` stays
derivable. Nothing else changes — the `IsSchurStraighten` STRUCTURE is otherwise sound (this is the same
"re-attach the ties the geometric application supplies" move the O1/O2/O3 SPECIFY correction already
made; these three are the two further ties the **transport** needs that the SPECIFY correction did not
add because it audited the packaging, not the transport consumer).

## Cross-check with #129 (the squeeze verdict) — both pins survive and tighten

#129 retired the clean single-unit form in favour of the **squeeze** `c₁·Φ ≤ F ≤ c₂·Φ`. The squeeze
packaging makes both pins natural and **automatically satisfiable**:
- **(ii):** in the squeeze, the unit role is played by the positive constants `c₁, c₂` (`a = c₁ > 0`,
  `b = c₂`). These are **bounded away from 0 by construction** — so if the corrected datum records the
  squeeze constants `[c₁, c₂]` (`c₁ > 0`) rather than an abstract `Measurable u`, field (ii) is met for
  free. (If the datum keeps abstract `u` with only `Measurable u`, (ii) is **unmet** — confirming the
  fix.) The unit-strip in the squeeze route is applied to the **constant** `c₁⁻¹`/`c₂` multiples (genuine
  units, `rlctAtOn_unit_invariant_aux` with `a = b = c`), which trivially satisfy the bound.
- **(i):** the squeeze compares `F` and `Φ` **at the same point** near the deepest point (no change of
  variables; #129). That point must **be** the deepest point — i.e. the comparison/chart is anchored at
  `χ 0 = w* = 0`. So `χ 0 = 0` is needed identically in the squeeze route.

So the corrected chart-existence datum that #129 + #130 jointly specify is: a comparison anchored at the
deepest point (`χ 0 = 0`, field (i)), with the squeeze inequality `c₁·Φ ≤ flatCore ≤ c₂·Φ` (`c₁ > 0`,
field (ii) — the genuine-unit constants), `Φ = (nReg unit-coeff regular squares) + dlnLoss S.red 0 (…)`,
resting on the structural fact `flatCore − Φ ∈ ideal(E)`. NOT the abstract `u`-factor with only
`Measurable u`, and NOT `rlctAtOn_comp_homeomorph`/MP-transvection alone.

## Most likely thing to break this
If the geometric construction's `u`/squeeze-constants happen to satisfy `u(0) ≠ 0` and `χ 0 = 0`
*incidentally* (which #127's blow-up→hard-pivot interface does arrange: the post-blow-up pivot is a HARD
1, so the leading unit is `≈ 1 ≠ 0` at the origin, and the chart is built around the origin), then the
**packaging** lemma is still sound and the **construction** still works — the gap is purely that the
locked *datum interface* doesn't *record* these facts, so the cover can't *invoke* them. The fix is to
promote the incidental truths to recorded fields. The risk is a future construction (a different node)
where `u(0) = 0` slips through `Measurable u` undetected; the fields close that.

## Next step to settle the open part
Hand the formaliser the three-field amendment to `IsSchurStraighten` (and the matching `hu`/`χ 0 = 0`
hypotheses already present in `schur_recursion_step_sound`, so the wiring becomes a direct field-feed).
Controller's call on whether to fold this into the locked structure now or stage it as the corrected
chart-existence statement. Decorrelation: this is a single-model (pp) lemma-signature trace; the Codex
leg is the same one unavailable in #129 (prompt at `g129-scripts/codex-prompt-UNAVAILABLE.md`) — re-run
when the CLI is reachable to decorrelate the "both pins required" reading.

Builds on #129 (squeeze verdict), the locked `IsSchurStraighten` (`GeneralR1Recursion.lean`), and the
transport lemmas `rlctAtOn_comp_homeomorph` (`S1Fubini.lean:54`) + `rlctAtOn_unit_invariant_aux`
(`S1Local.lean:139`). Script: `g129-scripts/g130_fidelity_check.py`.
