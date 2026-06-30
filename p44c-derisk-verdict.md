# VERIFY-FIRST DE-RISK — #44c `deepest_gauge_squeeze_exists` buildability

**VERDICT: WALL via the comparability route — do NOT sink the build. Prior art (machine-verified
counterexample + a controller shelving adjudication) already establishes the load-bearing core
identity is FALSE-AS-STATED.** This is not a fresh research wall I'm discovering; it's a banked,
adjudicated wall the commission premise ("route-first, not a fresh wall") contradicts. Surface, don't
drive.

## What #44c rests on (the load-bearing field)

`deepest_gauge_squeeze_exists` constructs a `DeepestGaugeChart`, whose load-bearing field is
`loss_squeeze` — an RLCT two-sided bound whose genuine content (docstring, #61/g156) is the
**core-comparability** `‖∏(T_s − Z_s(I+X_s)⁻¹Y_s)‖² ≍ dlnLoss M 0 (core)` (the additive Schur core,
after the multiplicative `T·(I−VY)⁻¹` form was already REFUTED). Equivalently (PIN2 card part-4):
the link `∑‖R‖² ≍ deepestCoreF(coreAbsorb…)`, `R = P11 − P10·⅟P00·P01` the full-product Schur core.

## The banked WALL evidence (`dgc-sub34` branch, controller-adjudicated 2026-06-23)

`expeditions/.../14-r1-design/pin2-loss-squeeze-statement-card.md` (commit 71539525) records:
- **Part-4 `‖R‖² ↔ ‖∏S_s‖²` is FALSE-AS-STATED, HALTED.** Machine counterexample (sympy):
  `L=2, r=1, reddim=2`: `E=0` but `∏S_s=0` while `R=−ε⁴≠0`. So the two cores do NOT agree even up to
  RLCT in general.
- The fix needs a **non-cancellation hypothesis (NC)** `∏‖S_s‖ ≤ κ‖∏S_s‖`, which auto-discharges
  **only in the scalar-reduced-core case** (`reddim`-1 layers) — NOT general `M`. (Banked:
  `codex/g156-leakage-answer.md`.)
- **The whole L2 `deepest_loss_squeeze` / `core_comparability` / `DeepestGaugeChart` comparability
  chain was SHELVED as REDUNDANT** (controller adjudication): the headline `aoyagi = ½·minAdm` is sound
  via the **comparability-free R1 COVER route** (recurses on the genuine child loss, no `∏S`
  comparability). `git grep` confirmed `DeepestGaugeChart` is consumed by nothing on the headline path.

So the comparability that `deepest_gauge_squeeze_exists` needs is the SAME object that (a) walled on a
machine-verified counterexample and (b) was deprecated off the headline path a week ago.

## Reconciliation: #44 IS critical-path, but #44c (this route) is NOT the way to it

- **#44 (`deepest_regular_core_normal_form`) genuinely matters** — it's one of the 5 Skeleton headline
  rungs (`AxCheck`: "L2 normal-form"), wired by `DeepestNormalFormWiring.deepest_normal_form_of_value`.
  The team-lead is right that closing it cascades.
- **But the CURRENT canonical decomposition already routes around the comparability:** #44 =
  `deepest_regular_core_reduces` (value-free reduction) ▸ `hRValue` (R1 value). The value-free reduction's
  heavy gate is `deepest_gauge_squeeze_exists` — which, per the field, still rests on the walled
  comparability. So **driving `deepest_gauge_squeeze_exists` via `core_comparability_squeeze` re-opens the
  shelved, false-in-general identity.** That is the WALL.

## Recommendation (the route that is NOT walled)

Do NOT drive `deepest_gauge_squeeze_exists` via the gauge core-comparability. Two non-walled options for
the controller:
1. **Confirm whether #44 even needs `deepest_gauge_squeeze_exists`** given the comparability-free R1
   COVER route that the controller already adjudicated SOUND for the headline. If the cover route
   discharges the L2 headline rung directly (as the PIN2 shelving says), #44c is redundant and the right
   move is to wire #44 through the cover, not the gauge squeeze. (This is the same "the headline doesn't
   need this chain" finding, now resurfacing at #44c.)
2. If #44 specifically (the deepest-point closed form, not just the headline) IS required and must go
   through a gauge chart, then the buildable restriction is the **scalar-reduced-core / NC-discharged
   case** only — general `M` needs the NC hypothesis which is false-in-general. That is a scoped, weaker
   theorem, not the stated #44c.

NET: the commission's "route-first, not a fresh wall" is contradicted by banked prior art. The
load-bearing comparability is machine-falsified in general and the chain was shelved as off-headline.
Surfacing for the controller's call BEFORE any build — exactly the verify-first gate firing RED.

Artefacts: PIN2 card (`dgc-sub34` @71539525), `codex/g156-leakage-answer.md` (the NC analysis + the
sympy counterexample). No fresh Codex consult needed — the prior adjudication is decisive.
