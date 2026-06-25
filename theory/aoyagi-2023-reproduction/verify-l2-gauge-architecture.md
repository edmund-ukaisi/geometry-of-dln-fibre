# L2 gauge-chart architecture — the L=1 decision + the unblock sequence

**Controller decision, 2026-06-24.** The `l2-gauge-close` tide surfaced a real architectural blocker
(it closed none, faked nothing). This records the decision and the unblock order.

## The L2 gate

`product_reduction` (Skeleton:1141) is ALREADY PROVEN (no sorry): it rewrites via
`deepest_regular_core_normal_form` + `reg_shift_add_core_eq_aoyagiLambda` (arithmetic). So the L2
gate's real content is:

`deepest_regular_core_normal_form` (Skeleton:1124, `hL : 1 ≤ L`, ONE sorry):

    rlctAt H (dlnLoss H B) (deepestPoint H r B …)
      = (r·(H 0 + H_last − r) : ℕ)/2  +  ENNReal.ofReal (lambdaCore (fun s => H s − r))

i.e. `regular-block/2 + core`. For `2 ≤ L` this is filled by `deepest_regular_core_normal_form_of`
(DeepestGaugeConstruction:894) — the gauge-chart route.

## The blocker (l2-gauge-close finding)

All four GaugeConstruction sorries (831/832 `Qf(firstLayer)=1`/`Pf(lastLayer)=1`; 443 PIN1; 624 PIN2)
share ONE keystone — **boundary frame triviality** — and it is FALSE at `L=1`: there `firstLayer =
lastLayer`, the single layer is an arbitrary rank-r matrix (no boundary-inner vanishing), so
`Qf(first)=1 ∧ Pf(last)=1` cannot both hold. Also `deepestFrameFamily` (the comment's intended
producer of the trivial boundary frames) does not exist yet, and `deepestPoint_frame` is a
`Classical.choose` of a generic rank-normal-form (no boundary guarantee).

## The decision: gauge chart is a `2 ≤ L` construction; `L=1` is the smooth base

The gauge chart STRAIGHTENS a product of ≥2 matrices. At `L=1` there is no product — `prod H A = A`
(single matrix), the loss is the shifted quadratic `‖A − B‖²`. So `L=1` is naturally the base case,
and the chart is inherently `2 ≤ L`. **This matches the existing architecture:** `IsDeepLayers`
(Skeleton:513) already guards its boundary-inner-vanishing clauses by `2 ≤ L` (vacuous at `L=1`,
comment 956–958), and `prod_wLayers_ge2` (854) is already `2 ≤ L`-specific. So the split exists; the
gauge chart must respect it.

**Case-split `deepest_regular_core_normal_form`:**
- **`L = 1` (base, DIRECT — no gauge chart).** `prod H A = A`; the rank-r normal form of `B` (the Core
  one-sided normal-form lemma, building) splits `A` near the deepest point into the regular
  `r·(H0+H1−r)` Morse block + the `(H0−r)·(H1−r)` core block, both pure sums of squares. So
  `rlctAt = r·(H0+H1−r)/2 + (H0−r)(H1−r)/2`, and `lambdaCore (H0−r, H1−r) = (H0−r)(H1−r)/2` at `L=1`
  (the single-layer core is itself a smooth block). A genuine smooth-Morse computation (NOT vacuous,
  NOT skipped) via `smoothBlockND_rlct` + the rank normal form.
- **`2 ≤ L` (the gauge chart).** `deepest_regular_core_normal_form_of` — restrict the whole gauge-chart
  chain (`deepest_gauge_construction` → `deepest_gauge_squeeze_exists` → `deepest_squeeze_transport` →
  `deepest_regular_core_normal_form_of`) to `2 ≤ L`. The boundary-frame-triviality then holds (distinct
  `firstLayer ≠ lastLayer`), matching `IsDeepLayers`.

## The unblock sequence (the next L2 work, in order)

1. **Core one-sided full-column-rank normal-form lemma** — `A.rank = r ∧ tail-cols-zero ⟹ ∃ P unit,
   P·A = corM` (+ dual via `Matrix.rank_transpose`). Reusable bedrock; needed by BOTH the `L=1` base
   and the `2≤L` boundary frames. **BUILDING** (`l2-gauge-chart-work` tide).
2. **Refine `deepestPoint_frame_exists`** (Codex design A) to guarantee the boundary identities for
   `2 ≤ L`, using the Core lemma. Keeps downstream referencing `deepestPoint_frame` with the extra
   property (avoids re-stating 624 / `deepest_loss_squeeze`'s `hregval`).
3. **Restrict the gauge-chart chain to `2 ≤ L`**; then fill in turn: **831/832** (boundary triviality
   from the refined frame) → **624** (PIN2; `endpoint_telescoping`'s `hinterface` now available —
   round-trip `framedParams = P·paramsSymm·Q` + `reindex(P0·B·QL)=fromBlocks` + `core_comparability_squeeze`)
   → **443** (PIN1; consumes `hQf0`/`hPfL`; the banked `_through_first` + missing `_through_last`
   analogue + collapse→fderiv assembly).
4. **Add the `L=1` base case** to `deepest_regular_core_normal_form` (direct smooth proof, step's
   own math above).
5. **Wire**: `deepest_gauge_squeeze_exists`'s GaugeChart:365 sorry ← `deepest_gauge_chart_construct`;
   then `deepest_regular_core_normal_form` closes → `product_reduction` (already proven modulo it) →
   the L2 gate falls. Add the Deepest* family to the aggregator at this point (currently deferred).

## Soundness notes (binding)
- The `L=1` base is a genuine smooth-Morse computation, NOT a vacuous skip — it must PROVE the formula
  at `L=1` (rank normal form + sum-of-squares RLCT), not assume it.
- The `2 ≤ L` boundary-frame-triviality is sound (distinct boundary layers), mirroring `IsDeepLayers`.
- ONE citation (S2 `monomial_rlct`) only; the smooth-block RLCT (`smoothBlockND_rlct`) is on our side.
- Do NOT regress any #120 frame-sandwich statement to the false `= id`.
