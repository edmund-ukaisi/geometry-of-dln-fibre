# R1 cover-producer lane (fm3/routem-ga-transport) — state at the L=2-anchoring scope wall

**As of 2026-06-23.** Paused for an operator scope call (general-L via explicit cover is L=2-only;
general-L needs the iterated rank-profile resolution). This note records what is banked, what is sound,
and what the scope decision turns on — so the lane resumes cleanly.

## The arc (findings that redirected the lane, in order)

1. **φ₁ not surjective** — the cert-104b §4 single-chart transport route is UNSOUND
   (`weightedThreshold_transport_aux` needs `Function.Surjective`; the single-pivot blow-up misses the
   positive-measure `{A₀₀=0, A≠0}` stratum). Sound route = the argmax/pivot COVER. (Decorrelated Codex.)
2. **Point vs box** — the per-chart object is a threshold over the exceptional DIVISOR (full ratio box),
   not the point; the point-lemma `weightedProductMin_mono1D_of_ne` is the wrong granularity. Built the
   box-form (`S1BoxProductMin`).
3. **Full-ratio-box wall** — the cover needs `core` integrable over the full ratio box, not the point
   RLCT (the active-rest ratios range over `[−1,1]`, not near 0).
4. **g156 verdict** — headline comparability-free (cover recurses on the genuine child via single-step
   Schur, never `∏S_s`). The interface is box-threaded (full-box integrability descends to the child's
   box), VALUE is the clean point-min.
5. **Glue (a)** — `core` (non-homogeneous, pivot=1) lifts to the child raw loss via the box-uniform
   `schur_node_squeeze` + the det-1 `ReducedTransport` reindex; #11 (`BoxThresholdBridge`) then serves
   the CHILD raw homogeneous loss per node.
6. **L=2-anchoring wall (the current pause)** — the inner `rlctAtOn core 0 = n/2 + R/2` Morse split
   (`n = M^{L+1}` Erow squares) is **L=2-only**. For L≥3 the Erow directions are degree-(L−1) forms (not
   Morse), the Erow-Morse count is 0, V8 overshoots (witness `(3,3,3,3)`), and no node-local `n_raw`
   repairs it. The cover is intrinsically an L=2 reduction. (Pen-and-paper, sympy-exact, Codex,
   `(3,3,3,3)` vs `Lambda.lean`; cobuild's independent `n=M(last)` refutation matches.)

## Banked Lean (all axiom-clean: `propext`/`Classical.choice`/`Quot.sound`)

SOUND GENERAL bedrock (reusable regardless of the scope call):
- `S1WeightedProductMin.lean` — `weightedProductMin_mono1D_of_ne` (point product-min; the per-chart value).
- `S1BoxProductMin.lean` — `boxpm_integrableOn_of_lt` (box-form per-chart integrability feed).
- `S1NodeBlowup.lean` — `dlnLoss_nodeBlowup_factor` (F∘φ = y₀²·core), `flatIdx_layer0_card` (mk−1 Jac power).
- `S1NodeFlatHomog.lean` — `flatNodeLoss_pivot_factor` (flat chart identity via layer-0 homogeneity),
  `symm_scaleActive_layer0`, `layer0Coords`. The value-level reduction is general-L-shaped.
- `S1NodeCoverGE.lean` — `node_cover_threshold_lt_top` (cover GE assembly), `chart_pullback_lt_top_of_boxpm`.
- `S1NodeCoverBridge.lean` — `BoxThresholdBridge` (box-threaded interface predicate), `chart_pullback_lt_top_of_bridge`.
- `S1BoxSqueeze.lean` — `box_integrableOn_of_squeeze` (box-level squeeze integrability transfer — GENERAL).
- `S1BoxAdditive.lean` — `boxAdditive_integrableOn` (n-D additive-block box integrability — GENERAL).

L=2-ANCHORED (do NOT wire as general-L): composing the above via the **∑Erow² Morse block** (the inner
`core ≍ ∑Erow² + child` split, `schur_node_squeeze` / `smoothBlockSplitForm` / `boxAdditive` applied to
the Erow directions). The two integrability lemmas (`box_integrableOn_of_squeeze`, `boxAdditive_integrableOn`)
are sound abstract facts; their APPLICATION to the Erow-Morse split is L=2-only.

## What the scope decision turns on

- **If L=2 is the anchored scope** (with (2,2,2)/`Case222` the instance, general-L deferred): the
  existing `schur_recursion_step_squeeze` + `Case222NodeDescent` are ALREADY on the Morse split, so this
  is the de-facto scope of the whole binding spine. The lane completes the L=2 instance.
- **If general-L is required**: the inner `core → child` step needs the iterated rank-profile resolution
  (per-stratum `½·mval`, the LR/Aoyagi resolution), NOT a single layer-0 Morse peel — a genuine re-scope.
  The pen-and-paper flagged honestly computing `(2,2,2,2)`/`(3,3,3,3)` RLCT as the next step to confirm
  whether the value-level g156 recursion (child = real reduced loss) still reproduces `½·minAdm` for L≥3.

## What SURVIVES general-L (independent of the call)

- The outer product-min `rlctAtOn(dlnLoss M 0) 0 = min{mk/2, rlctAtOn core 0}` (boxpm/cover-min).
- The value-level reduction of `core` to the genuine `dlnLoss(schurStateRed M)` (via `ReducedTransport`).
- The two general box-integrability lemmas (squeeze transfer, additive block).
- The chart identity `flatNodeLoss_pivot_factor` (via homogeneity, all L).

## Definitions pinned (for cobuild's `hmin`/`minAdmZ`)

`mk = M 0 · M 1`; `n_raw = M(Fin.last L)` **for L=2 only** (= 0 Morse directions for L≥3);
`child = schurStateRed M`. V4 `min{mk, n + minAdm(child)} = minAdm(M)` holds for L=2 (512/512), fails L≥3.
