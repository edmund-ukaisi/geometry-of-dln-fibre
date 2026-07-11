# priorities.md — Aoyagi-Full taste ledger

Controller proposes (VOI × directed-suspicion); operator edits directly (highest-authority signal).
Nothing unranked; "unclear-but-keep-going" is first-class. **Refreshed 2026-07-11 (pm) — STAGE 2 (A)-BUILD;
(□)-core NATIVE sjGoodMap route (inner slice BANKED); remaining = the outer tail + (S,J) L-recursion.**
Live integrative read: `synthesis.md` (UPDATE-883 newest); operator-review items: `discuss-at-close.md` (#97–#100).

## ★ STATE ANCHOR — Stage 1 COMPLETE (S2-free), Stage 2 = BUILD-discharge `(□)` via native (S,J)
Stage 1 delivered the fully-general Aoyagi learning coefficient (honest Lean 4 + Mathlib, BEDROCK-OK,
clean-three, **zero axiom declarations**), on `expedition/aoyagi-full` (draft PR #26 → dev):
`aoyagi_learning_coefficient_gen` (general L≥2, conditional on `(□) = RouteMBoxThresholdFinite (H−r)`
ALONE) + the UNCONDITIONAL `_gen_le` / `aoyagi_deepest_reduction_gen` / `_L2`. **Stage 2 discharges
`(□)`** → `_gen` unconditional → the (KEPT) unsuffixed `aoyagi_learning_coefficient` re-points to the
honest fully-general result. **OPERATOR (A) DECISION (#97, 2026-07-10, BINDING): BUILD the (S,J) atom
from scratch, do NOT cite. Route-search around the (S,J)/determinantal core is CLOSED** (cornrev
equivalence cert). LABOUR on established math (Aoyagi §5); the bar for "wall" is HIGH.

## Now (ranked)

1. **★ [STAGE 2 · ACTIVE GOAL] Discharge `(□)` = prove `DecoratedPeelStep` via the NATIVE (S,J) sjGoodMap route.**
   `(□)`-gate = `DecoratedPeelStep` (`RouteMSJDecoratedRec:78`, one unproven Prop; driver `→ (□)` AND `→`
   the obsolete `sjJointResolution:803`, sorry-free). **★ ROUTE PIVOT (UPDATE-883, charter-vindicating,
   VERIFIED vs live code):** the NATIVE sjGoodMap route WINS — the per-chart INNER slice is **ALREADY BANKED**
   at 7/2, det-inverse-free: `gammaPeelIntegral_sjGoodMap_eq` (RouteMSJGoodCoords:95) ∘
   `sjGoodChartLoss_endpoint_lt_top` (RouteMSJVExpose:74) ∘ `sjGoodMap_loss_matBox_lt_top`
   (RouteMSJGoodChart:269), all 0-sorry, via `corner_block_cube` (isotropic, dim a·b+t·h=7 → 7/2=½minAdm,
   codims-add). The `|det M|^{−4}` det-inverse of the casting route was a self-inflicted A₂-reparam artifact
   (charter: re-express natively → done). **ABANDONED (off critical path, banked/reusable):** the casting
   route — corner334 @96409822 (min→sum validated in Lean) + onePeel334 @a39a37e4 (clean-coords codim-rescue);
   also the earlier Route-V crux `twoBlock_radial_le` + `FrontSpectral`. Do NOT consume/rebuild these on the
   native path (BUT their anisotropic analysis may feed the outer-tail estimate — see the caveat).
   **★ THE REMAINING MOUNTAIN (native, det-inverse-free):** the **OUTER tail integration** (`σ_min(L_θ)^{−2c'}`
   on the good∪deeper cover) + the **(S,J) L-recursion** (the front `Ã₁`-rank descent = the T4 decorated
   double induction; A₂ rescued per-level per onepeel-tonelli). `chartInner_eq_outerShearFree` flags it.
   **★ CAVEAT (vsastruct prior, to adjudicate):** the crude coercive `∫ σ_min(L_θ)^{−2c'}` likely UNDERSHOOTS
   below 7/2 (worst-direction σ_min collapses the coupled corner to the 3/2-min caricature) → the **sharper
   ANISOTROPIC estimate** (the corank-recursion / `twoBlock_radial` per-singular-value structure — where the
   "off-path" crux/corank2 analysis becomes reusable) is probably the deeper-rung crux; banked-adjacent
   `RouteMSJProductTube` (LAYER-2 σ_min-integrability). **NOW:** mountain self-recon [ace21ecb] mapping
   banked-vs-new → re-engage vsastruct on the σ_min-coarseness (crude vs sharper) with the recon-map →
   commission the mountain formaliser on the native route. Then → `DecoratedPeelStep` proved → `(□)` ∀M →
   mint unsuffixed `aoyagi_learning_coefficient` (#108). Certs: `threads/genm-vsastruct/` (…, onepeel-tonelli,
   onepeel-tieback, onepeel-altroute); recon: `threads/genm-mountain-recon/`. Live read: synthesis UPDATE-883.
2. **[RESOLVED 2026-07-09] Peel-stack naming — KEEP the unsuffixed `aoyagi_learning_coefficient`.**
   Operator decision: keep it. It stays a sorried placeholder until Stage 2 discharges `(□)`, then it is
   re-pointed to the honest unconditional fully-general result. No action now.
3. **[OPERATOR-GATED] `dev` PR — DRAFT opened (#26).** Stage-1 milestone up for review; merge on operator
   decision (not before Stage 2 or whenever the operator chooses). Controller does not merge.
4. **[DEFERRED · roadmap] θ analytic-multiplicity seam.** `cards/theta-analytic-multiplicity-seam.md` +
   ROADMAP Bundle 4. Separate future direction; `λ` unaffected. NOT Stage 2.
5. **[NON-BLOCKING] stale-docstring residue.** Central retirement note (AxCheck:101) + prominent files
   swept; any remaining `[…, monomial_rlct]` per-result prose is minor polish (emitted `#print axioms`
   is ground truth).

## Watching (suspicion / risks)

- **★ SOUNDNESS WATCH-POINT (T4, the (□)-core) — the A₂-units-bounded-below RLCT-collapse.** The
  vslice-§5 corner resolution's load-bearing non-obvious brick is "the units `U₀,U₁ > 0` stay bounded
  below on the generic-A₂ chart" — this is what stops the DLN sum-form from RLCT-collapsing to the `min`
  caricature `z²(x²+y²)`. If the route-S build does NOT split the A₂-rank-drop off to the higher-Mval
  branch (lets A₂ degenerate inside cell₂), a subtle RLCT-collapse hides there — textbook conceptual
  slop (bedrock.md: technically-correct-but-subtly-wrong; the base is audited hardest). GATE route S's
  close on a decorrelated A₂-rank-drop-split check (re-engage vsastruct). (synthesis UPDATE-873.)
- **`(□)` climbability (Stage-2 crux).** Aoyagi §5 is established ⇒ labour, not a wall; the corank-2 rung
  is decorrelated-confirmed finite at 7/2 (3 ways). The deepest grind is closing `sjJointResolution` at
  the corner monomial (the geometric corner resolution — the GAP). A genuinely-new obstruction here (not
  labour) would be a real escalation — watched, not expected. Dead routes (do NOT revisit): the ∧²-
  compound tube (asymmetry, corank2-cert §4); the SEAM det-Jacobian (UPDATE-771); the front-peel
  shortcut (#93).
- **Tide reliability.** A background formaliser can idle-loop (burst→idle, no commit) — watch FROZEN
  worktree edits + no commits (not just idle pings); take over + drive directly rather than nudge.
- **Branch hygiene.** Controller stays in the MAIN checkout ON `expedition/aoyagi-full` (per operator
  2026-07-09); build via `scripts/lb` (never bare `lake`); PRs/dev-master operator-gated.
- **Cadence.** Fewer higher-signal ticks; honor the ≥20-min heartbeat; resist reflexive doc-churn.

## Operator notes

(empty — operator injects here)
