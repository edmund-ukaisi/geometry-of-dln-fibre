# priorities.md — Aoyagi-Full taste ledger

Controller proposes (VOI × directed-suspicion); operator edits directly (highest-authority signal).
Nothing unranked; "unclear-but-keep-going" is first-class. **Refreshed 2026-07-11 (late) — STAGE 2 (A)-BUILD;
(□) via the DECORATED (S,J) DESCENT (Route A, coupled diag(b) ledger). ★ The spine RE-POINTED (□) onto the new
sole contract `DecoratedDescent = ∃ adm, (trivial admissible) ∧ DecoratedStepHyp adm ∧ DecoratedBaseHyp adm`
(the plain-IH `DecoratedPeelStep` was UNPROVABLE/Q2 → marked dead; `routeMBoxThresholdFinite_of_decoratedDescent`
is the live driver, clean-three @b142a966). Q_D CERTIFIED no-obstruction (#142, both anchors, exact toric-ray);
the peel-closure invariant + the (i) incidence are NATIVE/α (`minAdm_eq_backPeel` re-expression — #97 HONORED,
NO cite; the last Proved-vs-Cited fork RESOLVED to Prove, #114). **6 clean-three modules banked** (spine +
measure bedrock RouteMSJInnerDescent + invariant-(ii) RouteMSJTransversality + (P)/(T)-guard RouteMSJAdmEncoding
+ Rayleigh core RouteMSJLeafRayleigh + leaf finiteness RouteMSJLeafFinite). DecoratedBaseHyp's LOSS part DONE by
proof (`corankLeaf_rpow_lt_top`, route A, bypasses sjLoss_terminal + (P)/(T)). **REMAINING:** the invariant α-build
(`minAdm_eq_backPeel` + chain → rank≥b) + adm def + wire corankLeaf into DecoratedBaseHyp [mostly landing] →
**`DecoratedStepHyp` — THE remaining substantial analytic core** (the decorated peel + the intersection COUPLED
estimate = deepest soundness; NOT a codim freebie per cover's x²(x²+y^{2N}) correction) → `DecoratedDescent` →
(□) → mint #108. BUILD-TO-THE-END; bounded labour, no wall. Decorrelated adversarial hunts caught 5 errors on
paper (atom-first / plain-hIH / decoration / full-rank / higher-codim-slack).**
Live integrative read: `synthesis.md` (UPDATE-931 newest); operator-review items: `discuss-at-close.md` (#97–#114).

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

1. **★ [STAGE 2 · ACTIVE GOAL] Discharge `(□)` via the DECORATED (S,J) DESCENT (Route A) — prove `DecoratedDescent`.**
   `(□)`-gate = `routeMBoxThresholdFinite_of_decoratedDescent : DecoratedDescent → ∀M (□)` (clean-three @b142a966,
   RouteMSJDecoratedRec). `DecoratedDescent = ∃ adm, (trivial admissible) ∧ DecoratedStepHyp adm ∧ DecoratedBaseHyp adm`
   (adm-abstract decorated recursion; the plain-IH `DecoratedPeelStep` is DEAD — Q2: peel emits `[reduced]·[H⁻⁴]`, plain
   IH can't carry it). Controller bedrock/vacuity review PASS (non-vacuous: ∀D→false base, trivial-only→unprovable step;
   forces the peel-closed p=0-transversality family). **ROUTE CONFIRMED (#140):** front-first g(Q)/qPeelIntegral is
   FAITHFULNESS-CONTESTED (shared-A₂, disjoint-A₂ FALSE); `#123`/Cauchy–Binet a TOOL not the closer.
   - **DONE / banked (clean-three):** the spine (`DecoratedDescent` + driver); measure bedrock `RouteMSJInnerDescent`;
     `DecoratedBaseHyp` LOSS part = `corankLeaf_rpow_lt_top` (route A, `RouteMSJLeafFinite`+`_Rayleigh`, `∫(frobSq ΓZ)^{−c'}<⊤`
     at ½minAdm(base) given the `Z·Zᵀ≽c·I` units interface); invariant-(ii) `RouteMSJTransversality`; (P)/(T)-guard +
     regression-test-2 `RouteMSJAdmEncoding`; **the A₂ α-unlock `RouteMSJBackPeel`** (`minAdm_eq_backPeel` re-expressed as
     the banked front-peel #117 + convexity ⟹ co-minimizing ρ≥b, @c90dcab5, cover PASS). Q_D CERTIFIED (#142); invariant
     width-general CERTIFIED (#144).
   - **★ adm-FORK RESOLVED → (B) valuation-predicate (UPDATE-936, cert §10/§10.1).** #144 peel-closes the VALUATION predicate
     (not just the reachable set), so #3 (adm def) DECOUPLES from #5 (peelOp). **FINAL #3 adm def:**
     `adm M D := genuineCarrier D ∧ (a=0 ∨ b=0 ∨ ∀η∈Crit D, ⨅_j ν_η(corankGen D j)=0)`, Crit incl. intersection rays (C1).
     `genuineCarrier D := D.Z = paramsBox(deeperChain M)` (pins the EXACT deeper chain — controller SPINE check: SJDecoration
     is NOT definitionally genuine, so this clause is LOAD-BEARING; an unpinned/free carrier gives the wrong rank-strata codim).
   - **NEXT (the build, genm-sj5-desc2):** (α native, #97 honored, NO cite) #2-core `corank_survival_ae` (AG-free: banked
     D1JointDiffRankExact factor → RankLocusClosed minor-cut → DeepestCoreNonvanishing null-set; free-A genericity, NOT
     component-decomposition) + the units bridge (full-row-rank ⟹ ∃c>0 `Z·Zᵀ≽c·I`) — **`RouteMSJCorankSurvival.lean`
     sorry-free but STAGED untracked, awaiting desc2 green report + green-gate + AxCheck (canonical-clean discipline)** →
     #3 (adm def (B), spec'd above) → #4 wire corankLeaf into `DecoratedBaseHyp` (jac via Tonelli). [Bounded, native.]
   - **★ THE REMAINING SUBSTANTIAL CORE = `DecoratedStepHyp` (the decorated peel):** the coupled corner blow-up (route-S
     §5 sectors, corrected residual `H₁⁻³(H₁+H₂)⁻¹`) → charges-ADD to `sjLoss_terminal`, closing on the reduced-chain IH at
     the ½peelCharge-shifted threshold. ★ SOUNDNESS: the intersection/deficient-rank rays' `≥½minAdm` must be ESTABLISHED
     by the QUANTITATIVE COUPLED estimate (NOT "higher codim ⟹ slack" — cover's x²(x²+y^{2N}) correction, #114); cover's
     deepest audit focus.
   **THEN:** `DecoratedDescent` proved → `(□)` ∀M → mint unsuffixed `aoyagi_learning_coefficient` (#108, on the FULL general
   (□) — precision guard). Certs: `threads/genm-sj5/` (descent-buildplan, route-reconcile, toric-ray-cert, transversality-recursion,
   cov-ledger-design, obligation1-spec); live read: synthesis UPDATE-931.
1b. **[banked-but-reusable, off critical path] det-monotone (`RouteMSJDetMono`, #112 rebuild, unwired);
   corank-Gram (`RouteMSJCorankGram`, one isolated sorry, untracked) = the det-Gram-weight TOOL usable INSIDE
   Route A (#140), not the closer.** Historical (superseded framings): the front-first g(Q)/qPeelIntegral route
   (faithfulness-contested #140 — shared-A₂) and the earlier front-first cover are BOTH superseded by the
   decorated (S,J) descent (item 1). Their banked spectral machinery (`twoBlock_radial_le`/`FrontSpectral`/
   `ProductTube`/RadialPolar) + the corank-q `qPeelIntegral_lt_top` (sound abstract lemma, (□)-application
   contested) remain reusable tools, not the (□) route. No separate lane remains — the route IS the decorated descent.
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
  **★ NOW CONCRETE as B5-desc leg (iii)/B5d — the `w>0` unit supply** (deeper cores bounded below a.e. →
  uniform on the compact box; technique banked). When genm-sj5-schur fills the inner-descent hole, this leg
  is where the RLCT-collapse would hide — audit it hardest at B5-desc review, decorrelated.
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
