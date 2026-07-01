# Threads — `determinantal-atlas`

Per-rung formaliser/reviewer threads (the ladder is in [`priorities.md`](priorities.md)). One **builder/committer**
per shared worktree at a time; read-only auditors run concurrently. Controller integrates + re-gates per
[`loop-prompt.md`](loop-prompt.md).

## P0 — recon

| rung | seat | teammate | status | notes |
|------|------|----------|--------|-------|
| P0 | scout | a687ac4d | ✅ DONE `787e688f` | verdict: mostly re-home/de-DLN-ify (overlap API + cover already built; residue bridge already proved); **capstone = BUILD** as a bespoke Zariski predicate over the rank-`r` open (NOT Mathlib `FiberBundle`, NOT over the closure). Refined ladder in `priorities.md`; report `threads/p0-recon/report.md` |

## Phase 1 — foundation (`det-atlas-p1`)

| rung | seat | teammate | status | notes |
|------|------|----------|--------|-------|
| P1.a | formaliser | abaaacd2 | ✅ DONE + RE-GATED `f6684cf5` | overlap API → `Core/RingTheory/Localization/Overlap.lean` (bare `Localization` ns); consumers swept. **Full-aggregator re-gate GREEN (3828 jobs), sorries 0, `awayTriple_cocycle` axiom-clean.** |
| P1.b | formaliser | a728b739 | ✅ DONE `d24f9b01` | `Core/RingTheory/Determinantal/Basic.lean` (bare `Matrix` ns): `detMinorPoly`/`eval_detMinorPoly` re-homed + generalized `Field→CommRing`; new `Matrix.determinantalIdeal` + API (`_mem_`, `_eq_span`, `_le_iff`). green 3829, sorries 0, axiom-clean |
| P1.c | formaliser | a4700497 | ✅ DONE `040a66e2` | `Strata.lean` (bare `Matrix`): rank strata + cover + connective `mem_rankLeLocus_iff_determinantalIdeal_le_ker` (field-level); `RankMinorCover` deleted, consumers swept. green 3829, sorries 0, axiom-clean, self-review+Codex PASS. (Tip advanced post-commit → L3 validated) |
| P1.d | formaliser | a8eebf34 | ✅ DONE `e572b50f` | `Schur.lean` (bare `Matrix`): `rank_fromBlocks_zero`, `pivotRankChartEquiv` (`finrank=r(p+q−r)`), `rank_eq_iff_schur_eq`, `schurComplement_normal_form`; `DeterminantalChart`+`SchurChartIff` deleted, `SchurGauge` kept (DLN gauge). green 3828, sorries 0, axiom-clean |
| P1.e | formaliser | a6a886c2 | ✅ DONE `f2cd20af` | `Dimension.lean` (bare `Matrix`, engine-free): `rankStratumDim`/`Codim` + `codim+dim=ambient` + finrank-anchor to the pivot chart; engine-bound `varietyDim_…_stratum`/`height_…` re-pointed + "Proved, not cited" docstrings. green 3829, sorries 0, axiom-clean. **PRECISION CORRECTION: Brick A is Proved (zero-cited, via the orbit codim engine), NOT cited — reviewer+Codex confirmed; my brief's "cited" tag was wrong** |

## Phase 1 — boundary re-gate (controller) ✅ PASSED
Full build green (3829 jobs); sorries 0 / **0 axiom**; axioms `[propext, Classical.choice, Quot.sound]` on all
Phase-1 headlines (`rankStratumCodim_add_rankStratumDim_eq` even pure `Nat`), on the engine-bound
`varietyDim_productRankLocusLE_stratum` (**Brick A Proved — no global axiom**), and on **both DLN payoffs
(unchanged)**. **Phase 1 complete → PR opened (base `dev`); proceeding to Phase 2.**

## ✅ Build status — re-gate GREEN; contamination episode CLOSED
- **Contamination (mine, fixed + confirmed):** the worktree's `.lake` was warmed (`cp -al`) from the
  **pre-FL-III** `foundation-lift` worktree → stale trdeg/Dimension oleans → spurious `Unknown constant
  Algebra.trdeg`. Diagnosed as cache not source. Fixed: `rm -rf .lake/build` + clean rebuild → **full aggregator
  GREEN (3828 jobs), `Dimension/Localization.olean` BUILT**. dev sound throughout. (→ lesson DA1.)
- **Box-load episode (resolved):** under heavy parallel-expedition load the from-scratch build OOM-thrashed;
  deferred until the box quieted (18G free), then re-ran clean → green. The worktree now has a correct warm
  `.lake` for the remaining rungs (P1.b+ build incrementally). (→ lesson DA2.)

## Phase 2 — constructive atlas + capstone (`det-atlas-p2`, off `-p1`)

| rung | seat | teammate | status | notes |
|------|------|----------|--------|-------|
| P2.a | formaliser | a9f9042b | ✅ DONE `5aad04f5` | `Atlas.lean` (bare `Algebra` ns): `StandardFibreChart` (structMap/triv/flat) + `flatModel`/`ofTrivialization`; DLN `standardFibreChartOfPivot` the non-vacuous instance. green 3830, axiom-clean; aggregator-wired at integration |
| P2.b′ | formaliser | a50b98e3 | ✅ DONE `50a6842d` | `AlgEquiv` groupoid laws (`trans_assoc`/`trans_refl`/`refl_trans`, `ext;rfl`) → `Core/Algebra/AlgEquiv/Groupoid.lean`; sibling-clash confirmed absent; axioms just `[Quot.sound]`. green 3831 |

> **#20 review fixes merged forward** (`58c661b7`): PR #20's three points (Schur `prodLequiv`→`private`; `rankStratumDim` docstring scoped to `r ≤ min p q`; priorities/Dimension prose Brick-A→Proved) landed on `det-atlas-p1` (`5d846875`, threads replied + resolved) and merged into `det-atlas-p2`; re-gate green 3830.
| **P2.b** | formaliser | acb882d6 | ✅ DONE + PUSHED `541bf5d3` | `Core/RingTheory/Determinantal/AtlasTransition.lean` (bare `Algebra` ns): `AtlasChart` (chartElt + bare-`k` `trivK` — Flag 2 pairing) + `overlapElt`/`targetChartLoc`/`overlapTriv`/`chartOverlapTransitionK`(+`_apply`/`_trans_symm`)/`overlapTransition`; `AtlasFibreChart extends AtlasChart` carries `StandardFibreChart`. `awayCongr'`(+`_symm`) re-homed to `Localization/Overlap.lean`. DLN `FibreTargetOverlap` re-homed: `pivotAtlasChart` the instance, base-side transition + round-trip = abstract `Algebra.AtlasChart.…` at the pivot charts; target-side kept one-`Away`-layer (instance-synth). Codex (xhigh) design-vetted Option C. **Flag 3 dodged** (bare-`k` trivK, no over-base `triv` in transition path — no diamond). full green 3832, sorries 0, axiom-clean `[propext, Classical.choice, Quot.sound]`. Cocycle set up reachable via groupoid laws (P2.c) |
| **P2.c** | formaliser | acb882d6 | ✅ DONE + PUSHED `718e0583` | cocycle-compatibility (2-fold): `overlapTransition_trans_symm` (target-side round-trip `= AlgEquiv.refl`) + `overlapTransition_symm` (inverse characterization), in `AtlasTransition.lean`. **Pure groupoid algebra, no localization-element entry**: `self_trans_symm`/`symm_trans_self` FOUND in Mathlib v4.29 (not built), inner cancel → LANDED `chartOverlapTransitionK_trans_symm` → outer cancel. No whnf/kernel-cost trap (the recon's `@[reducible] targetChartLoc` worry did not bite). green 3832, sorries 0, axiom-clean `[propext, Classical.choice, Quot.sound]`. Executor's decorrelated Codex (xhigh): SOUND. **Controller fidelity pass: faithful, non-vacuous.** This IS the recon's "cocycle field" (lines 52/94/125) → **P2.d unblocked** |
| **P2.f** (was P2.c′) | formaliser | p2f-triple | ✅ DONE + PUSHED `b6ab4764` (cocycle) | **target-side triple cocycle** — DELIVERED for the CANONICAL triple transitions: `tripleElt`/`targetTripleLoc` (symmetric: localize at the non-pivot PRODUCT `D·E`)/`tripleTriv`/`chartTripleTransitionK`/`tripleTransition`/`chartTripleTransitionK_cocycle`/**`tripleTransition_cocycle`** (`g_jk∘g_ij=g_ik`, cyclic=id), surfaced on the predicate. green 3834, sorries 0, axiom-clean; base cocycle by `algHom_subsingleton`, target by groupoid conjugation; fidelity-reviewed (1 docstring overclaim fixed). **GAP:** shipped cocycle is of the canonical triple transitions, NOT proved = the restricted 2-fold `overlapTransition` (the operator's naturality (iv)) — see P2.g |
| **P2.g** | formaliser | p2g-naturality | ✅ DONE + PUSHED `e1eec097` | **naturality (iv) DELIVERED** — `restrict_overlapTransition_eq_tripleTransition` + the **commuting square** `restrictTriple_comp_overlapTransition` (ties `restrictedOverlapTripleTransition` to the ACTUAL `overlapTransition` via the genuine `restrictTriple`/`baseRestrTriple` = `Away.mul'` further-loc, `IsLocalization.liftAlgHom`) + **`overlapTransition_restricted_triple_cocycle`** (operator's literal `g_jk∘g_ij=g_ik` for the atlas's OWN restricted 2-fold transitions). Reorder (`C·E`↔`E·C`) by `mul_comm` `awayCongr'`. Route: base-subsingleton over `Base` (SOUND; target-`M` avoided per Codex) + trivK conjugation. green 3834, sorries 0, all 8 axiom-clean. Codex SOUND, fidelity reviewer FAITHFUL (6 checks). **Controller fidelity PASS + independent re-gate (build 3834 + `#print axioms` on all 5 headlines = standard-3).** |

## PR #21 re-review (operator, source-only, 2 passes) — no soundness issue; 3 fidelity/doc items
| rung | seat | teammate | status | notes |
|------|------|----------|--------|-------|
| **P2.h** | formaliser | p2h-product | ✅ DONE + PUSHED `e30952ff` | (3) **STRENGTHEN-A** [substantive]: `AtlasFibreChart` drops `extends`/`M`, stores only `chartElt`+`fibreModel`, DERIVES `toAtlasChart` with `trivK := fibreModel.triv.restrictScalars k` — product triv is the SINGLE source of truth, tie is DEFINITIONAL (`trivK_eq_product = rfl`). Corollary `overlapTransition_isProduct` (cocycle is genuinely of the over-base PRODUCT). DLN instance discharges structurally (rfl). (1-2) all stale-doc sites swept (`AtlasTransition` Scope+`tripleElt`, `FibreTargetOverlap`, `DLNFibre.lean` comments, `FibreZariskiLocalTriviality`, `LocalTriviality`) → only GLOBAL gluing/π/Flat-π (R1) remains marked not-built. Codex verdict STRENGTHEN-A. **Controller fidelity PASS + independent re-gate: green 3834, sorries 0, `#print axioms` standard-3 on product corollary + witness + BOTH DLN payoffs (no regression).** |

## PR #21 re-review — FOLLOW-UP (10:06Z two-item review, at head b1902e79)
Controller mis-targeted the first consolidated reply at the 09:02Z three-item review; the 10:06Z
follow-up raised TWO items still open. (→ lesson DA4: fetch the LATEST reviews before replying "resolved".)
- **Item A (stale product-API docs) — FIXED `a58752ce`** (controller, doc-only): LocalTriviality chart-field
  doc + `overlapTransition_trans_symm` docstring (the now-false "DECOUPLED / NOT an over-base-product
  cocycle" — invalidated by the P2.h tie); AtlasTransition `AtlasFibreChart` module bullet (stale
  `extends`/`trivK_eq`-field wording). green 3834, no stale tokens remain.
- **Item B (named `targetProductOverlapTransition_trans_symm`) — WALL, surfaced to operator.** The DLN
  transition defs (`overlapTriv`/`targetChartLoc`/`targetProductOverlapTransition`) are CONCRETE (via
  `perPivotLocalTrivializationDatum.trivialization`), not routed through the abstract atlas; the abstract
  round-trip works generically over opaque `C.trivK` but at the concrete `pivotAtlasChart` `trivK` reduces
  to the trivialization monster → both delegation and direct groupoid proof `whnf`-timeout (200000).
  Reverted; honest prose note added (predicate-level `overlapTransition_trans_symm` on `pivotAtlasFibreChart`
  is the green exported round-trip form). Options for a concrete named theorem: (i) `maxHeartbeats` bump
  (historically used here; slow, discouraged), (ii) mark the concrete trivialization `irreducible` (may break
  flatness/product proofs), (iii) accept predicate-level export + note. Awaiting operator call.

## PR #21 re-review — earlier three items (09:02Z) RESOLVED (P2.h)
Strengthen (item 3), stale-doc sweep (items 1-2), narrowed cocycle prose (item 2) all landed `e30952ff`; controller-verified. The capstone predicate `IsZariskiLocallyTrivialAffineProduct` now earns its name: the transitions consume the over-base PRODUCT trivialization, so pairwise inverse + triple cocycle are genuine product-atlas coherence. **#21 ready for operator merge.**

## Phase 2 — atlas coherence COMPLETE (P2.f + P2.g)
The atlas API now carries the **full standard coherence package** (operator's PR-#21 request): cover · per-chart
over-base product · pairwise inverse law (`overlapTransition_trans_symm`, P2.c) · **triple cocycle of the atlas's
own transitions** (`overlapTransition_restricted_triple_cocycle`, P2.f+P2.g, tied via naturality/commuting-square).
Independent controller re-gate GREEN (3834, sorries 0, axiom-clean). R1 now scoped to the GLOBAL gluing only
(naturality is an INPUT to it, not the gluing). **#21 ready for operator merge.**
| **P2.d** | formaliser | p2d-capstone | ✅ DONE + PUSHED `7b43aaef` | **`Algebra.IsZariskiLocallyTrivialAffineProduct k Base M BaseLoc Fibre U`** (`LocalTriviality.lean`, bare `Algebra` ns): `ι` + `chart : ι → AtlasFibreChart` + `cover : (⋃ basicOpen chartElt) = U`. **Cocycle = derived lemma (not a field)** — `overlapTransition_trans_symm`/`_symm` from P2.c (holds for any `AtlasChart`s). DLN instance `reducedFibre_isZariskiLocallyTrivialAffineProduct` (`FibreZariskiLocalTriviality.lean`) at `U = rankROpen` (open, load-bearing — not `⊤`); new cover lemma `iUnion_pivotDatum_basicOpen_eq_rankROpen` (PivotDatum-indexed, le_antisymm via banked selector cover). green **3834**, sorries 0, **instance witness axiom-clean** = non-vacuity. Executor Codex (xhigh): clean on all 5 fidelity Qs. **Controller taste-check: faithful + sound.** |
| P2.d review | reviewer | p2d-review | ✅ DONE — **PASS-WITH-NITS** | decorrelated audit (`threads/p2d-review/verdict.md` + Codex): sound + faithful, no soundness/fidelity defect; new cover lemma correct (both inclusions), no global-bundle over-claim. **Independent re-gate GREEN 3834, sorries 0, axiom-clean** (= Phase-2 boundary re-gate). Two prose-precision nits FIXED `60fb928b`: Q2a (instance "non-vacuity/geometric witness/realized" → honest inhabited/satisfiable; `rankROpen ≠ ∅` not proved) + Q1c (cocycle decoupling line: on `trivK`/`M`, not the over-`BaseLoc` product). **Escalated to operator:** `Base → TotalRing/AmbientRing` rename (signature change — `Base` is the total/source ring by AG convention; docstrings flag it, mathematically fine) |

## Operator decisions (2026-06-30)
- **Capstone naming → BRIDGE, not keep-vs-rename.** Operator: build a bridge so the predicate retains its
  correct names in BOTH worlds (ring-theory `Base`/`BaseLoc` ↔ AG `total`/`base`/`fibre`/`projection`, via the
  `Spec`-contravariance flip) rather than pick one convention. → **rung P2.e** (additive view, keep `Base`/`BaseLoc`;
  scheme-side accessors PER-CHART; global fibration morphism R1-gated). Dispatched (`p2e-bridge`).
- **Phase-2 PR → OPENED (#21)** `det-atlas-p2 → dev` (https://github.com/edmund-ukaisi/geometry-of-dln-fibre/pull/21),
  after P2.e landed green, shipping the complete both-worlds capstone. **Awaiting operator merge** (merging
  stays operator's). After merge: branch cleanup + mark expedition complete.

| rung | seat | teammate | status | notes |
|------|------|----------|--------|-------|
| **P2.e** | formaliser | p2e-bridge | ✅ DONE + PUSHED `80991e75` | two-worlds bridge view: `FibrationView` accessors `totalSpace`/`fibreSpace`/`chartBaseSpace`/`chartProjection i = comap (fibreModel.structMap)` + `Spec`-flip dictionary docstring; additive (`Base`/`BaseLoc` kept), shape = bare accessors (not a wrapper — Codex concurred). Per-chart projection only; global `π` NOT constructed (needs gluing of per-chart projections — R1; **Codex sharpening:** for maps into a fixed target the gluing condition is pairwise overlap-agreement, NOT the triple cocycle). DLN dictionary `rfl`-example. green 3834, sorries 0, accessors axiom-clean. 4 Codex fidelity fixes folded in. **Controller fidelity pass: faithful + honest.** |

## Phase 2 — boundary re-gate (controller) ✅ PASSED
Full aggregator GREEN (**3834 jobs**); sorries 0 / 0 axiom; the P2.d capstone (`reducedFibre_isZariskiLocallyTrivialAffineProduct`) + the abstract predicate's derived cocycle + the new cover lemma all axiom-clean `[propext, Classical.choice, Quot.sound]`; both DLN payoffs unchanged. Decorrelated review PASS-WITH-NITS, nits fixed (`60fb928b`). **Phase 2 COMPLETE (P2.a/b′/b/c/d) → ready for the Phase-2 PR (base `dev`, signal-and-wait).** Roadmapped-not-built: P2.c′ triple cocycle (R1 global-gluing track).

## Concurrency rule (this expedition)
At most **one builder/committer** in `.claude/worktrees/det-atlas` at a time (a second `lake build` corrupts
`.lake`; two `git commit`s race the index). Read-only auditors (no build, no commit) may run alongside one
builder. Rungs touching the same file are serialized.

_Updated each tick._
