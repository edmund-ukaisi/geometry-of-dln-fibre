# synthesis.md — Aoyagi-Full controller's integrative read

(Internal ledger; assumes repo context. Flushed every tick; read on re-ground. Not a deliverable.)

## ⚠ RECOVERY (2026-06-22 ~01:30) — VM CRASHED mid-construction; reorient + recreate team
**The VM crashed** during the construction phase (ConnectionRefused on the agents). Reorientation:
- **DURABLE (survived, on origin):** `origin/expedition/aoyagi-full @e6827ba` = the ENTIRE DESIGN PHASE — locked resolvedForm interface (explicit `dlnLoss M' 0` reduced core), #127 per-node (L,R)-transvection witness, #128 L2 squeeze bridge, #126 per-node-distinct, the 5-point IsSchurStraighten contract, all pp-hall certs. PLUS `origin/fm/a2-theta @2a41a8c` = the A2 achiever-θ arithmetic substrate (committed+pushed). The hard part is safe.
- **LOST / early-stage (specs all durable in the certs, cheap to redo):** fm's cover build (`.claude/worktrees/r1-cover` clean @e6827ba — was just starting), a114e07e's L2 build (`.claude/worktrees/l2-product` clean @1822374 — was still scoping the general squeeze).
- **SALVAGEABLE on disk:** fm-2's crux sub-lemma (1) `hardPivot_schur_blockId` (the `fromBlocks_eq_of_invertible₁₁` block-identity, ~28 lines, mid-proof) — uncommitted in `.claude/worktrees/fm2-ge/…/GeneralR1Recursion.lean`.
- **TEAMMATES: DEAD** (crash). RECREATING the construction team.
- **REMAINING CONSTRUCTION (all against the durable @e6827ba specs):** (1) the crux `schur_straighten_exists` body [(1) block-id ≈salvaged → (2) dlnLoss decoupling → (3) MP-shear k-composition via lemma2Fwd's measurePreserving_shearAt → assemble]; (2) the (C2) cover + ResolutionTree recursion → `core_rlct_eq_lambdaCore`; (3) L2 = the SQUEEZE (Φ:=Σreg²+G²; c₁Φ≤F≤c₂Φ + rlctAt_mono×2 + unit-strip + S1.5) + half-(b); (4) A2 `aoyagiTheta_eq` re-scope to the divisor-mult form + the AchieverTheta aggregator wire; (5) T (#10) assemble `aoyagi_learning_coefficient`. pp-hall (pen-and-paper) + rv-2 (reviewer) on-demand. Design is bedrock; this is pure green-tools-only Lean construction.

## Current read (2026-06-21 ~21:45): ★★ MILESTONE — ACTIVE SCOPE COMPLETE: A1 CLOSED + LADDER 3/3 CLOSED ★★

**The active scope (validate ladder (1,1,1)→(2,1,2)→(2,2,2) + A1 `lambdaCore_eq_clean` + machinery) is COMPLETE.** Both
milestone events landed + independently gated. Two PRs ready (operator-gated). G3 (general-M) surfaced to the operator.

**A1 CLOSED @`9e2faea` (origin/worktree-rung0-defs) — 4-leg gated PASS.** `lambdaCore_eq_clean (M)(hL:1≤L) :
∃ c hc, 1≤c ∧ lambdaCore M = cleanCore c (sortedSmallest M c hc)` — sorry-free. `#print axioms = [propext,
Classical.choice, Quot.sound]` (clean-three, **NO monomial_rlct** = S2-independent arithmetic as required, NO
sorryAx). Full library green 2890 jobs; scripts/sorries 6→5 (A1 chain sorry-free; 4 remaining Skeleton sorries =
the OTHER contract rungs L2/D1/general-R1/A2 + 1 stale Case222 stub on this branch). The 4 gating legs:
a114e07e build + controller source-corroboration + fm 5-check PASS (statement/value/hL/non-vacuity) + pp-hall
cliff verdict (decorrelated). ARCHITECTURE: forward-max engine (`forwardMax` + `eraseIter` global↔local bridge)
→ feasible competitor qFM; qStar prefix-dominates-qFM; u-space band (`band_of_uTel`); carrier `FMDom` via an
**in-order strong induction `FMDom_all`** (resolved a genuine declaration cycle, well-founded band-at-<i,
`qFM_uTel_band`'s statement UNCHANGED); achiever core `static_count` = band-free **order-statistic kernel**
(`aS_m<τ`, gfc only inside `aS_succ_le_Yvec`, Codex-Lean-checked) + **positional closer** (`M^k≥uTel_k` via the
uTel-recurrence identity + IH band, no gfc). **8 confounds caught/corrected across this seam** (see lessons).

**LADDER 3/3 CLOSED @`1034c80` (origin/fm-2/case222-block) — rv-2 PASS all gates.** `case222_rlct : rlctAt H222
(dlnLoss H222 0) deepest222 = 3/2` — the GENUINE rlctAt ladder headline (matching case111_rlct/case212), via the
proven axiom-clean connector `rlctAtOn_eq_rlctAt` + `deepest222=origin` (sound, non-vacuous bridge). Voigt-merged
(union-resolved aggregator), full library green 3699 jobs, sorries = exactly the 5 Skeleton rungs, S2 the only
citation, merges cleanly onto dev. `(2,2,2)` value = ≤ (`rlctAtOn_myF222_le`, +monomial_rlct) ∧ ≥
(`rlctAtOn_myF222_ge'`, clean-three S2-free, the genuine 24-leaf blow-up cover) → `rlctAtOn_myF222_eq = 3/2`.

**TWO PRs READY (operator-gated; the operator opens/merges):**
1. `fm-2/case222-block @1034c80` → dev (ladder 3/3, the (2,2,2) value). fm's PR-body draft adapted to the rlctAt
   headline. Merges cleanly onto dev (0 conflicts), Voigt already in.
2. `worktree-rung0-defs @9e2faea` → dev (A1, lambdaCore_eq_clean). **ORDERING:** land PR 1 first, then merge the
   new dev into the A1 branch (drops its stale Case222 stub via dev's real (2,2,2), keeps A1's Skeleton) before
   PR 2 — the two branches both touch Skeleton/Case222 at different bases.

**OPEN / SURFACED TO OPERATOR:** (a) **G3 (general-M) scope-decision** — the path to the GENERAL
`aoyagi_learning_coefficient` (still sorryAx) is the 4 remaining Skeleton rungs (D1/L2/general-R1/A2); per the G3
memo (#105/#106) the cover-side general regular-change is make-or-break and should be gated on a pen-and-paper
adjudication FIRST (route-before-lines). (b) **24-leaf `resolution_charts_case222` fidelity roadmap** — the Unit-
collapse ∃-witness is contract-faithful (the genuine geometric content is in the ≥-cover) but a faithful 24-leaf
packaging is a boundary-move, roadmapped not built. (c) the honesty framing: this is **ladder rung 3/3 (the
(2,2,2) VALUE)**, NOT the general headline — the 5 general-M Skeleton rungs stay open.

### UPDATE (~22:15) — operator said "drive to completion, your call"; GENERAL-M PHASE OPEN; G3.2 GATE GO
Operator handed the milestone back (hero task, executive call mine). Opened general-M, route-before-lines for the
mountain. **G3.2 GATE GO** (pp-hall #109, WITNESS-CONFIRMED + decorrelated: exact-symbolic L≤3 + multi-step r=2
(3,3,3)→(2,2,2)→(1,1,1) + Codex conceptual all-L transported-line/covector proof). General-R1 is now a CONSTRUCTION
task (math settled, well-founded ΣM-drop). ONE caveat baked into the route: **chart-LOCAL adapted bases**
(transported-line/hyperplane), NOT a global polynomial Q (RLCT local at origin). Active general-M wave:
- **fm-2 → general-R1 mountain (#111)**: the G3.2 Schur lemma (chart-local pivot, ‖∏C‖²=monomial×‖∏C'‖², reuse
  L1+S1.5), then recursion/cover/G5-glue. Incremental; rv-2 audits as pieces land.
- **pp-hall → D1≥ value-freeness (#112)**: is the two-point core-domination core(deepest)≤_local core(v) value-free?
  (a114e07e's L2-scope: homogenization (a) R1-separable, S1 germ tools green; D1≥ needs (a)-type, the two-point
  domination is the Aoyagi-Thm-2 crux.) Verdict unblocks D1≥.
- **a114e07e → D1**: D1≤ banked green (origin/d1-scope), D1≥ parked as named sorry pending pp-hall #112.
- **fm → A2b (#110)**: faithful named-witness θ rung (achiver chart, A2a's free-∃ rejected as the weak-existential
  trap; cAch-as-findGreatest LOAD-BEARING — θ not constant across tied achievers). S2-free, A1-substrate.
- DEP MAP: value chain G3.2→R1→L2(b); L2(a)+D1≥ parallel (pending #112); θ (A2) = R1-COUPLED (folds into R1 as B2, NOT standalone — the faithful θ axis-set IS the resolution divisors; B1 surrogate rejected as coincidental-construction).
- **INTEGRATION MODEL (operator directive ~22:30): ONE mega-expedition branch = `expedition/aoyagi-full`; push/merge EVERYTHING there; NO PRs until the hero task (general-M headline) is COMPLETE.** The "two milestone PRs" are SUPERSEDED — A1 + ladder 3/3 + all general-M work consolidate into expedition/aoyagi-full (fm-2 doing the consolidation merge: d1-scope [Skeleton=A1-line] + fm-2/case222-block [(2,2,2)/Voigt], #111-prefix). The dev→master PR happens once, at completion. So no operator gating mid-flight; the controller merges freely into the mega-branch.

### UPDATE (~23:35) — GENERAL-M BUILD PHASE LIVE: (C2) architecture set, L2↔R1 SEAM LOCKED, D1 UPGRADED
Architecture fully resolved + the team building all 4 remaining Skeleton rungs in parallel. Two interfaces brokered through the controller (route-before-lines on the seams); two major confounds caught + corrected BEFORE lines.

- **(C2) per-node architecture (the clean-recursion confound KILLED):** general-R1 = the (2,2,2) machinery generalized, two stages per node: (1) **det-1 Schur GL-straighten** (fm-2's `resolvedForm`, generalizing `lemma2Fwd`/Aoyagi-Lemma-2 — measure-preserving, UNIT Jacobian, straightens the rank-defect center {r−pq=0}→coordinate center {w=0}); (2) **coordinate-subspace blow-up** (fm's `g5_pivotNode`/`pivotBlowupOn`, Jacobian |u|^{Mval−1}, (k,h)=(1,Mval−1), ratio Mval/2) → ⨅ monomialThreshold. The CLEAN det-1 recursion was DISPROVED (fm-2 dimension count: det-1 conserves dim ⟹ telescopes to ambient/2 = 4 ≠ 3/2 for (2,2,2); the blow-up monomial weights carry the 5-dim-fibre deficit). Anchored in the verified (2,2,2): `step1Residual = resolvedForm ∘ lemma2Fwd` THEN cover.
- **resolvedForm INTERFACE (fm-2→fm, R1-internal):** 5-field contract (fm's ask) — (1) type `(chart dom)→(Fin N'→ℝ)`; (2) MeasurePreserving/det-1 unit-Jac; (3) coordinate-center ID {r−pq=0}→{w=0} exposing the EXPLICIT pivot index set; (4) reduced-chain map (M'+core'); (5) strict-transform eq `core x = core'(resolvedForm x)`. fm-2 drafting the SIGNATURE first (so fm builds the cover in parallel); pp-hall decorrelated-validating the contract for completeness vs the (2,2,2) anchor before fm-2 commits the body.
- **L2↔R1 SEAM LOCKED (a114e07e's catch — S2-hygiene, LOAD-BEARING):** L2 (`product_reduction`) consumes the **core-VALUE form** `core_rlct_eq_lambdaCore : rlctAtOn (core_M) 0 = ofReal (lambdaCore M)`, **NOT** the raw `⨅ monomialThreshold`. Reason: the ⨅-form would force S2 (`monomial_rlct`) INTO L2 to evaluate it, violating "S2 strictly downstream of R1." R1 proves the ⨅-form `resolution_charts` (carries S2, the (2,2,2) `rlctAtOn_myF222_le` form) THEN bridges ⨅ → lambdaCore via **G3.5** (chart-ratio→min, #115-cert) + **DEFINITIONAL unfold** (`lambdaCore M := ½·(Adm M).inf' (Mval M)`, Lambda.lean:80 — **A1-FREE**; A1 = the separate clean-closed-form identity `lambdaCore = cleanCore(¼(∑Y²−∑M²))`, OFF this path — fm's correction, one fewer coupling) — all INSIDE R1 — to produce `core_rlct_eq_lambdaCore`. THAT value equality crosses the seam; L2 stays S2-clean. ⚠️ Do not re-spec L2 onto the ⨅-form on a re-ground — it re-introduces the S2 contamination.
- **L2 build (a114e07e, on d1-scope):** = half-(a) deepest-point regular/core split (block-elimination coord homeomorph + S1Fubini nReg-peel; template = (2,2,2) `e222` transport — REAL lines; the brief's named helper `dlnLoss_one_layer_deepest` does NOT exist, build from green L1/S1.5/S1Fubini) + half-(b) reduced to `core_rlct_eq_lambdaCore` (the single interface sorry).
- **D1 UPGRADED (pp-hall #122):** D1≥ (the ⨅-over-fibre geometric refinement) is **NOT** Mathlib-scale constant-rank — there's an ELEMENTARY route: gauge to rank-r identity corner (`block_elimination`, done) + **triangular unit-pivot elimination** (solve zᵢ=−hᵢ/uᵢ by division by a unit, iterate; chain multilinearity ⟹ each pivot linear ⟹ no non-triangular case), verified exactly at L=3 (2,2,2,2) intermediate v. Lean ingredient = local unit-division + finite triangular induction (FAR lighter than constant-rank). Status: "Mathlib-gated detour" → **"elementary self-contained rung, ON DECK after the headline."** Headline STAYS `rlctAt(deepest) = aoyagiLambda` (SLT coefficient via L2+R1). a114e07e's D1≥ docstring (d1-scope @5c14f35) now OVERSTATES the difficulty ("Mathlib-contribution-scale") — precision fix to fold into its next L2 bank.
- **A2 — `thetaGeom = aoyagiTheta` over Adm is FALSE (fm's numerical sanity-check, corrects MY premise):** I called A2 "validated on cert cases" — WRONG: the cert table omitted **(2,2,2,2,2)**, the breaker — BOTH naive `thetaGeom` defs (#argmin Adm = 6, #binding rank-strata = 6) but `aoyagiTheta = 5` (the design-spec's OWN §3 l.149 warning: "6 minimisers but θ=5, naive count over-counts"). So there is NO pure-ℕ Adm/Mval bridge. ⟹ CONFIRMS **B3** (already-decided): faithful θ = a(ℓ−a)+1 = per-CHART binding-divisor multiplicity = **R1-divisor content (G3.6, gated on #111)**, NOT computable from Adm. A2 fill-work = the HONEST arithmetic substrate ONLY (`aTheta M := Sprefix M (cAch M+1) % cAch M` + `aoyagiTheta` totality + `cAch`-canonicity, ~30-50 lines, feeds G3.6, NO false bridge) — fm building (b), pivots to cover on resolvedForm. ⚠️ The Skeleton `aoyagiTheta_eq` (~1495), if stated as the Adm-bridge, is a WRONG-statement sorry — re-scope to the divisor-multiplicity form (controller, headline-writer) when G3.6 is close.
- **Recursion-step MP-resolution + regular-strip DECONFLICTION (fm-2):** my unconditional "GO clean `schur_rlct_recursion_step`" was WRONG (fm-2's `ambient/2 = 4 ≠ 3/2` disproof stands for the unconditional). fm-2's fix (Lean-tested): the step is sound + provable **as a CONDITIONAL with `MeasurePreserving chart` (+≃ₜ+MeasurableEmbedding) added** — `rlctAtOn(dlnLoss M 0)(chart 0) = nReg/2 + rlctAtOn(G²) 0` via transport+unit-strip+S1.5; the unsoundness relocates ENTIRELY to `schur_scalar_normalForm`, which becomes the **C2 form** (= the resolvedForm/det-1 straighten, NOT the false scalar-MP form). ⚠️ This recursion-step = a114e07e's L2 **half-(a)** (same regular/core split → nReg/2). DECONFLICT: fm-2's recursion-step is the CANONICAL regular-strip engine; **a114e07e CONSUMES it for half-(a)** (build against its statement, fm-2 proves it), NOT rebuild (#125 tracks the same-vs-different-level check). fm-2 reports TWO signatures: recursion-step (for L2) + schur_scalar_normalForm/resolvedForm (for the cover).
- **LANE MAP:** a114e07e = L2 (+ D1 banked/on-deck); fm-2 = resolvedForm (R1 front); fm = cover #113 (R1 back, held for resolvedForm) + A2 fill; pp-hall = resolvedForm-contract validate + D1 on-deck route (g122 cert); rv-2 = green-gates. All → `expedition/aoyagi-full`. A1 CLOSED; D1≥ roadmapped/on-deck.

### UPDATE (2026-06-22 ~00:10) — MILESTONE: general-M CONSTANT-RANK-FREE; chart-construction picture COMPLETE; crux = schur_chart_exists
- **schur_recursion_step_sound PROVEN** (0 sorry @5499bc4): the MP-conditional regular-strip, via rlctAtOn_comp_homeomorph → rlctAtOn_germ_local (NEW reusable bedrock) → rlctAtOn_unit_invariant_aux → S1.5. + **IsSchurNode type banked** @6fd2379 (the blow-up-form ResolutionNode carrying strictTransform/monExp/measure_drops/active-pivot — fields 1-6). Crux isolated to `schur_node_exists`/`schur_chart_exists` (the MP-chart CONSTRUCTION).
- **WHOLE general-M push is CONSTANT-RANK-FREE** — the Mathlib gap that forced the rlctAt(deepest) headline re-scope is GONE for BOTH rungs: L2 (#125) + D1≥ (#122) each have an explicit elementary triangular-unit-pivot route on identity corners (deepestPoint_exists), verified exact on (2,2,2)/(3,2,3)/(2,2,2,2)/(4,3,2)/(4,4,4). (Headline stays rlctAt(deepest); D1≥ ⨅-fibre on-deck, now cheaply.)
- **Chart-construction COMPLETE + the unit-weight-vs-MP CATCH (pp-hall #125, LOAD-BEARING — corrected my own wrong-tool routing):**
  - **L2 outer deepest peel (a114e07e half-(a), NO blow-up):** χ is UNIT-Jacobian (det=unit≠±1, INTRINSIC — pivot (1+w0) multiplies the pivot var; verified (2,2,2): det=(w0+1)²(w4+1)). ⟹ NOT MeasurePreserving. Do NOT use schur_recursion_step_sound / rlctAtOn_comp_homeomorph (both REQUIRE MP). Use the **UNIT-WEIGHT transport** (rlctAtOn_unit_invariant_aux: |Jχ|∈[a,b], 0<a, doesn't move sSup) + germ_local + S1.5. ⚠️ Do NOT re-route a114e07e's half-(a) to MP on a re-ground — that's the wrong-tool bug, caught here before lines.
  - **R1 per-node chart (fm-2 schur_chart_exists, POST-blow-up):** the blow-up normalizes the pivot to a HARD 1 ⟹ pure TRANSVECTIONS (det=±1) = lemma2Fwd (measurePreserving_lemma2) ⟹ MP ⟹ schur_recursion_step_sound APPLIES. **Per-node — pp-hall #126 (CORRECTS an earlier "apply #125 directly" inference):** NOT apply-#125-directly. The per-node zero-core (B'=0, all generators bilinear, Jac rank 0) has NO regular block/unit-pivot for #125's peel; instead the per-node node = fm's (B) blow-up FIRST (→ hard-1 pivot) → fm-2's (A) MP transvection straighten → recurse. A DISTINCT C2 node reusing green pieces (elementary, uniform assembly, no new mechanism).
  - Both are unit-GENERATOR equivalences (RLCT-invariant via S1 transport), NOT literal Euclidean Morse (stronger, unneeded) — formalisers aim at the weaker target.
- **THE CRUX = `schur_straighten_exists` (fm-2):** the per-node MP-transvection straighten — the (A) field ONLY (post-blow-up, det±1, lemma2Fwd-generalization), NOT the composite node. DESIGN GATE CLOSED by #126; ORDER resolved (blow-up THEN straighten per-node). **LANE (controller-set):** blow-up + node-assembly + cover glue = fm's (B, pivotBlowupOn/#113); det-1 straighten ONLY = fm-2's (A) — fm-2 does NOT re-add the blow-up (it deleted IsSchurNode for exactly this). fm-2's `IsSchurStraighten` interface (χ on post-blow-up coords, banked @3b7a831) VINDICATED + relayed to fm for sign-off. **Design phase essentially COMPLETE** — remaining = heavy Lean construction + pp-hall's UNIT-WEIGHT transport lemma for a114e07e's L2 half-(a) (the last open design item, gating half-a).
- **LANE (current):** a114e07e = L2 (half-a UNIT-WEIGHT peel + half-b → core_rlct_eq_lambdaCore); fm-2 = schur_chart_exists [CRUX] + recursive node; fm = blow-up cover #113 (held for fm-2's residual+field-3) + A2 substrate (b); pp-hall = unit-weight lemma + order confirm (#125 done); rv-2 = audit @5499bc4. A2 `aoyagiTheta_eq` = bare-existential placeholder, re-scope to faithful divisor-mult (thetaDivisorMult) at R1-time.

### UPDATE (2026-06-22 ~00:32) — ★★ DESIGN PHASE 100% COMPLETE — every gate cleared; pure construction remains ★★
All general-M design gates closed: #109/118/121 (C2 architecture), #112/122 (D1 elementary, constant-rank-free), #115 (cover), #123 (recursion fields 4+6), #125 (L2 outer unit-Jac transport), #126 (per-node = DISTINCT node, blow-up→hard-pivot transvection), **#127 (the per-node adapted-basis WITNESS, @1822374)**. The push is now pure Lean construction against validated, elementary, constant-rank-free specs.

- **#127 WITNESS (the crux's last gate, @1822374):** explicit unipotent transvections on the (3,3,3) reduced node — general block `A=[[1,a],[b,D]]` → `L=[[1,0],[−b,I]]`, `R=[[1,−a],[0,I]]` (det=1) → `L·A·R = blockdiag[1, D−ba]`. Hard-1 uniform per-node (blow-up normalizes a coord to 1); chart-locality handled (#109 caveat — cover supplies a hard-1 locally, NOT an obstruction); ΣM'<ΣM; only obstruction = straightening BEFORE blow-up (⟹ blow-up-first). So `schur_straighten_exists` = blow-up(hard-1) → det=1 transvection(L,R) → regular pivot-row + smaller zero-core → recurse; straighten is MP → rlctAtOn_comp_homeomorph.
- **THE ENGINE DECISION (i) — bounded-unit-Jacobian, ONE canonical regular-strip:** fm-2 flagged that `schur_recursion_step_sound` requires MeasurePreserving, but a114e07e's L2 chart is unit-Jacobian (pp #125) — a real mismatch. RESOLVED: generalize `schur_recursion_step_sound` to a BOUNDED-UNIT-Jacobian chart (drop MP; |det Dπ|∈[a',b'], 0<a'; unit-Jac weight absorbed via rlct_unit_invariant_aux + weightedThreshold_transport_aux). ONE engine for BOTH R1 (det±1, special case) AND L2 (perturbed-unit) — avoids the double-build. ~+30 LoC (fm-2), independent of the crux. a114e07e CONSUMES it for L2 half-(a) (does NOT separately build rlctAtOn_comp_unitJac).
- **fm SIGN-OFF status:** conditions (a)+(b). **(b) [explicit center field active/p]** = ALREADY in @0caad83 (pivot_active/active_nonempty; fm reviewed the older @3b7a831). **(a) [flatRedCore = explicit `dlnLoss M' 0 ∘ flat-embed`]** = fm-2 specializing now (fm's structural recursion descends on M'). On (a) landing → fm LOCKS → pivots to the cover.
- **LANE (construction phase):** fm-2 = engine-(i) generalize + `schur_straighten_exists` [crux] + flatRedCore(a); fm = re-review @0caad83 → lock → cover (structural recursion wrapping g5_pivotNode over tree depth, base case = L=1 smooth-block) + A2(b) DONE @2a41a8c; a114e07e = L2 (deepest unit-Jac χ + bounded-unit-Jac hypothesis + factor → consume engine; + half-b → core_rlct_eq_lambdaCore); pp-hall = FREE (every design gate cleared), on call for decorrelated fidelity-audit as heavy builds land; rv-2 = audit @5499bc4/@0caad83.
- **INTEGRATION (deferred to next consolidation pass):** wire fm's `AchieverTheta` import into DLNFibre.lean (controller single-writer); consolidate d1-scope (a114e07e L2/D1) + fm/a2-theta into expedition/aoyagi-full. Banked + acyclic, no urgency.

### UPDATE (2026-06-22 ~00:40) — #128: L2 route REFINED to the SQUEEZE (supersedes the χ/engine-(i) bits above)
pp-hall #128 (@cdfc18a) — a114e07e's L2 seam catch was RIGHT; it refines the L2 route (and moots engine-(i)):
- **The clean form `F∘χ = ΣEᵢ²+G²` is FALSE.** The deepest split's core couples to the regular coords: F = ΣEᵢ² + (G + E·h)² (cross terms 2G·E·h). The (2,2,2) anchor's resolvedForm is likewise COUPLED. No c-o-v produces the clean SoS — so S1.5 cannot be fed a literal ΣEᵢ²+G² from a source chart.
- **L2 half-(a) = the SQUEEZE (NOT a coordinate split / c-o-v):** Φ := Σ(reg gen)² + G² (G = E-FREE Schur core, defined directly as the clean form). Squeeze c₁Φ≤F≤c₂Φ near 0 (STRUCTURAL: F−Φ=(g11−G)(g11+G), g11−G ∈ regular ideal (g00,g01,g10) ⟹ bounded-linear-perturbation, F/Φ→1) ⟹ rlctAt(F)=rlctAt(Φ) [rlctAt_mono ×2 + unit-strip of the constants] = nReg/2 + rlctAt(G²) [S1.5 on Φ]. **GREEN-TOOLS-ONLY** (rlctAt_mono ×2 + rlctAtOn_unit_invariant_aux + smoothBlockND_rlct + S1.5); NO constant-rank, NO Morse, NO c-o-v, NO measure-Jacobian, NO ideal-generator-invariance (project lacks it — don't reach for it). The ONLY new obligation = the squeeze inequality (elementary, regular sequence). a114e07e DROPS the deepest unit-Jac χ construction — the squeeze sidesteps it.
- **The "two units" / unit-Jac concern is MOOT** — the squeeze compares F and Φ at the SAME point (no c-o-v). ⟹ **engine-(i) [bounded-unit-Jac generalization] is MOOT** — L2 doesn't consume a c-o-v engine. fm-2 KEEPS `schur_recursion_step_sound` MeasurePreserving for R1 (drop the +30 LoC generalization).
- **The coupling is L2-SPECIFIC** (the outer, NO-blow-up, perturbed pivot 1+w0). It does NOT hit R1: R1's per-node is POST-blow-up hard pivot → EXACT transvection (#127 L·A·R=blockdiag[1,S]) → DECOUPLES cleanly into Σ(pivot)² + ‖S·A2red‖² (E-free). So fm-2's clean hfactor IS satisfiable for R1; its MP recursion-step + schur_straighten_exists stay sound, unchanged. (Reconciles #127 blockdiag vs #128 coupling: blow-up-or-not.)
- HONEST scope refinement of #125/#122: the deepest split is NOT a clean coordinate ΣEᵢ²+G² (would need a Morse normal form the project lacks); it's the rlct-level SQUEEZE to the idealized Φ + S1.5. Still constant-rank-free. a114e07e's route-before-lines catch forced this BEFORE the false-literal body went down.

## Prior read (2026-06-21): ★ R1 EXECUTION — S1.5 sorry CLOSED (6→5) @1304cf2; (2,2,2) route PINNED ★

**Milestone @`1304cf2` (pushed origin, rv-2 auditing):** the S1.5 wire is in — `rlct_additive_smooth_block`
now `exact …_aux` (closes a sorry, **6→5**), axioms `[propext, Classical.choice, Quot.sound]` (no sorryAx,
no monomial_rlct). `resolution_charts` **re-scoped to the CORE form** `rlctAt M (dlnLoss M 0) (0:Params M)
= ⨅ i, monomialThreshold (d i)(k i)(h i)` (rlctAt, deepest=0 — replaces the old false full-loss form);
`resolution_charts_case111` realigned to it, STILL axiom-free (the genuine M=(1,1,1) instance). Only declared
axioms in-tree: `monomial_rlct` (S2) + `opaque rlctOrderAt` (θ-seam). 5 sorries, all in Skeleton (the rungs).

**Measure engines all axiom-clean** (verified by explicit build + #print axioms): Fubini `_aux` (S1.5),
G5-step `g5_flat_cover` (#52), `rlctAt_mono`, `product_min_rlct` (#56), `product_min_rlct_of_ne` (#57).

**R1 design COMPLETE — (2,2,2) deeper-point pin RESOLVED (pp + decorrelated Codex, identical):** the δ-pivot
chart's "unit" U=ξ²+η²+(bξ+r)²+(bη+s)² is a nondeg smooth-4-block (Hessian det 16) vanishing EXACTLY at
{ξ=η=r=s=0} = the deeper stratum **B=0** (fm SPECIFY-catch, chart-exact §8 caveat). Route = **STEP-3
sub-blowup** (option b); the δ-pivot was never a leaf — its 4 step-3 children ARE part of the **stable 24-leaf
set** (8 unit d=2, k=![1,1], h=![3,2] + 16 block d=3, k=![1,1,1], h=![3,2,3], all RHS 3/2; ⨅=3/2=lambdaCore(2,2,2),
θ=1). **Soundness DISCHARGED:** deeper stratum B=0 has codim 4 > minMval 3 ⟹ its exceptional ratio 2 > binding
3/2 ⟹ NEVER binds — chart-exact form of "centers=admissible strata, no center beats min". Full Jac = **α³·ρ²**
(α³ = step-1 A-blowup). Durable in r1-222-cover card §δ-CHART-DEEPER-POINT-PIN + §δ-BRANCH-BUILD-ROUTE-FORK.

**Route-fork adjudicated (controller call):** the product_min-skip route is SOUND (shear unimodular even with
b free; rlct(U)=2; positivity-OK) but **heavier** — it needs a NEW weighted-product-split lemma (because #56
is **TRIVIAL-weight** and the δ-leaf carries the α³ρ² Jacobian). step-3 is lighter for (2,2,2) (uniform monomial
machinery, no new lemma). The weighted-split is a reusable **general-M down-payment** → **DEFERRED** (general-M
gated on G3 = roadmapped, not the active target). ⟹ build (2,2,2) δ-branch via step-3; #56 serves trivial-weight
call-sites only ((2,1,2) #55 TBC).

**Green-gate GAP found + fixing:** `lake build DLNFibre` builds only the aggregator's closure → not-yet-consumed
engines (S1ProductMin #56, S1G5 #52, ParamsFlat) escaped it (caught via "S1ProductMin.olean does not exist" on
axiom-check). Built them explicitly (green; #56 axiom-clean). fm to (a) import stable engines into the aggregator
+ (b) restore AxCheck.lean. Lesson banked. "Green build" ≠ "every module compiles."

**Since the milestone (trunk now @930a6a0, all pushed):** rv-2 AUDIT **PASS** on @1304cf2 (S1.5 wire / re-scope /
case111 — decorrelated, validated the min-on-core + n/2-via-Fubini decomposition). **Green-gate gap CLOSED**
(@73c52f9 + @930a6a0): all 9 measure engines now imported by the aggregator + **AxCheck.lean restored**
(emits `#print axioms` every build — 5 results clean, headline sorryAx). **#57** `product_min_rlct_of_ne`
gated @2e8dc4c. **#58** pivot-blow-up atom gated @930a6a0 (pivotBlowup/Deriv/_det=(x 0)^n/_injOn, parametric
n — serves all 3 (2,2,2) blow-up nodes). Lesson banked: green `lake build <lib>` covers only the aggregator
closure (orphan engines escape).

**Active (trunk @536740b; LADDER 2/3 — (1,1,1) + (2,1,2) DONE + axiom-free):**
- **(2,1,2) #55 — DONE @536740b, axiom-free.** `case212_rlct = [propext, Classical.choice, Quot.sound]` (AxCheck);
  6→0: product-MIN heart (`product_min_rlct`), both block-RLCT bridges (EuclideanSpace↔Pi via
  `PiLp.volume_preserving_toLp`, in-seat), coord-split (the (1,1,1)-`entryME` pattern), `prod212_entry`
  (lean-formaliser). Merged + aggregator/AxCheck-wired. rv-2 auditing. Audits PASS so far: milestone/#58/#61/#52.
- **(2,2,2) #54** — fm-2, on flat `Fin 8→ℝ` (carrier **FORCED**: product `(Fin4→ℝ)²` lacks `IsAddHaarMeasure`).
  Node toolkit done/near: #58 (C¹/det/InjOn full-block), #61 (argmax cover), #64 (spectator), #65 (hmeas),
  #67 (argmaxCellOn flat-subset cover) — all gated; + `pivotBlowupOn` det (fm-2's +91 WIP, green+sorry-free,
  gating pending fm-2's confirm) → **#69 g5_pivotNode** (single reusable node, in progress). **#68 per-leaf
  VALUE lemmas DONE (fm half of #54).** REMAINING: pivotNode → 24-leaf 3-deep assembly (+ φ_L2 splice) + the
  **#66 seam** — route (ii): fm-2's OWN explicit m.p. `Params≃ᵐFin8` via `piCongrLeft` + an explicit a00..b11
  bijection (order pinned by construction, sidesteps the noncomputable equivFin). **Measure-instance verify-first
  flagged:** the piCongrLeft m.p. must land on Params's *actual* MeasureSpace instance (= rlctAtOn's), via the
  generic reindex lemma — not a parallel canonical-Pi measure. rv-2 audits the seam (the silent-hole point).
- **Case222 wrapper** (fm) — thin (2,2,2) validate headline, gated on #54's result. **pp** on-demand.
**Roadmapped (operator-gated scope):** G3 (general-M wall), #19 keystone (#37/#45/#46), weighted-product-split
(general-M). **Fixed-M ladder = active target: (1,1,1) DONE · (2,1,2) DONE · (2,2,2) #54 (the last rung).**

## Prior read (2026-06-20): ★ CONTRACT IS BEDROCK @296d3e4 — structural-proof phase OPEN ★

**rv-2 FINAL re-audit @`296d3e4` CLEAN → BEDROCK DECLARED.** The 9-issue fidelity arc is CLOSED. The contract
is genuine bedrock: domain PROVABLY complete (hr middle-width + hL L=0, systematic corner sweep proved no
10th hole), keystone clean, A1-clean + L1 genuinely proven (no sorryAx, not vacuous), headline assembles
axiom-clean through D1▸L2, S2 the ONLY citation (no leak), every rung name=content/non-vacuous. `git diff
2ee02b2 296d3e4` is hL-ONLY (zero drift). The rock the structural proofs now stand on.

The 9 issues (all caught by proof-attempts/decorrelated checks BEFORE anything built on them, all fixed):
6 in the original adversarial pass (L1 vacuous, L2 over-claim, D1 under-claim, S1.1 measure, R1 analyticity,
S1.5 analyticity); 7th deepestPoint false (middle-width) → hr; 8th lambdaCore weak existential → strengthen
(#19, sequenced); 9th deepestPoint false (L=0) → hL. Two sweeps closed the vacuity + domain classes wholesale.

Two honest residuals (NOT bedrock defects — off the criterion): deepestPoint_exists is a `sorry` (fm
mid-proof — a PROOF obligation, not a statement defect); A1 lambdaCore (#19) + A2 weak existentials (flagged,
off the headline path, strengthen sequenced).

### Earlier status (pre-bedrock, retained for the arc):
Two structural rungs landed during the contract phase. Honest status:

**Landed / green:**
- **Keystone `paramsEquivFlat`** (`Params H ≃ᵐ (Fin N → ℝ)`, measure-preserving) — fm-2 @`d7b1ba3`
  (Route A++). **rv-2 PASS (bedrock-clean):** isolated `/tmp` green-gate (2851 jobs, no shared-tree race),
  ParamsFlat ZERO sorries, axioms `[propext, Classical.choice, Quot.sound]` (no sorryAx/stray), NO leaked
  global instance (threads by `rfl`; bare `Matrix` still has no MeasurableSpace), flatDim correct by decide.
  Unblocks the (1,1,1) bridge, S1.1's use-site, R1's measure facts. (Nit: unused `forall_true_left` in
  `measurePreserving_piCurry` — fm-2 cleans on next touch.)
- **A1 `clean_eq_printed`** — fm, committed @`c234651` (genuine ℚ identity, rv-2 9324-case verified). KEEP.
- **A1 `lambdaCore_eq_clean`** — fm, committed @`f8233f2` (worktree-rung0-defs, sorry 13→11) — but it's the
  **WEAK existential (8th fidelity issue)**: closed by FREE CHOICE (ℓ=1, m=![1,(min Mval).toNat], needs only
  min≥0) — proves NOTHING about M, NOT Aoyagi Lemma 3. fm flagged it (good). DECISION: strengthen to genuine
  Lemma 3 (lambdaCore M = clean form at Def-3-selected widths, m BOUND to M; ~200-line balanced-split
  exchange). OFF the headline critical path (headline uses aoyagiLambda directly) ⇒ SEQUENCED after L1; weak
  proof KEPT with loud docstring flag as honest interim. pp DELIVERED the genuine statement (card
  `threads/14-r1-design/a1-statement-card.md`): `∃ ℓ ∈ {1..L}, lambdaCore M = cleanCore ℓ (sortedSmallest M ℓ)`
  — `m` PINNED to M's ℓ+1 smallest reduced widths (genuine: forced by (M,ℓ)). ⚠️ NOT an extremum: `min_ℓ`
  AND `max_ℓ` are BOTH FALSE (pp refuted Codex's "cleanest" via M=[1,1,4] / [2,2,2]) — formaliser must keep
  the `∃ℓ`. Verified 1360/1360. fm formalizes #19 (replace weak stmt+proof) AFTER deepestPoint_exists (off
  critical path). Def-3 sidestepped entirely.
- **L1 `block_elimination`** — fm @`fb65243` (worktree-rung0-defs), GENUINE explicit block-normal form (not
  the vacuous rank claim), ~220 lines via adapted-basis (`Basis.sumQuot` + `basis_toMatrix_…`). sorry 10→9.

**Weak-existential sweep (rv-2, complete):** exactly 2 weak rungs — A1 `lambdaCore_eq_clean` + A2
`aoyagiTheta_eq` (both on the fix list). L1, deepestPoint_exists, R1 GENUINE. Discriminator banked (lessons):
`∃ x, LHS(data)=f(x)` is WEAK iff f free-covers a CONCRETE LHS (x choosable free of data), GENUINE iff the
LHS is OPAQUE/pinned (witness must encode data). R1 genuine despite A1-shape (rlctAt = opaque sSup). No
surprises lurking — fidelity class fully catalogued.

**The 7th bug (caught by fm's proof attempt, MISSED by the bedrock audit):** `deepestPoint_exists`
(`Nonempty {w // IsDeepLayers H r B w}` under `hB : B.rank = r` ALONE) is FALSE — H=(3,1,3), r=2,
B=diag(1,1,0): the MIDDLE width H 1=1 bottlenecks the product to rank ≤1<2 ⇒ empty fibre ⇒ Nonempty FALSE.
The HEADLINE is then false too (⨅ over ∅ = ⊤ ≠ finite). Root cause: "rank B=r ⟹ r≤H s" holds only for the
OUTER widths. **Fix (decided): add `(hr : ∀ s : Fin (L+1), r ≤ H s)`** to deepestPoint_exists + deepestPoint
+ deepestPoint_isDeep + product_reduction + deepest_point_reduction + aoyagi_learning_coefficient. It is also
the well-definedness domain of `aoyagiLambda` (M⁽ˢ⁾=H⁽ˢ⁾−r needs r≤H⁽ˢ⁾). **FIXED + MERGED @`2ee02b2`** (hr
threaded through all 6 decls, headline assembles, deepestPoint_exists kept as sorry under new sig; contract
now TRUE, no empty-fibre ⊤). 7th bug closed. **9th issue (L=0 corner):** even WITH hr, false for L=0 (empty
product = identity ⟹ fibre needs B=I; `L=0,H=![2],r=0` has hr✓ but empty fibre) → fix `(hL : 1 ≤ L)`
(L=0 = no network = out-of-model; verified sufficient 484/484). Same DOMAIN-UNDER-SPECIFICATION class as the
7th. fm applying hL + proving deepestPoint_exists (one pass, then I merge). rv-2 commissioned a SYSTEMATIC
DOMAIN-CORNER SWEEP (catch the domain-hole class wholesale, like the weak-existential sweep) + HOLDS the
final contract PASS until hr+hL merges + sweep clean. (Fidelity-issue tally: 9 — all caught before proofs
build on them; the contract is converging to genuine bedrock.)

**rv-2 re-audit @2ee02b2 + DOMAIN-CORNER SWEEP (done):** hr-fix PASS (build green 2851, 10 sorry, axioms
clean, witness CONSTRUCTED for (1,1,1)/r=0 per the standing rule; A1/L1 genuinely proven, no sorryAx; L1 not
vacuous). 9th bug (L=0) INDEPENDENTLY confirmed (decorrelated counterexample). **Sweep result: NO further
hidden corner beyond L=0 — `hr ∧ hL` CLOSE the existence/headline domain COMPLETELY** (r=0→origin OK;
hr-equality boundary OK; only L=0 uncovered). ⇒ once hL lands + the final re-audit runs, the contract domain
is PROVABLY complete (no 10th domain hole lurking) = BEDROCK. The domain-bug class is closed.
Full rung×corner matrix (rv-2): R1 `resolution_charts` is SAFE at L=0 with NO hr/hL (the ONE unguarded
rung — at L=0 dlnLoss is constant ⇒ `rlctAt=⊤` either way, R1's ∃ discharges via `ι=Empty`, ⨅∅=⊤); all
other rungs (S2/S1.x/L1/A1/A2) clean at every corner (L=0, r=0, r-extremal, zero-width, d=0). So R1 needs
NO domain hypothesis — good for its formalisation. **Convention noted:** `rlctAt(≡0 loss)=⊤` in this dev
(rv-2 proved it; literature leaves F≢0's RLCT undefined) — BENIGN (the ≡0 case only at hL/analyticity-
excluded corners; the headline's rlctAt is for a non-≡0 loss, vanishing AT the deepest point not identically,
so the convention never taints the headline). Docstring note on `rlctAt` queued for convention-honesty.

## Live status (per-track)

- **fm-2 (measure track)** — keystone (d7b1ba3) + bridge (b342cd2, axiom-free) + continuity-to-ParamsFlat
  (fb50adc) ALL DONE; measure track COMPLETE. **NOW on the real S1.1 `weightedThreshold_transport`** (heavy
  transport rung; infra banked: continuity homeomorphism + 2-sided box-iff + sSup). Then the deepestPoint r>0
  telescoping (dependent-Fin, routed here post-S1.1). Commits to expedition; rv-2 green-gates behind. Trunk
  @`fb50adc`.
- **fm (algebra track)** — branch `worktree-rung0-defs` (Skeleton-only), based @1bb9e31 (I merge forward;
  no rebase needed — Skeleton independent of keystone). A1-clean + A1-lambdaCore(weak) + L1 + hr-fix DONE +
  MERGED @`2ee02b2`. NOW on `deepestPoint_exists` PROOF (reuses L1 adapted-basis) → then #19 lambdaCore-
  strengthen (waits for pp's genuine statement). **Trunk @`296d3e4`: keystone + A1 + L1 + hr + hL; Skeleton
  sorry 9.** hL MERGED; rv-2 running the FINAL bedrock re-audit (domain now provably complete → closes the
  9-issue fidelity arc). **deepestPoint_exists FULLY PROVEN + MERGED @`9402bba`** (axiom-clean, no sorryAx;
  the r>0 prodAux telescoping CLOSED — fm de-risked the algebra + delegated the HEq cast-wrangling to a
  formaliser + reviewer subagent; statement byte-identical; rv-2 re-auditing). Critical-path rung DONE (feeds
  D1). Skeleton sorry 10→9. **fm now on #19 proof** (genuine lambdaCore, ~200-line balanced-split exchange).
- **pp (design)** — R1 design DELIVERED + 2 increments (binding-divisor correction; value-match downgrade).
  Standing down on-demand; re-engage for R1 value-match execution when fm's L1 lands.
- **rv-2 (review)** — green-gating keystone d7b1ba3; queued: re-audit the hr-corrected contract. Decorrelated.

## Integration topology (current)
expedition/aoyagi-full = integration trunk (fm-2 commits here directly). worktree-rung0-defs = fm's Skeleton
branch (I merge → expedition). Files DISJOINT (fm-2: ParamsFlat/Case111; fm: Skeleton) — contract change is
Skeleton-LOCAL (verified: no refs to deepestPoint/headline/L2/D1 outside Skeleton). Merges are clean. MAIN
working tree has no Lean WIP between fm-2 commits. Controller green-gates via rv-2 (isolated builds) to avoid
the shared-tree build race.

## PROOF-MODULE PATTERN (S1.1+) — eliminates Skeleton contention
Heavy rungs that are Skeleton sorries are proven STANDALONE in Foundations modules, then I WIRE each into
Skeleton single-writer (`exact <lemma> …`, verbatim statement). S1.1 `weightedThreshold_transport` →
`Foundations/S1Transport.lean` (fm-2, option B approved); S1.3/4/5 likewise if fm-2 takes them. Result: fm
owns Skeleton's INLINE rungs (deepestPoint, #19 lambdaCore); fm-2 owns Foundations PROOF-modules; I do the
1-line Skeleton wires at integration. Zero fm↔fm-2 Skeleton collision + it's the per-rung modular split
(build-time), done as-needed rather than big-bang. The wired lemma's statement must match Skeleton's verbatim.
**Refinements (rv-2 full-trunk catch @92a1101):** (1) the proof-module lemma gets a DISTINCT name (`_aux`/
`_impl`) — same FQN as the Skeleton contract decl = duplicate-declaration landmine at wire-in; wire =
`Skeleton.<rung> := <rung>_aux …` (verbatim statement still unifies). (2) a Foundations proof-module is
ORPHANED from the root `DLNFibre.lean` closure until wired (Skeleton imports it) — so the DEFAULT
`lake build DLNFibre` SKIPS it (gate WIP via explicit module-builds; `scripts/sorries` globs so counts it,
but the root build doesn't compile it). The FULL-trunk `lake build DLNFibre` (not module-scoped) is the gate
that catches orphans + collisions — run it at integration, not just the module build.

## 10th fidelity issue — S1.1 bare equality FALSE (analytic-implication gap; fm-2 caught @6dbc880)
The bare-hypothesis Skeleton `weightedThreshold_transport` EQUALITY is FALSE — the reverse `≥` fails two ways:
(1) **surjectivity gap** (w*∉range π ⟹ π⁻¹{w*}=∅ ⟹ RHS=⊤≠finite LHS) → needs `hsurj : Surjective π`;
(2) **Luzin-N gap** (hderiv off-E doesn't make π(E) null; a Cantor-staircase π sends null E→positive π(E), an
F-singularity there adds LHS mass the off-E CoV misses) → needs `hImE : volume (π''E)=0`. The Skeleton
docstring ASSUMED "π(E) null via Luzin-N" but the hyps don't encode it (Mathlib Luzin-N needs DifferentiableOn
ℝ π E). **NEW CLASS** — not a domain-corner (the sweep cleared S1.1's corners) but an analytic-IMPLICATION gap
(hyps don't imply the conclusion), only the proof attempt surfaces it — even on the IsAddHaarMeasure-pinned
statement. fm-2 ESCALATED (didn't silently fix) + delivered both sorry-free: `weightedThreshold_le_transport`
(unconditional ≤) + `weightedThreshold_transport_of_surjective_image_null` (full = under hsurj+hImE, conclusion
defeq Skeleton). FIX: add hsurj+hImE to Skeleton S1.1 (LOCALIZED — doesn't ripple to D1/L2/R1 statements, which
don't expose π; their PROOFS supply the hyps, both hold at the R1 resolution use-site: chart surjective +
exceptional divisor null). Pending rv-2 decorrelated confirm (7th/9th protocol) → fm wires
(`exact …_of_surjective_image_null` + import + the 2 hyps, Skeleton single-writer). R1 design note: R1's
per-chart S1.1-transport invocation must supply hsurj (chart onto nbhd) + hImE (exceptional divisor null).
**rv-2 CONFIRMED (decorrelated + Codex)** both gaps (π=exp surjectivity; π=id+Cantor-staircase Luzin-N) +
fm-2's 2 lemmas PASS; Codex Q3 resolved (hsurj+hImE COMPLETE, no 4th gap). Executing: fm wires S1.1 (+ S1.4).

## S1 batch status (proof-module pattern, fm-2 owned modules → fm wires)
- **S1.1** `weightedThreshold_transport_aux` (S1Transport.lean @20ab62a) — PROVEN under hsurj+hImE (10th issue,
  CONFIRMED). fm wiring (add 2 hyps + `exact` + import; also resolves orphan FLAG 1).
- **S1.4** `rlct_germ_local_aux` (S1Local.lean) — PROVEN, bare statement SOUND (no gap). fm wiring (`exact` + import).
- **S1.3** `rlct_unit_invariant` — **11th fidelity issue:** bare statement FALSE without `Measurable u`
  (non-measurable u → u·F non-measurable → not Integrable → rlctAt=sSup∅=0 ≠ rlctAt F). Fix `Measurable u`
  **rv-2 CONFIRMED** (decorrelated + Codex; Vitali-set counterexample, `IntegrableOn⟹AEStronglyMeasurable`
  crux Lean-verified). `AEMeasurable u` is the minimal hyp but `Measurable u` is the contract choice (cleaner,
  use-site-safe — analytic unit continuous). fm-2 PROVEN `rlct_unit_invariant_aux` under it (S1Local.lean,
  axiom-clean); fm wires (add Measurable u + exact). **All 3 S1 _aux ready to wire: S1.1/S1.4/S1.3** (fm batch).
- **S1.5** `rlct_additive_smooth_block` — **12th fidelity issue (DEEPER):** the disjoint-block additivity is
  FALSE two ways (non-measurable G [gap-class]; G≡0 ⟹ rlctAtOn(0²)=⊤ ⟹ RHS=n/2+⊤=⊤≠LHS [≡0-convention]) AND,
  even fixed, needs heavy Laplace-asymptotic machinery (Mathlib-gap); can't be cited. fm-2 delivered the honest
  substrate @`2cb79cc` (sorry-free: `rlctAtOn_zero_eq_top` [also discharges #24 docstring], `smoothBlock1D_rlct`
  n=1; the false aux NOT carried as a sorry). rv-2 confirming the counterexamples. **L2-ARCHITECTURE STRATEGY
  routed to pp** (additivity-with-hyps vs R1-on-full-loss-subsumed vs smooth-block-alone restatement — how L2
  combines regular ⊕ core). fm-2 proving the smooth-block VALUE `rlctAtOn(Σxᵢ²)=n/2` (general n, needed
  regardless; Mathlib-gap radial integrability). This is a design node, not just a hyp-gap.
  **RESOLVED (pp + Codex, l2-architecture-card):** DROP additivity AND R1-on-full-loss (the latter needs mixed
  principalization of (x,m) — heavier; F=Σx²+core is a SUM not monomial×unit). **Restate S1.5 to the
  smooth-block FUBINI LEMMA:** `rlctAt(Σxᵢ² + core)` in a core normal-crossing chart `= n/2 + min_j(h_j+1)/(2k_j)`.
  PROOF LIGHT (no Laplace): `∫(|x|²+s)^{-c}dx = C·s^{n/2-c}` (radial x=√s·ρ, Beta, finite iff c>n/2) + Fubini
  (s=core≥0) ⟹ core RLCT at shifted exponent ⟹ n/2 + λ_core. Chart-form core=monomial is nonzero-a.e. +
  measurable ⟹ dodges BOTH gaps by construction. APPLIED PER-CHART in R1: λ_full = min_chart(n/2 + λ_core) =
  n/2 + ½ min_t Mval. So L2's regular⊕core = Fubini-lemma + R1-core-resolution + min-over-charts (NOT a
  standalone additivity). fm-2 proving the Fubini lemma; fm restates+wires Skeleton S1.5.
  **Fubini ROUTE (fm-2's call):** the smooth-block case is genuinely CLOSED-FORM (NOT Laplace — Laplace only
  for general both-arbitrary additivity, not ours). Route B (iterated-1D: n=1 Fubini `∫(x²+s)^{-c}=C·s^{1/2-c}`
  iterated, stays on Params-flat product measure) likely cleaner than Route A (radial via
  `integrable_fun_norm_addHaar` [Mathlib HAS it, corrects the earlier gap-flag] + EuclideanSpace-Haar bridge).
  **UPDATE: general-n single-block n/2 PROVEN** (`smoothBlockND_rlct` rlctAtOn(Σxᵢ²)=n/2 on EuclideanSpace,
  S1SmoothBlock.lean @505e0a2, axiom-clean, 201 LoC — the Mathlib-gap was NOT real, radial `integrable_fun_norm_addHaar`
  + ball-truncation + rpow-iff). The FUBINI lemma (the +core combination = n/2+λ_core) is the s>0 EXTENSION of
  that radial machinery (`∫(‖x‖²+s)^{-c}=C·s^{n/2-c}`, Fubini, + monomial-core threshold) — CLOSED-FORM (NOT
  Laplace), in flight (fm-2). S1.3 also PROVEN + ON TRUNK now (S1Local 0-sorry @505e0a2).
  **FUBINI DE-RISK (fm-2 SPECIFY + Codex):** the exact radial identity holds ONLY at ε=∞; finite-ε (RLCT nbhd)
  is asymptotic-only + Mathlib has NO parametric radial integral. So directions SPLIT: ">=/integrability LIGHT"
  (a.e. comparison + Integrable.mul_prod + radial_ball_iff, ~4-6 sublemmas); "<=/non-integrability" (the CUSP
  lower bound — pp re-adjudication SHAVED to ~5-7 sublemmas via EXACT ball-volume `vol{‖x‖²≤s}=V_n·s^{n/2}`
  [measure_ball/addHaar_ball — NOT a parametric radial integral, dodges the gap]; monomial divergence finish).
  **≥ DIRECTION DONE (fm-2, S1Fubini.lean, 110 LoC, axiom-clean, module-green 2676):** `cmpF` (split engine
  `(s+t)^{-(a+b)}≤s^{-a}t^{-b}`) + `joint_integrableOn_weighted` (a.e. cmpF comparison + Integrable.mul_prod +
  volume_eq_prod). rv-2 PASS (#40, axiom-clean, right condition, hGne faithful). Off-Skeleton; controller wires
  into the aggregator at the equality. **≤ DIRECTION fully de-risked** (every atom + Step A `[‖x‖²≤G](2G)^{-c}w ≤
  |F|^{-c}w` handling BOTH G>0 antitone + G=0 hygiene-corner, cuspVol exact `vol{‖x‖²≤s}=ofReal(√s^n)·Vₙ`,
  notIntegrable_rpow, joint_lintegral_top sig — all in scratch; remaining = mechanical Tonelli + factor +
  hcore_top⟹⊤). **STATEMENT-SHAPE DECISION (load-bearing, supersedes the (i)-vs-(ii) routing Q AND the card §B
  "explicit monomial core"): (A) ABSTRACT-CORE SHIFT THEOREM.** fm-2 found the standalone multivar monomial
  divergence `∫_box ∏|y_j|^{a_j}=⊤` is NOT the ~30-LoC elementary fact first estimated — Mathlib has the pi-product
  factorization only for the FINITE/integrable case, not a lintegral=⊤ divergence (custom pi-Tonelli = heavy).
  So BOTH the standalone build (heavy) and S2-reuse (axiom-import) are dodged by stating S1Fubini ABSTRACTLY:
  `rlctAt(Σxᵢ² + core) = n/2 + rlctAt(core)` — the pure "+Σx² shifts the RLCT by exactly n/2" shift theorem, with
  the core's integrability (≥, hGne+hy) and divergence-at-shifted-exponent (≤, hcore_top) as EXPLICIT hypotheses
  (symmetric, honest, dodge both 12th-finding levers by construction). The monomial+S2 obligation MOVES to R1's
  per-chart use-site: R1 supplies rlctAt(core)=S2's ⨅axisRatio for its resolved monomial, and hcore_top follows
  from that value by the sSup definition (NO hand-built multivar integral). Strictly cleaner — S1Fubini stays
  axiom-clean + monomial-machinery-free, the shift is its sole content, and S2 lands exactly where it belongs
  (the monomial RLCT). pp confirming the R1 use-site discharge (3 hyps + cover-composition) in parallel. **λ_core=0
  EDGE (rv-2):** the c=a+b split (b>0) covers c<n/2+λ_core only for λ_core>0; the λ_core=0 regime routes through
  `smoothBlockND_rlct` (=n/2) directly — fm-2 handles in the equality-lift (likely vacuous at the deepest point
  where the core is genuinely singular, but kept general). The <= IS NEEDED (R1 UPPER = binding-chart divergence;
  S2 alone doesn't cover the SUM Σx²+monomial — +Σx² shrinks the integrand so divergence is non-trivial). So R1
  is heavier than first scoped (Fubini-per-chart + multiplicity-control R1.2 + cover R1.6) but all designed +
  tractable, and the abstract shift makes the Fubini-per-chart step a clean plug-in.
**Use-site obligation (tracked):** hsurj+hImE (S1.1) + Measurable u (S1.3) must discharge at D1/R1 (resolution
charts: surjective onto nbhd, exceptional-image null, analytic unit measurable). The bare-under-specification
gap-class is RECURRING across the analytic rungs — caught reliably by the proof attempts + escalation.

## R1 design BANKED (pp, thread 14) + R3b DECISION + value-match DOWNGRADE
- **Value/atlas split.** VALUE `rlctAt(‖∏C‖²)=½·min_t Mval(t)` (pinned by codim S(t)=Mval, thread-03) vs
  explicit CHART ATLAS (Aoyagi affine blow-ups).
- **Binding-divisor mechanism** (pp self-corrected the wrong "telescoping" framing): per branch, ONE blow-up
  of the residual-block-zero center (codim EXACTLY Mval(t)) is the binding divisor (k,h)=(1,Mval−1), ratio
  ½·Mval; min over branches = ½ min_t Mval = λ. (Telescoping per-rank-drop would give ½·min(cᵢ) = TOO SMALL.)
- **VALUE-MATCH DOWNGRADE (pp §8, verified L=3):** the headline's value-match does NOT need the full atlas —
  only the minimizing branch's binding divisor, produced by **iterated L1 to the residual block (REUSES fm's
  L1 + deepestPoint_exists machinery)**. Route: (i) iterate L1 → codim-Mval residual block; (ii) residual =
  codim-Mval coord subspace (thread-03); (iii) blow up → divisor-ratio lemma → ratio ½·Mval [UPPER bound,
  L1-reuse, cheap]; (iv) cover/exhaustiveness inequality over strata [LOWER bound, the residual real work].
  Full normal-crossing atlas DEFERRED (only to strengthen the statement beyond value-level). R1's "mountain"
  status partly downgraded.
- **Residual-block claim NAILED (pp §8, general-L; verified L=2,3,4 + decorrelated Codex):** after the
  pivot split, the residual cutting S(t) is a REGULAR SEQUENCE of length EXACTLY Mval(t) — not
  over-determined (the full interval rank-pattern r_{ab}, a≥2, adds NO independent generators; inner
  constraints are CONSEQUENCES), not coarser. So {residual=0} is a clean smooth codim-Mval(t) coordinate
  subspace ⇒ binding divisor (k,h)=(1,Mval−1), ratio ½·Mval(t), rigorous at general L. STRUCTURE: the
  residual is NESTED Schur-blocks R₁..R_L (R_j = D_j−C_jA_j⁻¹B_j per layer), `S(t)∩chart = {R₁=…=R_L=0}`,
  Σ|R_j|=Mval — jointly coordinates ⇒ one smooth center. CAUTION: a final-PRODUCT residual alone cuts the
  COARSER {∏=0} (union over profiles), NOT S(t) — must use ALL R_j. CAVEAT (Codex): ratio ½·Mval holds at a
  GENERIC point of the minimizing stratum (nongeneric suffix-vanishing points need more blow-ups but don't
  affect the value-match). pp self-caught + dropped a wrong "inner intervals stay generic" sub-claim (what
  holds is codim=Mval exactly, which is all the mechanism needs).
- **Codex correction adopted:** prefix-stratum partition right for the VALUE but too coarse for a literal
  atlas (charts refine by full rank-pattern); R1↔Adm is VALUE-level, NOT a chart bijection.
- **R1 LOWER BOUND + complete decomposition (pp, done) — MULTIPLICITY-CONTROL finding (pre-execution catch):**
  UPPER (≤ ½ min Mval) = ONE binding-divisor chart (cheap, L1-reuse). LOWER (≥ ½ min Mval) needs the FULL
  cover + a sharp finding: **the lower bound CANNOT come from codim alone** — the divisor ratio `(h_E+1)/(2k_E)`
  depends on F's VANISHING ORDER k_E, not codim (counterexamples: `rlctAt(x^{2k})=1/(2k)<½·codim`; `(x²+y²)²`:
  1/2≠1). So **R1.2 = MULTIPLICITY CONTROL** (`h_E+1 ≥ k_E·min Mval` per divisor), HOLDS for our core via
  regular-sequences⟹k_E=1 but PROVEN per-divisor, NOT a codim shortcut. DECOMPOSITION (execution-ready): R1.1
  chart family[L1] + R1.2 multiplicity[NEW] + R1.3 codim=Mval[thread-03] + R1.4 Fubini-per-chart + R1.5
  S1.1-min-over-cover + R1.6 cover/exhaustiveness[NEW] + R1.7 S2. NEW lifts = R1.2 + R1.6 (the real lower-bound
  work). Route: complete explicit resolution + per-divisor monomial check (one-citation-clean); SoS+codim DEAD.
  Subtleties: strata-not-components (Z=⋃S(t)); local-vs-global codim (origin sees min Mval); properness (w/ S1.1).
  pp+fm EXECUTE when S1.1+Fubini land (close); R1.2 first.
- **DECISION R3b** (self-contained, one-citation). R3a (cite LR `rlct=codim/2`, arXiv:2411.19920) OUT:
  violates one-citation scope (codim = THE new content) + Aoyagi-independence. Surfaced to operator as
  informational/override-able.
- **No hidden hypotheses** (Codex §4): char-0, positive widths, r≤H s (=the hr fix). Toric/Newton route DEAD.

## WIN — λ-citation ELIMINABLE — now DEMONSTRATED END-TO-END (bridge @`b342cd2`)
The (1,1,1) bridge `case111_rlct_eq_monomialThreshold` is CLOSED sorry-free (fm-2) ⇒ **`case111_rlct` is the
FIRST fully sorry-free + axiom-free end-to-end RLCT result** (`#print axioms = [propext, Classical.choice,
Quot.sound]`, NO sorryAx, NO monomial_rlct, NO native_decide). So λ is PROVABLY axiom-free for (1,1,1) — the
WIN is no longer just probed, it's demonstrated. General case = labour (no wall). Reviewer-agent fidelity
survived; rv-2 green-gating decorrelated. **Banked REUSABLE S1.1 infra (general in H):**
`continuous_paramsEquivFlat`/`_symm` (flattening is a HOMEOMORPHISM), `prod_paramsEquivFlat` (coord-product
preserved), `prodBoxSymm_rpow_integrableOn_iff` (2D 𝓝0 box-iff) — feeds the real S1.1 + R1. Only θ-order
stays the genuine analytic seam (S2 order-half).

## #19 genuine A1 statement — MERGED to trunk @`7986597`, rv-2 PASS, GREEN
Weak free-choice existential REPLACED by pp's candidate-d: `∃ c ≤ L, 1 ≤ c ∧ lambdaCore M = cleanCore c
(sortedSmallest M c)` (m PINNED via `sortedSmallest` = M's c+1 smallest reduced widths). **rv-2 PASS** (genuine
per discriminator; matches pp's ACHIEVER, NOT an extremum — verified 19600 cases, min_c/max_c refutations
reproduced; sortedSmallest faithful). 8th issue resolved at the STATEMENT level on trunk. Skeleton compiles
green (2534 jobs). Proof = sorry (~200-line balanced-split exchange, off-critical-path) — fm sinking it next
(gate OPEN). **Skeleton sorry 9→10 — correct + honest: a genuine sorry replaced the vacuous weak PROOF.**
Also merged: deepestPoint r=0 + Dblock_rank (r>0 telescoping still sorry, fm's). Cosmetic lints in fm's code
(show→change @534, deprecated Finset lemma @706, <;> @738) — non-blocking, fm cleans on next touch.
**#19 PROOF progress:** Step 1 `balancedSplit_min` PROVEN (balanced split minimises Σq²; e9e251d, reusable).
ROUTE-GAP found (proof attempt, again): card step-3 "per-c lower bound" was the FALSE `min_c` reading
(cleanCore NOT monotone in widths — `[1,2,4]`vs`[1,2,7]`: 2 vs −2; min_c/max_c refuted) — STATEMENT still
correct+total, only the ROUTE needs reframing to: per-T bound on T's OWN breakpoint widths (via balancedSplit_min)
+ **PERM-INVARIANCE of lambdaCore** (`lambdaCore M = lambdaCore M∘σ`, ~200-line Adm-cone exchange) + sorted-M.
#19 OFF the headline path — fm doing the S1 WIRES (S1.1/S1.3/S1.4, critical-path) FIRST.
**#19 keystone PARKED (decision d):** fm probed it — perm-invariance of lambdaCore is a MIN-LEVEL no-bijection
wall (Adm cones + Mval-multisets genuinely DIFFER under σ — 560/1700 & 1140/1700; holds only AT the min ⟹
multi-hundred-line explicit minimizer characterization, no slick transport). OFF-headline-path (headline uses
aoyagiLambda's min-def, closes sorry-free WITHOUT #19's proof). **THEN UN-PARKED via ROUTE B (fm, 2df8bf4):**
cleanCore depends only on the width MULTISET (Σm², Σm symmetric), so #19 needs NO global perm-invariance — a
LOCAL achiever analysis (T* breakpoint-multiset = sortedSmallest, via multiset-symmetry) + the per-T lower
bound (balancedSplit_min, DONE) suffices. ~200 lines, perm-invariance-FREE (avoids the wall, not solves it),
3900/3900. **pp VALIDATED + reframed (a1-route-reframe.md):** perm-inv = COROLLARY of the sorted-form
characterization (`lambdaCore M = lambdaCore (sort M)`), NOT proven via the Adm-cone bijection (saves the
beast). Residual hardness = the SMALLEST-WIDTHS-FORCING sub-lemma (on sorted M the minimizer's breakpoint
widths = the ℓ*+1 smallest, FORCED over every T via the `(M^S−H)` factors) — MUST be per-T-over-Adm-cone, NOT
a widths-extremum (exactly where the false min_c lived; the trap). UPPER (achiever) + LOWER (per-T
balanced-split + forcing). fm executing route B. So #19 is now a clean bounded build. fm sequence: wire
S1.1+S1.4 → #19 route B → R1/L2/D1
(critical-path beats off-path as Fubini lands for R1).

**S1 WIRES — S1.1 + S1.4 CLOSED + GREEN-GATED on trunk @`7258a36` (fm `aacdc7a`, FF-merged + full `lake build
DLNFibre` GREEN, 2855 jobs).** Skeleton sorry 10→7. Both rungs INDEPENDENTLY axiom-clean (controller `#print
axioms`): `weightedThreshold_transport` (S1.1, +hsurj+hImE [10th]) and `rlct_germ_local` (S1.4) = `[propext,
Classical.choice, Quot.sound]` — no sorryAx, no monomial_rlct. Orphan FLAG resolved for S1Transport+S1Local
(now in Skeleton's import closure). **7 remaining sorries:** S1.3 rlct_unit_invariant (138 — wire next,
Measurable u [11th] blessed + _aux proven), S1.5 rlct_additive_smooth_block (169 — awaits fm-2's Fubini lemma),
L2 (882), D1 (896), R1 (921), #19 lambdaCore (1055), A2 (1196). rv-2 auditing S1.1/S1.4 + the Fubini ≥ half.
NEXT (fm): wire S1.3 → then D1 `deepest_point_reduction`. S1Additive/S1SmoothBlock/S1Fubini stay orphans until
S1.5/L2 wire them (controller adds S1Fubini to the aggregator at that point).

**#19 CHECKPOINT (fm @`88cf38e`, worktree-rung0-defs) — ENGINES PROVEN + ROUTE CORRECTED + KEYSTONE PARKED (decision b).**
Two engines axiom-clean: `balancedSplit_min` (lower-bound engine `Σ balancedSplit² ≤ Σqᵢ²` at fixed sum;
re-derived solid after trunk syncs, `43b443e`) + `cleanCore_perm` (cleanCore multiset-symmetry, route-B crux,
`cfeec6f`). **ROUTE CORRECTED AGAIN (fidelity catch, now in the lambdaCore_eq_clean docstring):** the route-B
"per-c lower bound / min_c" framing is FALSE (M=[1,1,4]); AND Codex's first "single-c achiever rule
(aᵢ ≤ ⌈Sᵢ/i⌉)" is ALSO FALSE (278/3900 fail). The CORRECT rule (0 failures exhaustive widths 0..3 L≤4 +
3900/3900 widths 1..5): `c* = largest c with the CUMULATIVE predicate ∀1≤i≤c, aᵢ ≤ ⌈Sᵢ/i⌉` on sorted M, plus
the exact per-T identity `Mval = Σₖ gapₖ·(wₖ−Hₖ)` over strict-descent positions. **KEYSTONE PROPER = a dedicated
multi-session lift (~250-350 lines), NOT a bounded sub-thread:** two sub-lemmas on unsorted M — (1) per-T lower
bound (descent-set **dependent-Fin reparametrisation** of each T + complete-square + balancedSplit_min) +
(2) achiever construction + Adm-membership. The dependent-Fin descent reindexing is the genuine hard bulk (the
minimizer's breakpoint widths aren't literally sortedSmallest — they coincide only at c*; the "perm-invariance
wall" persists at this level). **DECISION (b): PARK the keystone, ROADMAP it** — it is WELL-SET-UP (genuine
statement + 2 engines + corrected cumulative-predicate route all banked → a dedicated tide later, after the
headline / when capacity); #19 is OFF the headline path (headline uses aoyagiLambda's min-def directly). **fm
PIVOTED to CRITICAL-PATH:** S1 wires (S1.1/S1.3/S1.4) → D1 `deepest_point_reduction` → R1 EXECUTION (with pp,
when Fubini lands) → L2 → T. Bounded #19 engine-nibbling (e.g. the per-T Mval identity) is FILL only, never over
the critical path.

**#19 ROUTE ADVANCE (fm @`85b0077`, supersedes the dependent-Fin descentSet plan — much cleaner):** the
**EDGE-VARIABLE TRANSFORM** `q_j = M⁽ʲ⁺¹⁾ + (u_j − u_{j+1})` on the FIXED level sequence — a fixed-`Fin L`
reparametrisation, NO dependent-Fin descentSet reindex (that was the hard bulk; dissolved). Exhaustively verified
(0 failures L≤4). NEW engines axiom-clean: `karamata_sq` (Karamata-for-squares via Abel summation, general/
reusable), `edge_identity` (`2·Mval = Σ(edgeQ)² − Σ(Mseq)²`), + QFeasible positional prefix bounds (Adm ⟹
QFeasible). **#19 now reduces to ONE clean gate** (in the docstring): the **smallest-k-sum majorization**
(`∀k, Σ(k smallest edgeQ) ≤ Σ(k smallest Y)` ⟹ karamata_sq). Mathlib v4.29 has NO Karamata/Schur/k-smallest API
(confirmed) ⟹ ~150-250 lines new combinatorics; proven irreducible (pointwise-after-sort FALSE q=[1,3]vs[2,2];
prefix/tail split undershoots — convexity essential). **STILL PARKED (decision b, reaffirmed 3rd time):** the gate
is a DEDICATED TIDE LATER (after the headline), even better set-up now (edge-transform + karamata_sq + QFeasible
all banked = one self-contained majorization theorem). fm REDIRECTED to the pending critical-path Skeleton tasks
(S1.3 wire + the 13th-finding restatement, which it had skipped for this #19 work) → then D1. Process note logged:
don't dispatch sub-formalisers per task (seat-reuse) + no further cycles on parked #19.

## Measure-side architecture — ROUTE A++ (DECIDED; now ACTUALLY green)
Matrix-wall paid-ONCE + contained by interface discipline. `Params.volume`=nested Measure.pi is **rfl**; fiber
instance = section-local `instance` (NOT a global Matrix instance, NOT a goal-type `letI` — elaboration order).
**Σ-form throughout via `piCurry.symm`, never `curry`/`×`** (`MeasurableEquiv.curry` has NO measurePreserving
companion in Mathlib; `piCurry` does); final reindex `Σ…≃Fin N` via `equivFin`; `measurePreserving_pi` =
piCongrRight MP, pass μ,ν explicitly. (pp corrected an earlier overclaim — it had verified type-level +
individual lemmas but the MP body was sorry'd; now the FULL body compiles EXIT=0 v4.29. Decision unaffected,
firmer.) These gotchas are REUSABLE for S1.1 + R1 measure facts. Downstream states facts on `Fin N → ℝ`, pulls
back via `integrableOn_comp_preimage` — never re-touch Matrix.

## Rung map (scoped)
- DONE: keystone paramsEquivFlat (d7b1ba3); A1 clean_eq_printed (c234651, to merge).
- NEXT (fm): hr statement-fix [contract-critical] → lambdaCore_eq_clean → L1 → deepestPoint_exists proof.
- NEXT (fm-2): (1,1,1) bridge (#12) → then S1.1 (heavy) + S1.3/4/5.
- THEN: L2 (needs L1+S1.5) · D1 (needs S1) · R1 value-match (needs L1 + S1.1; pp re-engaged) · A2 (θ-seam, post-R1).
- Assembly T: assembles from D1+L2 (+ hr threaded).
- Two hard builds remain: S1.1 + R1's cover-inequality (lower bound).

## STATUS @ 2026-06-21 ~01:30 (trunk @c32b694; Fubini @e2a3f0c)
- **S1 WIRE BATCH COMPLETE — S1.1/S1.3/S1.4 ALL CLOSED + green-gated + axiom-clean** (@c32b694; build green 2855,
  Skeleton 6 sorries; rv-2 PASS on S1.1/S1.4, S1.3 audit queued). The S1 transport/locality/unit substrate is DONE;
  only S1.5 (Fubini) remains of S1. 6 sorries: S1.5, L2, D1, R1, #19, A2.
- **R1 EXECUTION LAUNCHED** (pp leads math, fm formalises): pre-Fubini parts first — R1.1 chart construction
  (L1-reuse) + R1.2 multiplicity-control (`h_E+1 ≥ k_E·min Mval` per divisor, NOT codim shortcut); R1.4
  (Fubini-per-chart) plugs fm-2's shift theorem when the lift lands; obligations folded in (unit-absorption via
  S1.3, hcore_top endpoint, min-over-cover factorises n upstream-fixed). The mountain.
  - **R1.2 ROUTE — VERDICT: route B REFUTED → route-A-CONCRETE (pp + decorrelated Codex, INDEPENDENTLY IDENTICAL +
    witnesses).** ⚠️ CORRECTS my prior "L1-pivot charts resolve it" bank — that reading is WRONG. **THE DECIDER:**
    a residual product of length q≥2 has ‖∏C̃‖² with ordinary VANISHING ORDER 2q (NOT 2); regular changes (= L1)
    PRESERVE ordinary order ⟹ **L1-alone can NEVER expose the core as a smooth coordinate-square block** (route B
    is FALSE). The product-structure concern I gated on was REAL + it KILLS B. WITNESSES: (1,1,1) F=c₁²c₂² (monomial
    NC, only easy case); (1,2,1) F=(a₁b₁+a₂b₂)² (singular quadratic cone, first non-monomial); (2,2,2) F=‖AB‖²
    ord_0=4, Hessian ZERO, codim-3 irreducible, rlct=3/2 via radial/angular blow-up. So a **genuine BLOW-UP is
    REQUIRED + multiplicity-control is NON-VACUOUS** (k=1 on the EXCEPTIONAL divisors, post-blow-up, via the
    pos-def-REAL initial form — over ℂ fails at (x²+y²)²). **BUT not the abstract-infra mountain: route-A-CONCRETE**
    = explicit POLYNOMIAL blow-up charts (A=tA'; (2,1,2)=(x,xy,z,zw); etc.) with vanishing Jacobian on the
    exceptional locus, **S1.1 carrying the change-of-variables** (its hsurj+hImE hyps are EXACTLY for the blow-up's
    non-injectivity / null exceptional image — the 10th-finding design was built for this). NO Mathlib blow-up
    primitive. R1 = MEDIUM (explicit-poly-chart resolution + S1.1 + non-vacuous mult-control + cover). fm: do NOT
    build (B); the validate-small φ's (φ=id (1,1,1); explicit-poly (2,1,2)/(2,2,2)) ARE route-A-concrete charts.
    Codex sharpenings folded: (#2) R1.2 stays BARE (divisor inequality), assembly
    applies 1.unit-absorption → 2.monomial_rlct → 3.R1.2 → 4.S1Fubini SEPARATELY; (#3) Mval = CORE codim (reduced
    widths), assembly = **n/2 + B/2** (don't double-count the regular n). **fm seeded with R1.2a/b** (axisRatio
    arithmetic, zero-dep) + the route-independent (1,1,1) gate (xcheck vs `case111_rlct`); pp designing R1.1 charts
    validate-small-first ((1,1,1)→(2,1,2)→(2,2,2), symbolically verified). Climb order: R1.2a/b → R1.3 codim →
    R1.1 charts → R1.6 cover → assembly.
  - **14th FIDELITY FINDING (pp, load-bearing) — `resolution_charts` ORPHANED + MIS-SCOPED → RE-SCOPE to CORE
    (controller APPROVED):** (1) it's consumed by NOTHING (product_reduction doesn't call it ⟹ R1 was about to be
    built proven-but-unplugged); (2) it states the FULL-loss RLCT = ⨅ monomialThreshold (a MIN), but the full-loss
    RLCT = n/2 + ½·min Mval (a SUM — the reg n/2 is ADDITIVE via Fubini, not a min-direction) ⟹ FALSE for r>0; the
    (1,1,1) validate case had r=0 (n=0) so it didn't exercise the reg-term. FIX: re-scope to `rlctAt(core) wstar =
    ⨅ monomialThreshold` (R1's genuine content), and WIRE the assembly into product_reduction:
    `dlnLoss(deepestPt)` →[block_elimination] reg⊞core →[S1Fubini] n/2+rlctAt(core) →[resolution_charts(core)]
    n/2+⨅monomialThreshold →[A1] n/2+½·min Mval = aoyagiLambda. Clean separation: **R1 = core resolution; L2 =
    the assembly (split+Fubini+R1+A1); A1 = arithmetic.** The re-scope is REQUIRED for composition (S1Fubini takes
    rlctAt(core)). pp pins the corrected stmt + the `core` (∏C^(s)) object → fm restates + wires product_reduction;
    R1.1 charts resolve the CORE ‖∏C‖² (NOT full dlnLoss). Supersedes the stale-docstring item (whole stmt re-scoped).
- **S1.5 restatement+wire deferred to ONE pass** at fm-2's Fubini lift-close: I relay the complete signature
  (hGmeas + hGne + `[ProperSpace]`/`[IsFiniteMeasureOnCompacts]` instances) → fm restates + wires `exact` in one go.
- **FUBINI n=1 EQUALITY PROVEN** (fm-2, S1Fubini.lean @e1cf73c, 564 LoC / 17 thms, ALL axiom-clean): `step_rlct :
  rlctAtOn(x²+H)(0,y0) = ½ + rlctAtOn H y0` (H≥0, Measurable H, hHne germ-a.e.≠0; core space ProperSpace +
  IsFiniteMeasureOnCompacts). The **hardest analytic content of the whole expedition is DONE** — both directions:
  ≥ (step_rlct_ge: integrability split + sSup-lower-bound, ENNReal split idiom, admissible_downset); ≤
  (step_rlct_le: the cusp — step_lintegral_top contrapositive + core_adm_of_joint_adm open-witness wrapper via the
  {H≤R²}∪{H>R²} split; NO continuity needed for measurable H, the resolved subtlety). Measure-route B (1-D
  interval vol, no addHaar/EuclideanSpace bridge — lighter; cusp proven ONCE + reused per induction). **✅ S1.5
  ENGINE COMPLETE @ad1f313 — `rlct_additive_smooth_block_aux` (general-n shift `rlctAtOn(Σxᵢ²+G²)=n/2+rlctAtOn(G²)`)
  DONE + controller-VERIFIED axiom-clean (builds 2644 jobs, [propext,Classical.choice,Quot.sound], no sorryAx / no
  monomial_rlct).** The HARDEST analytic content of the expedition is proven (both dirs + cusp + down-set + sSup +
  λ_core=0 + the finPeel/chartN measure-preserving iteration). Minor: unusedSectionVars lint on [BorelSpace Y]
  (cosmetic). REMAINING for S1.5: fm wires `exact rlct_additive_smooth_block_aux` into the restated Skeleton
  statement (Skeleton-import pulls S1Fubini into the closure) → green-gate → rv-2 audit. **The whole S1 analytic
  substrate (S1.1/S1.3/S1.4 wired + S1.5 engine proven) is now COMPLETE.**
- **R1 DIFFICULTY MAP (pp general-atlas design + honest correction):** **R1.3 = LIGHT** — codim is a ℕ COUNT
  identity (∑ residual block sizes = Mval), NOT the determinantal-codim theorem; **Mathlib v4.29 gap GONE**
  (decorrelated-Codex + verified). **R1.1 = MEDIUM** (pivot recursion on L; base L=1 = smooth block via
  smoothBlockND_rlct, step = explicit-poly blow-up + recurse). **R1.6 (general cover) = THE MOUNTAIN** — the
  headline EQUALITY needs the LOWER bound (rlct ≥ ½min Mval), which needs the COVER complete (no missed worse
  divisor; codim-shortcut FALSE per x^{2k}/(x²+y²)², D1 doesn't give per-point LB) ⟹ critical-path, no shortcut.
  pp HONESTLY corrected its own "R1 medium" drift → R1.6 is where the difficulty concentrates; general-M may be a
  GENUINE WALL.
  - **R1.6 SHARP BOUNDARY + HEADLINE-REACH DECISION (pp detailed cover design + decorrelated Codex; controller
    adjudicated):** FIXED-M = INTRICATE-STANDARD, **provable now** (resolution = finite tree depth ≤L−1, unrolled
    to a finite explicit leaf-chart list; cover = finite sum, ONE Mathlib single-c-o-v per leaf; (2,2,2)=24 charts;
    NO recursion infra). GENERAL-M = **RESEARCH-WALL** (decorrelated-identical pp+Codex): n/tree/φ_i depend on M ⟹
    needs the recursion-as-a-theorem = the two missing-infra obligations **G3 (strict-transform tracking over
    arbitrary rank vectors) + G5 (gluing iterated c-o-v into ONE global integral identity; Mathlib has SINGLE
    c-o-v only)**. The cover is UNAVOIDABLE for the lower bound (Codex Q3 FACT; codim-shortcut false).
    **DECISION: (1) fixed-M LADDER near-term + (2) general infra (G3+G5) ROADMAPPED; (3) axiomatize-cover RULED OUT**
    (breaks one-citation / awkward-middle). LADDER (each a complete axiom-clean-mod-S2 headline instance +
    validates a machinery piece): (1,1,1) monomial [no cover] → (2,1,2) **Fubini-PRODUCT** [disjoint vars separate,
    NO blow-up — pp refinement] → (2,2,2) first TRUE cover [24 charts] → up the M-ladder. **DELIVERABLE FRAMING:**
    the full machinery (S1·Fubini·R1-fixed-M·A1·assembly) + the headline PROVEN for ladder cases; the FULLY-GENERAL
    headline = those + the named G3+G5 research obstruction (honest partial, NOT a false general claim). Assessing
    whether **G5 (abstract c-o-v-tree-gluing) is separable + buildable now** as a down-payment on the general lift.
    **OPERATOR SCOPE FLAG:** the general-M headline is gated on the G3+G5 research-infra lift — surfaced for the
    operator's steer (attempt the lift vs deliver ladder+roadmap); proceeding with the ladder meanwhile (no stop).
  - **(2,2,2) FULL COVER CLIMBED + VALIDATED (pp, exact-symbolic):** two nested blow-ups (faithful to Aoyagi
    Lemma 2/Thm 3): step-1 blow up {A=0} (4 charts, x-divisor ratio 2) → Lemma-2 regular split → step-2 blow up
    (3 charts, s-divisor ratio 3/2 = binding). **GENUINE HOLE caught+closed (validate-small working):** the 3
    step-2 charts are NOT uniform — E-/F0-pivot residuals are positive units (clean monomial×unit leaves), but the
    **δ-pivot residual U(origin)=0 is a SMOOTH-4-BLOCK** (v²+w²+G'²+H'²), so the δ-leaf = x²s²·(Σ⁴y²), NOT
    monomial×unit. Closed by CHECKING (not assuming): block rlct = 2 ≥ binding 3/2 ⟹ s-exceptional still binds at
    3/2 = ½·Mval(deepest), θ=1. Cover SOUND. **FIDELITY → Option A (BLESSED, fixed-M):** monomialize the smooth
    block (ratio-preserving — the cone Σⁿy² blows up to exceptional ratio EXACTLY n/2 = its rlct), so RHS
    `⨅ monomialThreshold` stays LITERALLY TRUE + leaves uniform. **DESIGN REFINEMENT:** the atlas has a THIRD
    block-monomialization layer ((2,2,2) is NOT 4×3=12 simple leaves; δ-branch subdivides into a 4-chart Σy²
    blow-up). **A-vs-B for GENERAL-M (open, part of the tractability verdict):** Option A's 3rd layer may COMPOUND
    G3/G5; Option B (block leaves bounded directly via smoothBlockND_rlct+Fubini, no extra layer, heterogeneous
    cover sum) reuses existing machinery — pp weighing as part of the general-M verdict. (2,1,2) confirmed NOT a
    cover (Fubini-product, disjoint vars, rlct=min(1,1)=1=½·Mval — separate small lemma).
  - **LOWER-BOUND SOUNDNESS SETTLED (pp + decorrelated Codex) — the general result is now mathematically PROVEN
    (on paper), so G3+G5 is pure FORMALIZATION labour, NOT open math.** The worry: a weakly-decreasing
    NON-admissible (t_L≠0) stratum with Mval < min_Adm (e.g. (2,2,2) t=(1,1), Mval=1 < min_Adm=3) — if blown up,
    exceptional ratio 1/2 < 3/2 would BREAK the LB. RESOLUTION: on {∏C=0} the product has rank 0 ⟹ **t_L=0 ALWAYS
    on the zero-locus ⟹ non-admissible strata are NEVER centers** (admPred's t_L=0 = "in the zero-locus"); every
    exceptional is admissible, k=1, h=Mval(t)−1, ratio ½·Mval(t), min over Adm ⟹ the bound. So the LB is
    structurally TRUE via the flag-resolution. **Codex Q4 lct-shortcut REJECTED as a trap** (rlct=½·lct(I)): (1)
    real-vs-complex unproven coincidence, (2) 2nd citation + breaks Aoyagi-independence (Lehalleur–Rimányi/
    multiplier-ideals), (3) black-boxes R1's content — cross-check only, NOT a proof path. So the headline-reach is
    now: **general theorem PROVEN on paper (decorrelated-sound); general Lean formalization = G3+G5 construction
    labour (roadmapped); fixed-M ladder formalized.** Operator scope flag refined: the lift is formalization-labour
    of a SETTLED result, not open research.
  - **G5-ABSTRACT SEPARABLE + BUILDABLE NOW (pp, checked vs Mathlib) → wall reduced to G3 alone.** G5 = `∫⁻_U|F|^{-c}
    = Σ_leaves ∫⁻(|F∘φ_i|^{-c})|Jac φ_i|` = [lintegral cover-additivity] ∘ [single c-o-v per chart], by finite
    induction on the depth-≤L−1 tree. Both Mathlib FACTS: single c-o-v = `lintegral_image_eq_lintegral_abs_det_
    fderiv_mul` (Jacobian.lean:1189) — over **lintegral (ℝ≥0∞) ⟹ NO integrability side-conditions** (the key; the
    threshold integrand is ∞ above rlct, ℝ≥0∞ handles it); + cover-additivity. ONE friction (not a wall): the lemma
    wants InjOn (blow-ups injective only OFF the null exceptional) → ADAPTER: apply to chart-minus-exceptional, the
    exceptional is null (`addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`). Intricate-standard, REUSABLE. **DECISION:
    BUILD G5-abstract (assigned fm-2, the measure specialist) — it's needed for the (2,2,2) cover's ∫=Σ∫ anyway (a
    G5-instance), reusable, and ISOLATES G3.** RESIDUAL (honest): **G3 (strict-transform tracking over arbitrary
    rank vectors — quiver-determinantal geometry Mathlib lacks) STILL the genuine general-M research piece**;
    G5-abstract isolates it, does NOT dissolve it. Refined roadmap: **general headline = ladder instances +
    G5-abstract (BUILT) + G3 (named open obstruction).**
    - **#52 SIMPLIFIED (pp, g5-abstract-statement.md): the LADDER needs only the SINGLE-STEP lemma** `∫⁻_U g =
      Σ_i ∫⁻_{V_i\Z_i} |det fderiv φ_i|·g∘φ_i` (finite a.e.-disjoint null-cover) — NO abstract rose-tree datatype.
      The (2,2,2) cover = finite compositions of the single-step lemma (A-blowup 4 ∘ step-2 3 ∘ block 4 = 24
      leaves). The abstract-tree form is DEFERRED to general-M (part of the G3 roadmap, not the down-payment).
      Mathlib anchors all checked (lintegral_image_eq_lintegral_abs_det_fderiv_mul + addHaar_image null + lintegral
      set-additivity); ℝ≥0∞-not-Bochner load-bearing. So #52 is the reusable single-step atom, tractable now.
      SEQUENCING: fm → (2,1,2) [product-MIN, no G5 dep] ∥ fm-2 → #52 single-step; then fm → (2,2,2) instantiates it.
- **13th FIDELITY FINDING (fm-2, proof-attempt-as-audit):** the committed Skeleton `rlct_additive_smooth_block`
  (line 169) is stated BARE (no hygiene on G) and is LITERALLY FALSE — germ-vanishing G² (or G≡0) ⟹ RHS=n/2+⊤=⊤,
  LHS=n/2; Lean-provable from `rlctAtOn_zero_eq_top` (S1Additive:67). The docstring ADMITS false but the SIGNATURE
  is bare = self-contradictory contract (the 12th finding's restatement was documented, never executed in the sig).
  FIX (controller-decided, fm executes single-writer, keep sorry): add `Measurable G` + a germ-non-vanishing hyp.
  **CONTROLLER CALL: hHne (G²≠0 a.e. near y0), NOT fm-2's hGfin (rlctAtOn(G²)<⊤) — hGfin is UNSOUND.** They are
  INDEPENDENT (not equal as fm-2 believed): hGfin admits a FALSE case. AIRTIGHT WITNESS (controller-derived,
  n=1,Y=ℝ,y0=0): G(y)=y·[y>0] ⟹ G²=y²·[y>0]; rlctAtOn(G²)(0)=1/2<⊤ (hGfin HOLDS) but LHS rlctAtOn(x²+G²)(0,0)=1/2
  (the y≤0 slice is pure x², ∫(x²)^{-c} diverges for c≥1/2, CAPPING the joint) ≠ RHS 1/2+1/2=1 ⟹ equality FALSE
  under hGfin. hHne excludes it (G²=0 on positive measure ⟹ ¬hHne). hGfin ALSO over-excludes true cases (G²=1:
  rlctAt=⊤, equality ⊤=⊤). So hGfin is wrong both ways; hHne is the sound hyp AND what fm-2's step_* already carry
  (the H=0 corner + cmpF a.e.-positivity). fm-2 ACCEPTED hHne. **EXACT LOCKED FORM** (relayed to fm; restate
  batched with S1.3, keep sorry): `(hGmeas : Measurable G) (hGne : ∃ U ∈ 𝓝 y0, ∀ᵐ z ∂(volume.restrict U), G z ≠ 0)`
  (germ form, G≠0 a.e. ⟺ G²≠0 a.e.). **FINAL COMPLETE SIG (fm-2 pinned, relayed to fm):** instances
  `[PseudoMetricSpace Y][MeasureSpace Y][ProperSpace Y][IsFiniteMeasureOnCompacts (volume)][OpensMeasurableSpace Y]`
  (the down-set needs them; NOT SigmaFinite as first guessed) — STRENGTHENING IS REQUIRED (the proof needs them ⟹
  a weaker Skeleton sig breaks the `exact _aux` wire; the "keep [TopologicalSpace] general" alt does NOT work).
  RHS `(n:ENNReal)/2 + rlctAtOn (fun y => G y^2) y0`. fm restates (batch w/ resolution_charts re-scope + (1,1,1)
  gate). USE-SITE: core's Y = Fin d→ℝ provides all 4 instances (bridge if Params-typed). R1's monomial ∏|y_j|^{2k_j}
  discharges hGne (≠0 off null coordinate hyperplanes). fm-2's proof _aux lands at iteration-close (one dependent-Fin
  snag: finPeel.continuous_invFun, no math depth) → fm wires `exact`.
- **R1 USE-SITE CONFIRMED (pp + Codex identical): CLEAN to relocate (confirms A) + 2 obligations folded into R1:**
  (1) **unit-absorption** — R1 chart core = unit·∏|y_j|^{2k_j}, so R1.2's S2 invocation MUST first absorb the
  nonvanishing unit via `rlct_unit_invariant` (S1.3), THEN S2 on the pure monomial (THE main hidden gap; Jacobian
  same); (2) **hcore_top endpoint** — free from the down-set property for strict c'>λ, +monomial-endpoint fact if
  literal ∫=∞ at λ (fm-2 pins which). min-over-charts CLEAN (n=r(H¹+H^{L+1})−r² upstream-fixed ⟹ factorises).

## GENERAL-M TRACTABILITY VERDICT (pp + decorrelated Codex) — THE WALL IS G3 ALONE
The definitive headline-reach picture. **A-vs-B (does the block-monomialization layer compound the wall?): NO.**
Codex flagged residual entanglement as FACT; pp LOCATED WHERE IT LANDS — at the T1 unit-termini (harmless:
monomial×unit either way), NOT the split-relevant T2 smooth-block termini (there the exceptional is pulled out
front ⟹ disjoint ⟹ product-MIN split holds). So: A's block blow-up compounds ONLY G5 (more leaves), no new G3;
B/hybrid (default B, cone-blowup only where entanglement occurs) is lighter for general M (reuses smoothBlockND +
the (2,1,2) product-MIN). **VERDICT: fixed-M (2,2,2) keeps Option A (uniform, execution-ready); general-M uses
B/hybrid; the block layer does NOT compound the wall.** CLIMB-OR-ROADMAP (assessed, not assumed): lower bound
SETTLED · G5-abstract BUILDABLE (down-payment, task #52) · block layer non-compounding ⟹ **G3 (explicit
flag-resolution / strict-transform for arbitrary M = quiver-determinantal geometry Mathlib lacks) is THE ONE
genuine research-wall — ISOLATED + NAMED.** ⟹ CLIMB fixed-M ladder + BUILD G5-abstract; ROADMAP G3. **Honest
general headline = ladder instances + G5-abstract + G3 (single named open obstruction)** — the best possible
roadmap shape (one well-scoped wall, not diffuse difficulty). OPERATOR SCOPE FLAG sharpened: general-M gated on
G3 ALONE. METHOD LESSON (pp, logged): when a decorrelated model flags a failure mode as FACT, the value is often
"locate WHERE it lands," not "abandon" — an obstruction confined to where it doesn't matter is a refinement, not
a refutation (dual of the Q4-trap: both = interrogate the SCOPE of the model's claim).

## G3 SPEC — the named wall, sharpened to its internal crux (pp, g3-spec-the-named-wall.md)
G3 = the EXPLICIT combinatorial flag-resolution of {∏C=0} (route-A-concrete, explicit poly charts — **NOT general
Hironaka**). Claim: for every M, a finite rose tree of explicit charts with (G3.1) coordinate-subspace stratum
centers, (G3.2) **strict-transform = smaller chain product [THE CRUX]**, (G3.3) leaves bottom out, (G3.4) cover
up to null, (G3.5) binding ratio (k=1, h=Mval−1) ⟹ rlctAt = ½·min_Adm Mval = lambdaCore.
**DONE vs OPEN:** G3.1 designed (R1.3 ℕ-count), G3.4 designed (cover + lower-bound settled), G3.5 done (R1.2a/b +
k=1 validated). **G3.2 (the in-chart residual re-identifies as a smaller matrix-chain product — the iterated
"Schur-complement-of-a-matrix-chain is a smaller chain product" fact) is THE genuinely-open crux.** CRITICAL:
**Aoyagi PROVES G3.2 on paper (pp.15-21) — so G3 is a FORMALIZATION gap, NOT open math.** The dedicated-tide build:
explicit pivot-chart φ+Jacobian → the Schur-complement lemma (G3.2, substantial) → recursion (terminates) →
cover+ratio wiring → glue with G5-abstract. Multi-rung tide.
**HONEST HEADLINE SHAPE — LOCKED:** PROVEN = the fixed-M ladder + the general machinery (S1/L1/L2/D1/A1/A2/
G5-abstract); ROADMAPPED = G3 (crux G3.2 = Aoyagi pp.15-21 to formalize). One well-scoped, paper-proven,
formalization-only wall — the cleanest possible roadmap (a known proof to formalize, not open research).
**OPERATOR SCOPE (sharpened):** the general-M headline is gated on the G3.2 Lean construction — a dedicated tide;
everything else proven/buildable. Choice: deliver now (ladder + machinery + G3 roadmap) vs commission the G3 tide.
**G3.2 AS A PRECISE LEMMA + ON-RAMP (pp, final sharpening):** G3.2 = "if the leading t₁×t₁ minor of the partial
product is a unit in a pivot chart, UNIMODULAR row/col changes give ∏(QCQ)=diag(E_{t₁}-regular, ∏C') with C' the
Schur-REDUCED chain (widths M^s−δ_s), and ‖∏C−B‖²=‖reg generators‖²+‖∏C'‖² ⟹ rlctAt=½·reg-dim+rlctAt(‖∏C'‖²),
recurse" = **Aoyagi Thm 3 + the chain-Schur recursion** (verified L=1; well-founded, ΣM^s strictly drops, base =
smooth block). **ON-RAMP: G3.2 REUSES `block_elimination` (L1, DONE) + `product_reduction` (L2)** — it's their
GENERAL-M chained form. So the G3 tide is "**generalize the already-built L1/L2 to an arbitrary-rank-vector
recursion + glue with G5-abstract**," NOT from-scratch resolution infra; the fixed-M product_reduction wiring is
the PROTOTYPE the tide generalizes. The roadmap is genuinely set up: one named wall, a precise lemma, a known
paper proof, AND a concrete on-ramp.

## D1 RE-SCOPED (fm proof-attempt-as-audit) — NOT a light standalone rung
D1 `deepest_point_reduction` is blocked on TWO real deps: (1) the **RLCT-monotonicity lemma** `|G|≤|F| a.e. near
w* ⇒ rlctAt G ≤ rlctAt F` — MISSING + measure-theoretic (the 0^neg a.e.-domination corner: |G|^{-c}≥|F|^{-c} a.e.
where G≠0, reverses at {G=0}); **assigned fm-2** (reusable by L2's per-point argument). fm has the pointwise core
`rpow_neg_antitone`. (2) D1 depends on **L2** (homogeneous-scaling Thm-2 argument needs core-homogeneity, not the
raw mixed-degree dlnLoss B ⟹ per-point core reduction ≈ L2-per-point). So critical-path order is
**S1✓ → [monotonicity lemma + L2(needs R1/Fubini)] → D1**, NOT S1→D1. Rung map corrected.
**fm BLOCKER cleared:** resolution_charts re-scope (#47) was decided but never LANDED in Skeleton — fm landing it
now (pp's core form, BLESSED) + the S1.5 wire (fm-2's verified package) in one batch → green-gate → (1,1,1) gate.

## STATE @ ~03:20 — R1.2 LIGHT confirmed (de-risk) + (1,1,1) gate spec'd; trunk @995a674
- **R1.2 IS LIGHT (pp confirmed, §8 literal):** post the L1/Lemma-2 unit-Jac changes, the residual/reg entries ARE
  coordinates (the changes DEFINE them so — F₂/F₃ are the L1 coord changes) ⟹ ‖reg‖² + residual block = Σ(coord)²
  = smoothBlockND + rlctAtOn_comp_homeomorph. NO IFT, no general reg-seq, no S1.1-diffeo. And the (2,2,2) Option-A
  cover is EVEN LIGHTER — all leaves monomial×unit ⟹ per-leaf = WEIGHTED monomial threshold, NO block-rlct. So
  the fixed-M ladder is cheap throughout; no R1.2 sub-mountain. fm-2's #54 block-rlct under Option A = quick.
- **(1,1,1) gate SPEC'D (pp → fm):** ι=Unit (1 chart), φ=id, |Jac|=1 (so BARE rlctAtOn is correct here — contrast
  the WEIGHTED (2,2,2)); d=2, k=(1,1), h=(0,0); monomialThreshold = 1/2 = lambdaCore(1,1,1) = ½·Mval, θ=2; box =
  Fubini-product = the done Case111Bridge. No cover, no G5 — fm SPECIFYs directly. The R1-batch's last item.
- fm: WIRE rlct_additive_smooth_block ((b) keep+exact, closes S1.5 sorry 6→5) + re-scope resolution_charts + the
  (1,1,1) gate → (2,1,2) [#55]. fm-2: product_min_rlct (#56) → (2,2,2)-measure (#54). pp: on-demand. rv-2: queued.
- **PROPERNESS GAP (fm SPECIFY-catch) → AVOIDED via g5_flat_cover (controller adjudicated):** a single explicit
  blow-up chart does NOT satisfy S1.1 `weightedThreshold_transport`'s GLOBAL `IsProperMap`+`Surjective`. Resolution:
  R1's per-chart transport = the **lintegral c-o-v inside g5_flat_cover** (per-chart `InjOn` off the null exceptional
  only — NO global proper/surj); global coverage = R1.6 (the cover). So `rlctAt(core)=⨅ monomialThreshold` =
  g5_flat_cover (∫=Σ∫) + per-chart weighted-monomial threshold (S2+unit-absorption) + sSup algebra. NOT
  G1/G2/G3-bespoke — g5_flat_cover is the GENERAL version of how (1,1,1) bypassed S1.1. (2,1,2) uses product_min_rlct
  (Tonelli, no transport) ⟹ gap moot there. **S1.1 ORPHAN FLAG:** S1.1 is NOT R1's chart-transport (earlier
  "S1.1 carries the blow-up CoV" was imprecise — g5_flat_cover does) ⟹ revisit whether S1.1 is used by D1/L2 or is
  now an orphan (proven, hsurj+hImE 10th-finding banked, possibly unplugged) — pp checking; name honestly; doesn't block.

## STATE @ ~03:00, trunk @c92501d — R1 DESIGN PHASE COMPLETE; execution remains
- **rlctAt_mono ON TRUNK** (D1/L2 engine; green-gated 2855 jobs, controller-verified axiom-clean). fm built it with
  the **zero-set-inclusion hyp (G=0→F=0)** — BETTER than the hGne alt (pointwise, no a.e. machinery; use-site:
  D1's scaled core has F's zero set). 15th finding (bare monotonicity false, G≡0/F=|x|⁴) caught at SPECIFY by both
  fm+fm-2; fm's fix adopted. (Also merged: R1.2a/b + the #19 engines, banked on trunk.)
- **FIXED-M LADDER DESIGN COMPLETE + CERTIFIED (pp R1 design role DISCHARGED):** (1,1,1) [done] · (2,1,2) [#55,
  product-MIN, min≠sum CERTIFIED via the c=3/2 ∫r^{-2}=∞ divergence test] · (2,2,2) [#54, 24-leaf cover, cover-
  complete 12063/12063, a G5-instance]. Roadmap mapped: lower-bound settled · G5-abstract build-ready (#52) ·
  A-vs-B verdict (wall is G3 alone) · G3 spec (crux G3.2 = Aoyagi pp.15-21 formalization gap). **Residual = pure
  formalization labour** (fm + fm-2 execute) + the G3 tide if commissioned.
- **EXECUTION UNITS:** fm → the R1 BATCH (S1.5 wire + resolution_charts core re-scope + (1,1,1) gate) FIRST [still
  not landed — fm redirected to it 3×; recurring fm→adjacent-work drift], then #55 (2,1,2) + #54-assembly; fm-2 →
  #52 G5-step + #54-measure; pp → on-demand (G5 questions / assembly / G3 tide). rv-2 → S1.5 PASS done; queued.
- **G5-ABSTRACT FLAT-COVER DONE (#52, fm-2 @48b9468, axiom-clean):** `perChart` (single-step c-o-v on V\N + null
  drop) + `g5_flat_cover` (∫⁻_U=Σ∫⁻ over a finite a.e.-disjoint chart-cover, lintegral_biUnion_finset₀). The (2,2,2)
  cover = this **composed 3×** (nested levels 4∘3∘4), NOT the abstract tree (deferred to G3). Over ℝ≥0∞ ⟹ no
  integrability hyps.
- **product_min_rlct HYP UNIFIED (pp):** positivity-guard (both ∫⁻>0) + disjoint + measurable, NOT "vanish only at
  0" (over-strong, excludes monomials) ⟹ ONE lemma covers block×block (2,1,2) + monomial×block (δ-leaf) +
  monomial². The (2,1,2) tool IS the δ-leaf tool. S1.5-PASS = the L2/additivity SUM-engine (NOT the δ-leaf PRODUCT).

## Next tick (state @ ~02:30, trunk @da24204)
**S1.5 FUBINI ENGINE COMPLETE @ad1f313** (controller-verified axiom-clean) — whole S1 substrate proven. R1 lower-bound
soundness SETTLED (general result PROVEN on paper). **(2,2,2) cover EXECUTION-READY** (pp, 24 leaves, cover-complete
12063/12063, a G5-instance). **G5-abstract BUILDABLE + assigned fm-2** (Mathlib lintegral c-o-v; reduces general wall
to G3 alone). Headline-reach DECIDED+flagged: fixed-M ladder now + G3 named obstruction.
LIVE: (1) **fm** — Skeleton batch (S1.5 `exact` wire + resolution_charts core re-scope + product_reduction wiring) +
the (1,1,1) gate → report green-gate. (2) **fm-2** — G5-abstract (cover-gluing lemma) + (2,2,2) per-chart measure
pieces. (3) **pp** — (2,1,2) Fubini-product design (completes the ladder design). (4) **rv-2** — audit the S1.5 engine
(#50) + queued wires. Then: fm formalises the (2,2,2) cover (pp leaf-list + fm-2 G5-abstract) → L2 (=block_elim+
S1Fubini+R1-core+A1) → D1 → T (fixed-M headline). #19 PARKED. G3 = the one named general-M research obstruction.
Watch the fm→#19 pull (parked 3×). Don't stop in a blocked state.

### (prior next-tick) state @ ~02:00
TWO BIGGEST RISKS RETIRED: Fubini n=1 equality PROVEN (@e1cf73c) + R1 route VALIDATED (A-concrete, B refuted).
Remaining = execution + assembly. **Re-scope PINNED** (pp → fm): `resolution_charts(M) = rlctAtOn(dlnLoss M 0)(0)
= ⨅ monomialThreshold` (reduced widths M = core) + product_reduction wiring chain (block_elim → S1Fubini n/2 →
resolution_charts-core + S2 + A1 → aoyagiLambda). **λ_core=0 edge HANDLED** (fm-2, core_admissible_zero, no
λ_core>0 hyp). Iteration keystone `rlctAtOn_comp_homeomorph` banked (@f254397).
INTEGRATE as they land: (1) fm-2's Fubini ITERATION (Fin-peel homeomorph + Σ-peel) → general-n
rlct_additive_smooth_block → report final sig → fm restate+wire (ONE pass) → I aggregator-wire S1Fubini +
green-gate → rv-2 audit. (2) R1 CLIMB (validate-small-first): fm closes the **(1,1,1) gate** (φ=id chart + S2 +
arith, NO general geometry, xcheck `case111_rlct`) → (2,1,2)/(2,2,2) explicit-poly charts; pp designs the GENERAL
atlas R1.1/R1.3(codim=Mval, heavy)/R1.6(cover) in PARALLEL (math validate-small'd via witnesses). fm also restates
resolution_charts (core) + wires product_reduction. (3) L2 → D1 → T. #19 PARKED. Critical path: Fubini-iteration
+ R1-(1,1,1)-gate → general R1 atlas → wire product_reduction → D1 → T. rv-2 decorrelated (R1 = heaviest audits).
Watch the fm→#19 pull (parked 3×). Don't stop in a blocked state.
