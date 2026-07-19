# Overlay — banked-family cards (cartographer, curated layer)

*The banked substrate the engine CONSUMES (never rebuilds — "survey before commissioning", compass
standing counsel). **Pass #2 (2026-07-18): REFRESHED + CONSUMPTION-SCOPED by the remaining rungs
R1–R6** (recon cert §5 roadmap). Each rung lists the families it consumes with PINNED decl names,
`file:line`, sorry-status, and an import-weight note. Pins RE-VERIFIED by grep against the live tree
(2026-07-18); drift from pass #1 flagged inline. All paths `lean/DLNFibre/DLN/RLCT/…`.*

**Import-weight key** (transitive DLNFibre-internal import count, a build-cost proxy; measured
2026-07-18): LIGHT ≤ 40 · MEDIUM 40–150 · HEAVY > 150. The full whitelist + the heavy-cone re-home
is in [[import-hygiene]].

**Rung → hole map.** [REFRESHED 2026-07-19, tick 170 — post-E-assembly.]
`monomialization_terminates` is ASSEMBLED (EngineObligations:72; 4 conjuncts proven clean-three);
`region_glue` is a PROVEN composition (`region_glue_of_chartBridge … hbridge`, :131). The two
live ANALYTIC holes are `chartBridge_buildTree` (:52, ← the chart-emission carrier + coverage's
3-Prop tide) and `o5_realization` (:63, ← D§ii/iii from cert-o5-realization §§3-4) — R2 and R3
CONVERGE at `chartBridge_buildTree`. R5 flips `engine_box_threshold_finite` → `hbox` → repoints
`aoyagi_learning_coefficient`. These two + the `canonicalResolution224` @[blueprint] forecast
(`CanonicalWitness224.lean:135`, off-cone, closes as a coverage corollary at (2,2,4)) are the
ONLY engine-cone sorries. Census: [[dead-routes]] § fossil census.

---

## R1 — construction carrier + faithful ledger + divisor-chooser (MEDIUM tide)

*Builds the resolution tree into `CanonicalResolution` — the structural half of
`monomialization_terminates`. Carrier + ledger + termination DONE; the chooser (full-`T`) is the
open fork-10 un-deferral.*

**Consumes (banked, sorry-free):**
- `minAdm` / `minAdmRec` / `minAdmRec_eq_minAdm` — `Validate/RouteMLayerSplit.lean:51,58,395`. The
  combinatorial budget; `decide`-computable. LIGHT (RouteMLayerSplit cone = 21).
- The μ-lex well-founded idiom `ℕ ×ₗ ℕ ×ₗ ℕ` + `InvImage.wf wellFounded_lt` — banked in
  `Validate/RouteMState.lean` (rung 2A surveyed it before building; no new WF machinery invented).
  Consumed by `conRel_wf` (`Engine/EngineConstruction.lean`, PROVED clean-three, tick 58). LIGHT (32).
- `Adm` / `admBound` / `Mval` — `Foundations/Lambda.lean:62,46,41`. The admissible cone (incl. the
  `j=1` block bound `min(M¹,M²)`, Def 3 p.8). LIGHT.

**Already built this expedition (do NOT rebuild — reuse in place):**
- `ResolutionTree` / `StepData` / `Edge` / `LeafData` (edge-labelled carrier) —
  `Engine/ResolutionTree.lean`. Import weight 4 (VERY LIGHT). r2-VALIDATED (tick 37).
- `RootLedger` + `stepUpdate` (3 cases, page-pinned) + faithful `StepRel := rootLedger e.child =
  stepUpdate n e.case e.subst` — in `Engine/EngineObligations.lean`. case-2 cleared advance is `+= 1`
  (p.21 truth-witness catch, tick 46 — NOT `+= resRows`). Eligibility conjunct `t̃(mergeIdx) =
  cleared + runLen` guards BOTH case-1 charts (tick 56).
- `ConState` / `StateInvariant` / per-case μ-descent (`conRel_stepCase11` /`_stepAppendAdvance`/
  `_stepRollover`, all clean-three, tick 59) — `Engine/EngineConstruction.lean`.

**Open — the FAITHFUL carrier lands at R1 NOW (council #3 fork 11, 2026-07-18):** full-`T` in the
State (t̃ DERIVED from T; T is non-derivable chooser-required data — deferring it is incoherent and
risks a μ-descent retrofit) + the `genDivExp` multiplicity field, in ONE faithful node-data pass.
The `EngineConstruction` "stores ONLY what the measure reads" docstring is STRUCK (the retired
finiteness razor encoded in code). The p.15 minimality tie-break + J₁ gap need full-`T`; propagation
PROOFS defer to R4. STOP-and-surface if full-`T` `stepUpdate` balloons; divProfile T-settings
page-verified at build.

---

## R2 — coverage / no-smaller-ratio: `ChartBridge` (HARD — the hardest named object)

*The one genuine new proof; landmark `coverage-theorem`. Lives INSIDE `monomialization_terminates`
(the bundle collapsed the fan-out — the covering CONTENT is in the construction hole, not its own
tide). Consumes the cover/null toolkit; may NOT consume `rlct=c*` (circularity guard).*

**Consumes (banked, sorry-free):**
- Finite box covers + measure-zero disposal — `Foundations/S1Cover.lean`, `S1BoxAdditive.lean`,
  `Validate/RouteMCoverLemmas.lean`, `Validate/RouteMNullSliceCov.lean`. LIGHT-MEDIUM. Load-bearing
  precondition: the SEPARATED leaf integrand (`IsFullMonomialization`), witnessed
  `g-leaf-chain-separation`, `g-pivot-conull`.
- The corank-2 coordinate-index model (`divCoord`/`resCoord` injective + disjoint over `Fin (flatDim
  M)`) — de-risked at (3,3,4) by `Engine/CoRank2Spike.lean` (rung 2C, tick 58; import weight 31).

**Gate (armed, do NOT skip):** the exhaustiveness hunt (`hunt-cert.md §5`) SURVIVED carrier-independent
(tick 12; 5 decorrelated legs, 0 undershoots) — no re-run needed, but a monomial-only hunt passes
vacuously; cite the scope by pointer, never "established". Kill = `g-coverage-sharing-killcond`.

---

## R3 — `region_glue` / per-leaf (HARD/MEDIUM — analytic hole)

*Per-leaf area-formula integration → box finiteness, glued over the finite subcover. The per-leaf
read MECHANISM CHANGED since pass #1 (elder tick 43): the banked local-homeomorph transport is
BANKED-BUT-UNUSED on this path; the read is now the Mathlib AREA FORMULA. See [[dead-routes]]
§ transport-on-leaf-path (retired-shape).*

**Consumes (banked, sorry-free):**
- **Area formula:** `lintegral_image_eq_lintegral_abs_det_fderiv_mul` +
  `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero` (Mathlib, v4.29 — elder-verified
  present tick 43). Needs ONLY the UPPER det bound `|det Dφ| ≤ hi·∏|u|^{divExp−1}`.
- **Flat model read (the per-leaf target):** `model_read_lt_top` —
  `Validate/RegionGlueModelRead.lean:215` (NEW this expedition, Module A COMPLETE tick 60,
  clean-three). `∫_cube (∏|x|^e)(∑x²)^{−c'} < ⊤` for `e>−1`, `0<c'<nr/2`; a.e. AM-GM domination via
  `Measure.pi_hyperplane`. Import weight 27 (LIGHT).
- **Scaling bridge (globalization):** `lintegral_rpow_neg_smul_bridge` +`lintegral_smul_set` —
  `Foundations/S1ScalingBridge.lean:88,36` (NEW, tick 40, clean-three, Foundations-grade abstract
  `F`). LIGHT. NOTE: pass-#1 name `∫_{εK}F^{−c'}=ε^{N−2Lc'}∫_K` is `lintegral_rpow_neg_smul_bridge`.
- **DLN homogeneity (degree 2L):** `flatNodeLoss_smul` / `dlnLoss_zero_smul` /`prod_smul` —
  `Validate/D1L2ExplicitCoreProducer.lean`. **⚠ HEAVY (302-file cone).** RegionGlueGlobalize uses
  only the smul lemmas but drags the whole D1L2 explicit-core producer. RE-HOME candidate — see
  [[import-hygiene]] § D1L2 worked example. The smul lemmas themselves only need
  `Foundations/S1NodeFlatHomog.lean` + `Validate/LossHomogeneity.lean` + `ParamsFlatLinear`.
- **Haar on `Params M`:** `instIsAddHaarMeasureParams` / `instBorelSpaceParamsGlue` —
  `Engine/RegionGluePerLeaf.lean` (NEW, via `paramsEquivFlatCLE`; volume on `Params M` is NOT
  auto-Haar — transported from the flat cube). These two instances are ALL that's currently landed
  in RegionGluePerLeaf — the area-formula theorem itself is Module B, IN FLIGHT (task #2).

**Already built (globalization half, boundedness-independent):**
- `routeMLayerBoxIntegral_lt_top_of_small_box` + `cubeBox_smul` + `routeMLayerBoxIntegral_eq_flat` —
  `Engine/RegionGlueGlobalize.lean` (tick 45, clean-three). **⚠ HEAVY (304).** Namespace quirk: lives
  in `Engine/` but declares `namespace DLNFibre.DLN.RLCT` — see [[naming]].
- Interface is FROZEN (ChartBridge strengthened: MeasurableSet + bounded-in-flat-cube srcBox, tick
  46) and abstract-field-gate-CLEARED exactly-sufficient (tick 51 — no third conjunct needed).

**Open:** Module B (per-leaf area formula, `RegionGluePerLeaf`, task #2) → Module C (cover assembly +
globalize, task #3) → `leaf_chart_image_lintegral_lt_top` → `region_glue_of_chartBridge`.

---

## R4 — `genDivExp` PROPAGATION proofs (MEDIUM — fidelity)

*The multiplicity-valued `genDivExp` FIELD now lands at R1 (council #3 fork 11); R4 is the
sharing-PROPAGATION proofs across per-divisor re-indexing (what balloons — Codex-confirmed tick 44).
No banked substrate to consume — fresh fidelity work on the carrier.*

**Guard / kill-condition (do NOT ship without):** `g-coupled-binding-334` (minAdm(3,3,4)=8 coupled
path only) + `g-delta-flatten` (identical multiplicities, different lct) re-checked. The current
binary `support : Fin numGen → Finset` is a nonzero-locus APPROXIMATION (recon §4); the exact
`LeafPullback` identity — not propagation — is what breaks coupling for the certificate, so R4 is
fidelity, not finiteness-load-bearing.

---

## R5 — wiring (MECHANICAL) + the enforced axiom-gate

*Discharge `hbox`; repoint the canonical headline → `_gen` → the UNCONDITIONAL CLEAN-THREE
`aoyagi_learning_coefficient` (kills the sorryAx of the 5 skeleton rungs). **Council #3 precision pin
(fork 11): this does NOT delete `cited_aoyagi_dln`** — the cite was NEVER in the λ cone (grep: only
absence-asserting docstrings); it lives in the OUT-OF-SCOPE `RlctPayoff` layer (needs `minAdm=codim`,
the next expedition's runway). "Kills the cite for free" was headline-inflation, STRUCK. GUARD (seat
B): `_gen`'s clean-three currently rests on a `#print` DIAGNOSTIC (`AxCheck.lean:913`),
confirmed-by-discipline not build-enforced — R5 installs an ENFORCED axiom-gate. L=1 reaches the
unsuffixed theorem via a SEPARATE fold (not `_gen`).*

**Consumes (banked, sorry-free — the whole consumer stack is PROVEN):**
- `aoyagi_learning_coefficient_gen` — `Validate/HeadlineGenAssembly.lean:55`. Clean-three, conditional
  SOLELY on `hbox = RouteMBoxThresholdFinite (H−r)` — uses NO `cited_aoyagi_dln`/`monomial_rlct`/
  `sorryAx` (recon §3, Lean-verified). **⚠ HEAVY (356-file cone = the value lane)** — unavoidable at
  wiring (the driver must SEE `_gen`); acceptable because R5 builds rarely. `EngineDriver` (359)
  inherits this.
- The `≤`-half (achiever divergence): `routeMCore_box_diverges_achiever_full'` —
  `Validate/RouteMAchieverFullHNoFree.lean:40`, 0-sorry. Folded with the finiteness half by
  `r1_resolution_general` (`Validate/R1ResolutionGeneral.lean`) into `= ofReal(lambdaCore M)`.
- Regular-peel / value-shift (Theorem 3): `reg_shift_add_core_eq_aoyagiLambda`
  (`Validate/DeepestFrontGaugeGen.lean` + consumers), `deepest_le_of_homogeneous_core`
  (`Validate/DeepestMinRlct.lean:157`, hypothesis-free — Theorem 4 deepest-point).
- `RouteMBoxThresholdFinite` (hbox predicate) — `Validate/RouteMBoxReduction.lean:165` (verbatim
  anchor). `engine_box_threshold_finite` (the discharger) — `Engine/EngineDriver.lean:44`
  (@[blueprint], sorry-free composition; its flip to clean-three IS the hbox event).
- MINT anchor: `aoyagi_learning_coefficient` bare name at `Skeleton.lean:1685` (legacy stub
  re-pointing at mint). ⚠ Skeleton.lean carries 3 legacy stub sorries (`:1094,:1140,:1197`) — see
  [[dead-routes]]; the repoint must land the bare name on `_gen`, not on a stub.

---

## R6 — regular-peel transcription (OWED FIRST-CLASS; off critical path, cost-probe-gated)

*Lemma 2 + Theorem 3 (block-diagonalization, Layer A) as first-class library objects. **Council #3
OVERRODE the recon's "value lane suffices" (fork 11): both seats reject it as the retired razor — the
value lane gets the NUMBER, not the OBJECT; under fork 10 (build HER mechanism) the peel is OWED.**
Placed post-spine, off the critical path, COST-PROBE-GATED (the SchurCore depth-≥3 wall,
`rr4-precedent`), surfaced to the operator for scope confirmation. θ + Eqs (1)–(5) stay out.*

**Consumes:** the value-lane peel (`reg_shift_add_core_eq_aoyagiLambda`, `DeepestFrontGaugeGen`,
`HeadlineRowColPermWLOG`, `D1Ge*`, all banked sorry-free in `_gen`) computes the shift VALUE, not the
OBJECT — so R6 builds Lemma 2's Schur-complement CoV + Theorem 3's peel induction as fresh
object-level work; no banked object-level substrate. Cost-probe first (the SchurCore wall).

---

## Worked precedent (the pattern the generic engine reproduces)

`Validate/RouteMBoxThresholdRR4.lean` — the (r,r,4) family end-to-end 0-sorry. Assembly decl
`routeMBoxThresholdFinite_rr4_of_schurRecStep` (`:219`); threshold match `minAdm_rr4_eq` (`:88`);
CoV `routeMLayerBoxIntegral_rr4_eq` (`:177`). See [[landmark-cards]] `rr4-precedent`. **OUTER-plumbing
precedent ONLY** — the inner SchurCore/front-peel core walls at depth ≥ 3 (`:12–21`), so it does NOT
precedent the L=3 (2,2,2,2) case-1(1) merge (task #7). NOTE: shorthand "RR4.lean" = this file (no bare
`RR4.lean`).

---

# D-ARC REUSE INDEX (cartographer-3, 2026-07-19)

*The construction kit t04 CONSUMES to fill `o5_realization` (`EngineObligations.lean:63`, `@[blueprint]`
sorried) via `cert-o5-realization.md` §§3–4. **The whole kit is banked sorry-free** — `EngineConstruction.lean`
= 0 sorries (verified `grep`, 2026-07-19); the coverage kit = 0 real sorries (the `sorry` token in
`PivotCoverFold.lean:8` is a STALE docstring line, not a proof hole — `node_pivotCover_of_atom` IS proven).
Every pin `file:line` grep-verified against the live tree at HEAD `da6567505`. All five families live in
`Engine/`. **The cert→Lean vocabulary map is the reuse's crux** (cert names ≠ Lean names in several places,
flagged inline). t04's ONE genuine new brick is `o5_realization`'s §4 descent case (the intra-layer
pull-ordering) — everything below is REUSE, not rebuild.*

## (a) The invariant kit — `EngineConstruction.lean`, all sorry-free

The o4/o5 state invariants + their per-transition maintenance + the reachability threading. The steering
descent invariant (cert §4) is maintained by CONJOINING these across the same three step-transitions.

- **Defs:** `SameLevelChainInv` (`:625`), `FlatTail` (`:650`), `WeakDecInv` (`:540` — **cert/handoff call it
  `WeakDec`; Lean name is `WeakDecInv`**), `WidthBound` (`:872`), `LiveHeadDom` (`:886`), `BoundaryFlat`
  (`:1422`), `T0Bound` (`:1490`), `NumDivFlatPos` (`:1588`), `MvalCoh` (`:1365`). The settled-fields bundle is
  the STRUCTURE `StateInvariant` (`:92`, layer/cleared/live-width — distinct from the o4 defs above).
- **Maintenance ×3 transitions** (rollover / case-1(1) `stepCase11` / append-advance `stepAppendAdvance`
  [+`_case12`]): `LiveHeadDom_step{Rollover,AppendAdvance,AppendAdvance_case12,Case11}` (`:1011,1041,1078,1123`);
  `SameLevelChainInv_step{Rollover,Case11,AppendAdvance,AppendAdvance_case12}` (`:1167,1175,1218,1264`);
  `BoundaryFlat_step{Rollover,Case11,AppendAdvance}` (`:1429,1441,1462`); `T0Bound_step{Rollover,Case11,
  AppendAdvance}` (`:1495,1500,1527`); `NumDivFlatPos_step{Rollover,Case11,AppendAdvance}` (`:1591,1594,1597`);
  `MvalCoh_{stepRollover,stepAppendAdvance,case11child}` (`:1376,1383,1395`). Roots: `{BoundaryFlat,MvalCoh,
  T0Bound,NumDivFlatPos}_conRoot` (`:2493,2496,2499,2502`).
- **Reachability threading (the fold's engine):** `MvalBoundaryInv_conOracle_stepChildren` (`:2261` — a THEOREM
  name, NOT a def) threads `BoundaryFlat ∧ MvalCoh` through EVERY `conOracle` step-child (case-2 via the
  telescoping identity, case-1 via the delta + BoundaryFlat). This is the pattern t04's §4 anchor-descent
  invariant re-uses: prove per-transition maintenance, thread through `conOracle`, fold at leaves.
- **Consumes:** `LiveHeadDom` case-1 maintenance CONSUMES chooser minimality (see (b)); `LiveHeadDom < Mrun(S)`
  guard is load-bearing (stranded pairs at level `= r_S` are OUT of scope — that is exactly why full-chain
  fails and `SameLevelChainInv`/`LiveHeadDom` survive; [[dead-routes]] minimality-free + full-chain kills).
- **Near-miss:** there is NO global `WidthBound`/full-comparability invariant — both are FALSE at interior
  bottlenecks ([[dead-routes]]). `WidthBound` is the LIVE-restricted bound only.

## (b) The chooser / minimality family — `EngineConstruction.lean`, sorry-free

**THE family t04's pull-ordering brick reuses** (cert §4 flagged brick ↔ cert-compchain-o4 §§6–7). Maps the
cert's "STEP1 / minimality" prose to Lean:

- `IsEligibleMinimalChoice s k runLen` (`:275`) — the eligibility+minimality predicate (`1 ≤ runLen ∧
  divTilde k = cleared+runLen ∧ ∀ k' at that level, divProfile k ≤ divProfile k'`).
- `chooseMin s target` (`:1818`) + `chooseMin_spec` (`:1830`) — the Def-4-least chooser + its read-off
  (returned divisor is at `target` AND componentwise-≤ all same-level divisors).
- `chooserTotalOnChain_of_sameLevel` (`:1861`) — o2 min-existence: on a `SameLevelChainInv` state the chooser
  never falls back (`ChooserTotalOnChain`, `:1852`). Helper `le_of_comparable_sum_le` (`:1842`, ∑-min ⟹
  componentwise-min on a chain).
- **`step1_dominates` (`:904` — cert calls this "STEP1"; Lean name is `step1_dominates`)** — the residual's
  core: at a case-1 node every level-`ℓ` divisor dominates every level-`≤J` divisor. Consumes `LiveHeadDom` +
  `FlatTail` + `WeakDecInv` + `divProfile_tail_eq_tilde` (`:893`). This is the exact lemma cert-o5 §4's descent
  case ("A lands at exactly `a^S`, Def-4-least at its level") transcribes.
- **Minimality is LOAD-BEARING** (cert-compchain-o4 Part 7): a non-minimal pick breaks `SameLevelChainInv` at
  `(2,2,3,3,2)`. Do not build the descent invariant "minimality-free" ([[dead-routes]]).

## (c) The Mval family — `EngineConstruction.lean` + `EngineDefs.lean`, sorry-free

§3's envelope-splice is ALGEBRAIC over these (same flavor as the banked telescoping/delta):

- `Mval_setTail_runMinWidth` (`:741`) — the case-2 telescoping identity `Mval(setTail layer cleared
  runMinWidth) = (widthMinUpto layer − cleared)(M(layer+1) − cleared)` (head terms die by
  `widthMinUpto_succ`, tail by constancy; ℤ then `.toNat`).
- `Mval_setTail_delta` (`:806`) — the case-1 tail-write delta `(τ−J)(M^(l+1)−J)`, faithful under `BoundaryFlat`.
- `MvalCoh` (`:1365`) is the ℤ-EQUALITY form `(divExp k : ℤ) = Mval` (NOT `.toNat`); `MvalCoh.toNat` (`:1370`)
  derives the `IsFullMonomialization` read-off. **Keep deltas over ℤ, cast at the leaf** (t04-handoff §4).
- Primitives: `runMinWidth` (`EngineDefs.lean:91`), `widthMinUpto` (`EngineDefs.lean:98`); helpers
  `widthMinUpto_succ` (`:693`), `runMinWidth_eq_widthMinUpto` (`:657`), `runMinWidth_antitone` (`:677`),
  `setTail_of_le` (`:631`).
- **Envelope-splice reuse (§3):** Steps 1–2 (each envelope term = 0; non-envelope prefix > 0) are exactly the
  factor-vanishing pattern of `Mval_setTail_runMinWidth`; Step 3 (splice `b`) is an `Adm`-membership +
  term-by-term `Mval` comparison — tractable with these lemmas + `leaf_mem_Adm` machinery (d), no new algebra.

## (d) The leaf / fold family — `EngineConstruction.lean` (+ `ResolutionTree.lean`), sorry-free

The A→C spine (task #21–23) that folds invariants to leaves; t04 reads terminal divisors off it.

- `leaves_isFullMono` (`:2461`) — the WF-induction fold (OracleInv+MvalCoh to leaves → `IsFullMonomialization`).
- `leafOfState` (`:1754`) + `t0Indices` (`:1719`) — the leaf constructor; analytic side = the `t̃=0` sublist.
  `leafOfState_rootLedger` (`:1790`). **Placeholder-chart caveat: `leafOfState.chartMap = id` today** — the
  REAL fold is t04's carrier work (see [[naming]] carrier disambiguation).
- `leaf_mem_Adm` (`:1313`), `_single` (`:1334`), `_t0` (`:1552`) — the `P ⊆ Adm` direction (needs `0 < L`).
- `leaves_resRank_zero` (`:2517`) — every leaf has `resRank = 0`, so `terminalExponents` (`ResolutionTree.lean:284`)
  = the `divExp` lists only (the residual `[]`). **This is the reduction t04's §ii uses**: `minAdm ∈
  terminalExponents ⟺ ∃ leaf `l`, ∃ analytic `k`, `l.divExp k = minAdm`** (t04-handoff §2).
- `conRoot_steps` (`:2561`) — the base wireability (root steps for genuine `M`); `leaves` (`ResolutionTree.lean:195`).
- **`srcBox.Nonempty` (slot 6):** `leafOfState`'s srcBox = `paramsEquivFlat ⁻¹' cubeBox 1` — nonempty (cube at
  radius 1, needs `0 ≤ 1`); cheap (t04-handoff §2).

## (e) The coverage kit — `Engine/`, sorry-free (feeds `chartBridge_buildTree`, the SIBLING hole; carrier must line up)

*Not t04's hole (that is `o5_realization`), but t04's CARRIER (the real `localSub`s + chart fold) is the
prerequisite coverage's 3 Props consume — the carrier's per-edge fields MUST line up with these signatures.*

- `pivotChart` atom (`PivotCover.lean:43`) + `pivotChartDom` (`:49`); a.e.-InjOn `pivotChart_ae_injOn`
  (`PivotInjOn.lean:47`, from `pivotChart_injOn` `:25` + `pivotChart_exceptional_null` `:40`).
- `node_pivotCover_of_atom` (`PivotCoverFold.lean:187`) — per-node cover from the pivot atom; the SHEARED
  variant `node_pivotCover_of_atom_sheared` (`ShearReconcile.lean:42`) carries the extra `ψ : Params M ≃ₜ
  Params M` gauge (the Q1b single-ψ; `ψ = id` on ledger-only case-1(1) merge edges). **Carrier constraint:**
  each edge's `localSub` must equal `ψ (q.symm (Prod.map (pivotChart (pivotOf e)) id (q ·)))` for these to
  apply — this is the shape t04's carrier emits (t04-handoff §3; journal tick 163 4-part spec).
- `chartBridge_of_pieces` (`ChartBridgeWiring.lean:59`) — **PROVEN implication** (the o5-fed Props enter as
  typed hypotheses over a fold-form `χ` parameter; `hχ : l.chartMap = χ l` bridges to the record). t04's carrier
  makes `l.chartMap` the real fold so `hχ` holds BY CONSTRUCTION.
- **Near-miss / stale:** `PivotCoverFold.lean:8` docstring still says "bodies are `sorry`, held for review" —
  STALE; the theorem is proven. Do not read it as a live hole.
