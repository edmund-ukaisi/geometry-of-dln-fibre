# Overlay — naming forwarding-pointers (cartographer, curated layer)

*Every rename leaves a pointer here so old references stay resolvable. Pointers ACCUMULATE — the
chart-era sections below the re-root marker still resolve old references into the retired
parts-bin (read them through `Engine/RETIRED.md`; do not treat their "live/in-flight" framing as
current).*

## ═══ RE-ROOT #1 (2026-07-21, tip 70a8ec6cf) — the A–E frame ═══

### Declaration renames this phase (old → new)

- **`AtlasRealizes` → `AtlasRealizesExponents`** (`DLN/Aoyagi/RecursionAdapter.lean:55`) —
  rev-monument-adapter precision escalation (77c7b6a39): the seam predicate names exactly what it
  checks (exponent realization), and clause (ii) was simultaneously WEAKENED to only-the-minimizer
  (the geometric obligation is STRICTLY weaker than pre-rename references suggest). ⚠ residual:
  docstring `:77` still says `AtlasRealizes` — flagged for the owner.
- **`rlctAt_mono_of_ae_le` → `rlctAt_mono_of_eventually_le`** (`Core/Aoyagi/IdealInvariance.lean:213`)
  — seat-A statement-lock repair: the hypothesis is an EVENTUAL (germ) domination `∀ᶠ`, not an
  a.e. one. Weighted twin landed as `wrlctAt_mono_of_eventually_le` (`:401`); the set-level form is
  `wLocalAdmissibleExponents_subset_of_eventually_le` (`:358`). No `_of_ae_le` name survives (grep 0).
- **D=2 blow-up name-cousins `…2`-renamed** (leaf-2 integration, 70a6c150d + 7f2e83edf; the
  general `OriginBlowup.lean` owns the bare names — CLAUDE.md: the general file is the canonical home):
  - `ball_subset_iUnion_blowup_image` (D=2) → `ball_subset_iUnion_blowup2_image`
  - `jacWeight_blowup_jac` (D=2) → `jacWeight_blowup_jac2`
  - `monomialFam_blowup_bexp` (D=2) → `monomialFam_blowup_bexp2`
  - `volume_blowup_excep` (D=2) → `volume_blowup_excep2`
  Same names in `OriginBlowup.lean` = the GENERAL lemmas (different constants — e.g. general
  `jacDet_blowupMap` needs `hD : 2 ≤ D`). The rest of `BlowupResolution.lean` was authored with
  `2`-suffixes (`blowupMap2`, `blowupChart2`, `blowupResolution2`, …), not renamed.

### Headline names (disambiguation — three near-cousins, all live)

- **`aoyagi_learning_coefficient_via_engine`** (`DLN/Aoyagi/LearningCoefficient.lean:299`) — THE
  summit (A–E frame): `rlctGlobal = cCodim/2`, cite-free value, +sorryAx from the monument only.
- **`aoyagi_learning_coefficient`** (bare, `Skeleton.lean:1685`) — the OLD chart-era mint anchor
  (λ = aoyagiLambda form, conditional stack); NOT the summit. Charter §1's "corollary" prose name
  refers to the summit's content — a close-phase reconciliation call for the controller.
- **`aoyagi_learning_coefficient_gen` / `_L1` / `_L2`** (`Validate/HeadlineGenAssembly.lean` etc.)
  — the banked predecessor value lane (hbox-conditional `_gen`; unconditional L=1/L=2 endpoints).

### Chart-era map node ids → disposition (claims.yaml re-root; old yaml @ 70a8ec6cf^ in git)

- `mint-repoint` → **superseded by `aoyagi-summit`** (the mint/hbox wiring never executed; the
  summit landed as `_via_engine` on the ideal route).
- `hbox-root` → **retired with the chart engine** (charter §1: hbox is the corollary's analytic
  shadow — "falls out of A+B or is decided false by them"). No live node; trail = `RouteMBoxReduction`.
- `engine-route`, `resolution-tree`, `case-step-lemmas`, `monomialization-termination`,
  `coverage-theorem`, `region-glue`, `gendivexp-support-redesign` → **retired → `chart-engine-retired`**
  (the dead-route registry entry; salvaged kernel = the adapter's four roots).
- `exponent-ledger-bridge` → content survives in **`object-d`** (`qipMin_eq_minAdm` +
  `divisorMin_eq_cCodim`) + the adapter seam.
- `reduction-layer`, `theorem4-localization` → content survives in **`corollary-reduction`**
  (deepest-point/homogeneity transport, `GlobalHomog`).
- `rr4-precedent` → retired guard (outer-plumbing precedent; still on disk,
  `Validate/RouteMBoxThresholdRR4.lean`).
- `naked-weight-route`, `decorated-descent-route` → KEPT as exit nodes (battery anchors).

### Files archived at this re-root (verbatim moves, git-tracked)

`overlay/archive/{banked-families,dead-routes,landmark-cards,paper-anchors,import-hygiene,wiring-endgame}-chart-era.md`.
The live paper-fidelity registry is now **compass.md § Paper-fidelity ledger** (elder-owned).

### Thread-dir numbering — collision disambiguation (carto pass #2, 2026-07-21 evening)

Two `threads/41-*` dirs coexist (suffix-disambiguated, the established convention here —
`16-`/`18-`/`19-`/`40-` all have the same shape). **NO rename** (expensive post-merge; both are
committed/merged — `41-rho-count-object` merged at `0abb4c8e1`). A pointer resolves it:

- **`threads/41-order-count/`** — seat-E (lean-formaliser), branch `expedition/aoyagi-engine-E`.
  **P6.1** band arithmetic, node `e-p61-band-arithmetic` (`Core/Aoyagi/OrderCount.lean`); Tier-1
  statement card.
- **`threads/41-rho-count-object/`** — pnp (decorrelated), branch `thread/41-rho-count-object`.
  **P6.2** ρ count-identification, node `e-p62-count-identification`; the deepest-stratum max-crossing
  certificate + `rho_battery.py` (now graduated to `battery/` with `_edgespec_traversal_334.py` as its
  runner-skipped helper).

**SEMANTIC split `P6 → P6.1 / P6.2` — elder register event-update LANDED `ab106f1a4`.** Old references
to a single "P6 — Lemmas 4–5, θ = a(ℓ−a)+1" now resolve to two entries (owed-register §2 P6 split + §0 O6):
- **P6.1** = band arithmetic — LANDED both tiers (`bandCount_eq` + `perJCard_eq_paper`); node
  `e-p61-band-arithmetic`; dir `threads/41-order-count/`.
- **P6.2** = count-identification — pnp-gate DISCHARGED, IN-SHAPING; node `e-p62-count-identification`;
  dir `threads/41-rho-count-object/`. **Object refined:** ρ = deepest-stratum max-crossing = **max CHAIN
  of binding minimiser profiles under componentwise ≤** (chainHeight). The thread-41 certificate's
  *antichain* speculation was CORRECTED to a max-CHAIN by seat-E's battery (1018 cores; witness
  [2,2,2,2,2]) — read that certificate THROUGH this correction; owed-register §2 P6.2 + compass
  § Paper-fidelity ledger CODA are authoritative.

## ═══ chart-era pointers below (HISTORICAL — read through RETIRED.md) ═══

*Created pass #1; **REFRESHED pass #2 (2026-07-18)**: the council-adopted restructure has LANDED
(tick 37 r2-validate), so pass-#1's "Pending (unlanded)" block moved to Landed; added the
new-this-expedition modules + the namespace quirk + two pin moves.*

## Landed since pass #1 (was "Pending", now in the root tree)

- **Edge-labelled carrier — LANDED (tick 37, r2-VALIDATED).** `Edge {case, subst, child}` +
  `branch (n) (edges : List (Edge M))`; `StepData` carries no `case`; leaf `chartMap` = derived
  path-fold. `Engine/ResolutionTree.lean`. The unary `StepInvariant` is GONE from root
  (pass #1 flagged it still present — resolved).

- **`ChartsCover` → `ChartBridge` — LANDED + STRENGTHENED (tick 46).** Per-leaf CoV bridge (chartMap +
  MeasurableSet-bounded `srcBox` + resRank + LeafPullback + LeafJacobian + a.e.-InjOn + image cover).
  Interface FROZEN + abstract-field-gate-cleared (tick 51). **PIN CORRECTION (cartographer-4, HEAD
  `0ae14ade9`): the `def ChartBridge` is in `Engine/EngineDefs.lean:75`** (a `Prop`), NOT
  `EngineObligations.lean` as pass-#2 wrote — `EngineObligations` only USES it (`chartBridge_buildTree`
  `:50`, `resolutionOf`-form `:123`). The re-typing batch (WIP `e849a4b11`, unmerged here) edits this
  `EngineDefs` def → flat virtual-leaf atlas.

- **`StepInvariant` (unary) → `StepRel` (faithful) — LANDED (tick 37/44).** `StepRel := rootLedger
  e.child = stepUpdate n e.case e.subst` (reads `e.child`; discharge rfl-class). `EngineObligations`.

- **`canonicalResolution_224` → split — LANDED (tick 30+).** `canonicalResolution224_arithmetic`
  (clean-three bank; the carrier-independent conjuncts) + `canonicalResolution224` (`@[blueprint]`
  forecast, its ChartBridge conjunct sorried at `Engine/CanonicalWitness224.lean:130`). Both live in
  `CanonicalWitness224.lean`. The AxCheck clean-three entry is on `_arithmetic`.

## New modules this expedition (recorded for reference)

- `Engine/EngineConstruction.lean` — the construction termination spine (rung 2A/2B: `ConState`,
  `StateInvariant`, `conRel_wf`, per-case μ-descent). NEW tick 58–59.
- `Engine/CanonicalWitness224.lean` — the (2,2,4) faithful-`stepUpdate` witness (renamed home of the
  split above).
- `Engine/CoRank2Spike.lean` — the corank-2 (3,3,4) coordinate-index de-risk (rung 2C). NEW tick 58.
- `Engine/RegionGlueGlobalize.lean` — homogeneity local→global (glue globalization half). NEW tick 45.
- `Engine/RegionGluePerLeaf.lean` — per-leaf area-formula read (currently only the Haar/Borel
  instances; the area-formula theorem is Module B, in flight). NEW tick 57+.
- `Validate/RegionGlueModelRead.lean` — the flat-coordinate `model_read_lt_top` (Module A). NEW tick 60.
- `Foundations/S1ScalingBridge.lean` — the abstract scaling bridge `lintegral_rpow_neg_smul_bridge`.
  NEW tick 40.

## Namespace quirk (FLAG — fold fix into the D1L2 re-home commit per [[import-hygiene]])

- **`RegionGlueGlobalize.lean` + `RegionGluePerLeaf.lean` live in `Engine/` but declare `namespace
  DLNFibre.DLN.RLCT`** (the parent), NOT `DLNFibre.DLN.RLCT.Engine`. The other 6 Engine modules
  correctly declare `.Engine`. So their decls (`routeMLayerBoxIntegral_lt_top_of_small_box`,
  `instIsAddHaarMeasureParams`, …) resolve at `DLNFibre.DLN.RLCT.*`, not under `Engine`. First flagged
  tick 45 (non-blocking). A reader qualifying with `Engine.` will NOT find them.

## Pin moves since pass #1 (old references now STALE)

- **`minAdm_le_Mval` → `minAdm_le_Mval_toNat` at `Validate/RouteMState.lean:259`** (was pinned to
  RouteMLayerSplit in pass-#1 banked-families). The minAdm-as-minimum direction the
  `exponent_ledger_bridge` / theorem4 need. See [[dead-routes]] (MinAdmMono trap).
- **The two engine holes moved line:** `monomialization_terminates` at `EngineObligations.lean:182`
  (sorry `:184`), `region_glue` at `:244` (sorry `:248`). Pass-#1 / priorities.md wrote `:142`/`:206`
  — STALE (the ledger + strengthening commits shifted them ~40 lines).

## Landed / stable (no forwarding needed, recorded for reference)

- **"RR4.lean" = `Validate/RouteMBoxThresholdRR4.lean`** (no bare `RR4.lean`). Assembly:
  `routeMBoxThresholdFinite_rr4_of_schurRecStep` (`:219`).
- **`aoyagi_learning_coefficient` (bare, mint anchor) at `Skeleton.lean:1685`** (legacy stub
  re-pointing at mint); the hbox-conditional form is `aoyagi_learning_coefficient_gen`
  (`HeadlineGenAssembly.lean:55`). `claims.yaml` `lean:` points at the bare name, `evidence:` at
  `_gen` — anchor/evidence split across modules (intended; see [[landmark-cards]] mint card). R5 wiring
  must land the bare name on `_gen`, avoiding the 3 legacy Skeleton stubs (see [[dead-routes]]).

## Close-phase rename list (owed at expedition close)

- **`tStar_le_tPrev` / `tStar_le_Msucc` — misleading `tStar_` prefix (rev-s3, tick 191).** Both are
  GENERIC-`Adm` lemmas over an arbitrary `T ∈ Adm M` (`RouteMAchieverPath.lean:36,52`), NOT specific to the
  achiever `tStar` — the prefix wrongly suggests `tStar`-only scope. Consumers: `RouteMAchieverPath.lean:112,
  115`, `RouteMAchieverStructAdm.lean` (several), and `Engine/O5Realization.lean:68,70` (§3 used them). Rename
  to an `adm_`-prefixed generic name at close; leave a forwarding pointer here.

## Watch (rename risk on landing)

- The full-`T` chooser (R1 open) + `genDivExp` redesign (R4) will re-shape `LeafData`/`StepData`
  ledger fields. The obligation projection names (`case_step_invariant`, `reduction_layer`,
  `coverage_theorem`, `exponent_ledger_bridge`, `resolutionOf`/`resolutionOf_spec`) are stable
  anchors; their statements are not. Re-verify at the next pass.

## D-arc vocabulary (cartographer-3, 2026-07-19) — cert/journal terms → Lean names

> **⚠ STALE on `o5_realization` (carto tick 348).** This section predates the o5 close. `o5_realization`
> is now CLEAN-THREE (t06 s4) — it is NO LONGER a hole. So "t04's hole" (below) and "the two named
> holes → chartBridge + o5" are superseded: the engine's ONE live analytic hole is `chartBridge_buildTree`
> (via the `LeafPullback` conjunct). The line pins (`:52`/`:63`) have also drifted (chartBridge is now
> `:49-52`, the drop-(D) projection). See the Final-arc forwarding pointers below + [[banked-families]]
> § Rung → hole map (refreshed). The cert/journal→Lean *name* mappings below remain valid.

*The o5/D arc's prose vocabulary and where it lands in the tree. Several cert names differ from the Lean
decl (flagged) — the reuse index [[banked-families]] § D-ARC has the full pin table.*

- **"o5-∈" / "o5 realization" / "minAdm ∈ terminalExponents"** → the `@[blueprint]` sorried theorem
  `o5_realization` (`EngineObligations.lean:63`), t04's hole. FUTURE proven name: the
  `minAdm_mem_terminalExponents`-class (naming pin, elder-gate7 tick 152) — **NEVER** `profileSet_eq_Adm`,
  `*_complete`, or `*_eq_Adm` (⊇ Adm is FALSE, [[dead-routes]] ledger #4). Its `.1` is the attainment half of
  slot 5 (paired with the PROVEN lower bound `minAdm_le_terminalExponents`, `EngineConstruction.lean:2540`,
  consumed at `EngineObligations.lean:79`); its `.2` is slot 6 (live attainment at a nonempty srcBox).
- **"the two holes" / "the two named holes"** → `chartBridge_buildTree` (`EngineObligations.lean:52`) +
  `o5_realization` (`:63`). NOT "monomialization_terminates + region_glue" (that framing is stale post-tick-165;
  [[dead-routes]] census update).
- **"STEP1"** (cert-compchain-o4 §6, cert-o5 §4) → `step1_dominates` (`EngineConstruction.lean:904`).
  **"WeakDec"** (both certs) → `WeakDecInv` (`:540`). **"MvalBoundaryInv" reachability** → the THEOREM
  `MvalBoundaryInv_conOracle_stepChildren` (`:2261`), not a def.
- **"Clearable" (about to be reified)** → elder-gate7 tick 152 REIFY-NOW: t04 lands the `Clearable` predicate
  (cert-o5 §1 boxed form) + a SORRIED library-surface theorem `P(M) = Clearable-Adm(M)` (typed honest name;
  docstring cites ledger #4; AxCheck watch `+sorryAx` until R7). It is NEVER an `IsFullMonomialization`
  conjunct — statement now, proof at R7 (task #27). Not yet in the tree as of HEAD `da6567505`.

## The two carriers — DISAMBIGUATION (cartographer-3, 2026-07-19)

*"Carrier" is overloaded across the map; two DISTINCT objects, do not conflate.*

- **LEDGER carrier (R1)** — the faithful `RootLedger`/full-`T`/`genDivExp` node-data that the μ-descent + the
  divisor/profile bookkeeping read. Landed as the A→C spine (`ConState`, `RootLedger`, `stepUpdate`,
  `leafOfState` divisor fields). This is what (a)–(d) of the reuse index bank.
- **CHART-EMISSION carrier (R2 pre-rung, t05's carrier arc, task #8)** — the per-edge chart surface.
  `ChartSubst` ALREADY IS the per-edge surface (`localSub` + `jacDivCount`/`jacPow`) — populate it, no sibling
  bundle (t04-handoff §3). This is the R2/R3 prerequisite the coverage kit ((e)) consumes; navigator-3 (tick
  168 E) made it an EXPLICIT R2 pre-rung, distinct from R1's ledger carrier. The spine is provably
  `chartMap`-blind, so populating charts leaves the (a)-(d) reuse kit and the two named-hole types unchanged.
  **FINAL SCOPE REVISED (tick 187+, R-b decisive) — supersedes the tick-163 "4-part spec":**
  - **field 3 is `α_e` SOURCE frames, not a target `ψ`** — per-edge `localSub_e = β̃_e = β_e ∘ α_e⁻¹`
    (det-1 source reparam; single-ψ and R-a target-ψ are BOTH DEAD, [[dead-routes]] carrier-arc kills);
  - **the spine path-accumulator (threading the fold into `leafOfState.chartMap` during `buildTree`) is
    STRUCK MOOT** (tick 187) — the atlas is realized via an auxiliary geometric tree `t_geo` (proof-internal;
    spine untouched), NOT threaded into `leafOfState.chartMap`;
  - **the coordinate split `q` must be CONCRETE in the carrier** (tick 185), the companion of the β field,
    not `node_pivotCover_of_atom`'s existential;
  - **per-node `d_center` family data** (case-1 `= runLen·resCols + 1`, case-2 `= (M(S)−J)·(M^{(S+1)}−J)`).
  The positive reuse index for all of this is [[banked-families]] § CARRIER-ADJACENT (cartographer-4).

## Endgame forwarding pointers (cartographer-6, 2026-07-19, HEAD `c342c55fb`)

*The center-split / d_center naming CHURNED node → edge → node across the endgame; both keyings now
coexist with distinct roles. Recording the live homes so old references (and the pass-#4
wiring-endgame §3 sweep, which is now wrong on `qNodeOf`) stay resolvable.*

- **`qNodeOf` — LIVE, per-NODE (`QNodeCarrier.lean:505`).** The center-split `Homeomorph` all the
  node's pivots share (per-node cover ruling, elder-gate9). Consumed by `geoChartMap`/`geoAtlas`
  (`GeoChart.lean`) + the fold Jacobian. **⚠ CORRECTS pass-#4 [[wiring-endgame]] §3**, which listed
  "`qNodeOf` (node-keyed; landed edge-keyed) → rename → `qOfCenter` + `qEdgeOf`" — that is STALE:
  `qNodeOf` was RE-ADOPTED node-keyed (t09) and is the form the tree consumes. Do not treat `qNodeOf`
  as struck.
- **`qEdgeOf` — LIVE, per-EDGE (`QNodeChart.lean:110`).** Keyed on `dCenterOfEdge node e`. Coexists with
  `qNodeOf`; it is NOT a rename target of `qNodeOf` (different granularity). The per-node cover ruling
  made `qNodeOf` the consumed one; `qEdgeOf` remains as the per-edge companion.
- **`qOfCenter` (`QNodeChart.lean:53`) / `qOfCenterCLE` (`QNodeCarrier.lean:781`).** The parametric
  center-split given an injective selector `c` — homeomorph form / CLE (linear) form. `qOfCenterCLE` is
  the fold Jacobian's conjugation input (fderiv reads it as a fixed CLE); `qNodeOf` is `qOfCenter`
  instantiated at the node's `cNodeOf` selector.
- **`dCenterOfEdge` (`QNodeChart.lean:64`) vs `dCenterOfNode` (`QNodeCarrier.lean:62`).** Per-edge count
  (drives the fan-out partition in `geomEdges`) vs per-node total (keys `qNodeOf`). Tie:
  `dCenterOfNode_edgeSum` (`QNodeCarrier.lean:117`, `Σ_e dCenterOfEdge = dCenterOfNode` on built branch
  nodes). NOT interchangeable.
- **`cNodeOf`** (in `QNodeCarrier.lean`) — the injective flat-coordinate selector the node blows up
  (`Fin dCenterOfNode → Fin flatDim`); `cNodeOf_injective` load-bearing. The earlier per-edge
  `dCenterOfEdge`-keyed `q` design is superseded here (the per-node cover shares one `cNodeOf`/`qNodeOf`).

- **single-per-node `ψ` — RETIRED (R-b source reparam).** `node_pivotCover_of_atom_sheared`
  (`ShearReconcile.lean:59`) survives ONLY at `ψ = .refl`; the "single-`ψ` covers a mixed node" reading
  is DEAD (pnp-psi T2). **DRIFT RESOLVED (carto, tick 348; nav-6 "ALREADY fixed").** The earlier flag
  (`:32-35` self-contradicting the model) is CLOSED: the module's RETIRE NOTE (`:13-21`) explicitly
  GOVERNS the provenance docstring below it — `:21` reads "The docstring below is kept for provenance;
  read it through this note." So the `:30-35` "single-`ψ` is the right model" text is retained
  provenance under a governing retire-note, not an unmanaged contradiction; no owner action owed. See
  [[dead-routes]] carrier-arc kills.

- **`o5_core` — DELETED (move-at-landing done, tick 189 ruling #3).** Was `EngineConstruction.lean:~2607`
  (sorry `:2611`). Its proven replacement is `o5_core_realized` / `tStar_realized`
  (`O5Realization.lean:882` / `:869`), clean-three. Any reference to `o5_core` in
  `EngineConstruction` is stale — the decl is gone; `EngineConstruction.lean` is 0-sorry again.

- **fold-Jacobian spine decls (t11):** `geoChartMap_fderiv_det` (`GeoJacobianSpec.lean:95`, per-edge
  atom), `abs_det_fderiv_foldr_comp` (`GeoJacobianFold.lean:60`, parametric fold). GATE-WIRED at
  `13b86217a` (AxCheck:12 import + watch lines; was a gate-orphan at the carto6 snapshot) —
  [[wiring-endgame]] §1a.

## Final-arc forwarding pointers (carto-standing, 2026-07-20, ticks 336–348)

- **"GeoInvValWalk" → `GeoInvVal.lean` (name clarification).** Journal/charge references to a
  "GeoInvValWalk" module resolve to `Engine/GeoInvVal.lean` (loss-t15, PHASE 3b) — the `Inv_val`
  value-invariant home. Its t14-INDEPENDENT consumer side is LANDED (0-sorry): `frobSq_of_diagonal`
  (`:36`), `leafDiagFrob_of_prodDiag` (`:61`). The `Inv_val` statement + four maintenance signatures
  land there once t14's walk fixes the shared plumbing (still in flight).
- **`geoAtlas_cocycle` / `geoAtlas_fold_det` (`GeoFoldRegroup.lean:1069` / `GeoLeafJacobian.lean:57`).**
  The fold-Jacobian wall, closed ticks 336–337. `geoAtlas_fold_det` is the cocycle STRENGTHENED to the
  R7 full-ledger ∃-form at `conRoot`/`id`; `geoAtlas_leaf_leafJacobian` (`GeoLeafJacobian.lean:76`) is
  the per-piece `LeafJacobian` bundle (tick 338). Supersedes the retired `GeoJacobianSpec:37` SPECIFY
  sorry (deferred tick 260, gone). The four maintenance theorems: `ledger_det_maintenance_{case2,
  case11,case12,rollover}` (`GeoFoldRegroup.lean:805/852/903/968`).
- **"GeoAtlasTransfer" — NOT YET ON DISK (placeholder name).** The witness-swap transfer batch
  (α-atlas, R-split stage 3) has no landed module yet; the file name is not fixed. When it lands, add
  the forwarding pointer here and card it in [[banked-families]] (FINAL-ARC § FORWARDING POINTER).
- **Witness atlas: `geoAtlas` (id) → `geoAtlasNorm (alphaGauge …)` (in flight).** The faithful witness
  re-points from the fork-15 id placeholder to Aoyagi's normalized chart (elder tick 340). References
  to the discharge "over `geoAtlas`" are the pre-swap form; post-swap the atlas is `geoAtlasNorm
  alphaGauge` (α = `residualSchurShear`, `GeoAlphaGauge.lean`).
