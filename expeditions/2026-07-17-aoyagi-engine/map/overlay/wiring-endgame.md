# Overlay — wiring-endgame (cartographer-5, pass #4: MAP + WIRINGS)

*Convened 2026-07-19 (journal tick 238), OPERATOR-requested, before the discharge batch. The endgame's
module graph + the `chartBridge_buildTree` discharge wiring checklist, verified FROM THE IMPORTS at
branch `expedition/aoyagi-engine--carto5` @ `64fe1a7f2` (= origin/expedition/aoyagi-engine tick 238),
NOT from memory. The remaining engine debt is ONE hole, ONE lane: `chartBridge_buildTree` (o5_realization
went clean-three at tick 218). Coverage-t08's tide is the sole path to the flip.*

## 0. The one-line state

`monomialization_terminates` / `engine_box_threshold_finite` are `+sorryAx` via **EXACTLY**
`chartBridge_buildTree` (`EngineObligations.lean:51-53`, a `sorry`). Discharging it flips the hbox event
the R5 mint re-point waits on. The discharge is `chartBridge_of_pieces` fed the coverage atlas — the
suppliers exist, but four of them are OUTSIDE `EngineObligations`' current import closure (two are
gate-orphans reachable from nothing).

## 1. The endgame module import/consumption graph

**Aggregator closure path:** `DLNFibre.lean:741` → `AxCheck.lean`. `AxCheck.lean:1-8` imports (direct):
CanonicalWitness224, EngineDriver, ClearableReify, NumDivFlatBound, O5Realization, QNodeChart, GeoChart,
DivBirthReach. Also `DLNFibre.lean:1479` imports `Engine.PivotCover` direct. The green-gate is
`lake build DLNFibre` = this transitive closure (aggregator note `DLNFibre.lean:273-275`).

**Import edges of the 10 named modules** (`X → Y` = X imports Y; grep-verified `^import`):

    ShearReconcile   → PivotCoverFold                    (+ Mathlib FDeriv/Transvection/Determinant)
    PivotInjOn       → PivotCover                        (+ Mathlib.MeasureTheory.Constructions.Pi)
    ChartBridgeWiring→ EngineDefs
    GeoChart         → QNodeChart, ShearReconcile
    QNodeChart       → CenterIndices                     (+ ParamsFlatLinear, Homeomorph.Lemmas)
    CenterIndices    → EngineConstruction
    DivBirthReach    → NumDivFlatBound
    NumDivFlatBound  → EngineConstruction
    ClearableReify   → EngineConstruction
    O5Realization    → ClearableReify, NumDivFlatBound

    (support: EngineConstruction→EngineDefs→ResolutionTree; PivotCoverFold→EngineDefs,PivotCover;
     EngineObligations→EngineDefs,EngineConstruction,O5Realization,RegionGlueAssembly;
     EngineDriver→EngineObligations; PivotLeafClauses→EngineDefs,PivotCover [consumed by FlatCubeLeaf])

**Reachability of the 10 from the aggregator (gate-coverage):**

| module | in `DLNFibre` closure? | path / consumers |
|---|---|---|
| GeoChart | YES | `AxCheck:7` direct |
| QNodeChart | YES | `AxCheck:6` direct + GeoChart→QNodeChart |
| CenterIndices | YES | QNodeChart→CenterIndices |
| ShearReconcile | YES | GeoChart→ShearReconcile |
| DivBirthReach | YES | `AxCheck:8` direct |
| NumDivFlatBound | YES | `AxCheck:4` direct + DivBirthReach→ + O5Realization→ |
| ClearableReify | YES | `AxCheck:3` direct + O5Realization→ |
| O5Realization | YES | `AxCheck:5` direct + EngineDriver→EngineObligations→O5Realization |
| **PivotInjOn** | **NO — ORPHAN** | NO consumer anywhere in the tree; escapes `lake build DLNFibre` |
| **ChartBridgeWiring** | **NO — ORPHAN** | NO consumer anywhere in the tree; escapes `lake build DLNFibre` |

⚠ **Two gate-orphans.** `PivotInjOn` and `ChartBridgeWiring` are imported by NOTHING — neither in
`AxCheck` nor the aggregator nor any Engine module. Both are sorry-free today (verified), but a break or
sorry in either escapes the green-gate until the discharge pulls them in (exactly the failure the
aggregator warns about at `DLNFibre.lean:273-275`). The discharge batch fixes this by importing both
(see §2). Until then they are direct-build-only.

## 2. The `chartBridge_buildTree` discharge — WIRING CHECKLIST (the operative deliverable)

The discharge fills the sorry at `EngineObligations.lean:51-53` via `chartBridge_of_pieces`
(`ChartBridgeWiring.lean:27-41`), which bundles `ChartBridge M t` from `atlas + himg (A) + hleaf (B, 8
per-piece clauses) + hexp (C)`. Piece-suppliers and their homes:

| discharge input | supplier decl | home (file:line) | in EO closure now? |
|---|---|---|---|
| `chartBridge_of_pieces` (the bundler) | `chartBridge_of_pieces` | ChartBridgeWiring.lean:27 | **NO** |
| `atlas` + cover (A) + LeafPullback/LeafJacobian (B) + hexp (C) | `geometricLeafPaths`/`geoChartMap` + coverage tide (task #8, in flight) | GeoChart.lean:45,60 | **NO** |
| cover-fold per-node atom | `node_pivotCover_of_atom` / `_sheared` + `reparam_image` | PivotCoverFold.lean:187 / ShearReconcile.lean:59,108 | **NO** (via GeoChart) |
| (B) coord clauses: divCoord/resCoord inj + disjoint | `leaves_chart_clauses_conRoot` | DivBirthReach.lean:325 | **NO** |
| (B) a.e.-InjOn `∃N null, InjOn chartMap` | `pivotChart_ae_injOn` (transported) | PivotInjOn.lean:47 | **NO** |
| numDiv ≤ flatDim (underpins injective divCoord) | `leaves_numDiv_le_flatDim` | NumDivFlatBound.lean:262 | YES (via O5Realization→NumDivFlatBound) |

### 2a. Import additions into `EngineObligations` (the four) — ORDERED

The proof site is `chartBridge_buildTree` in `EngineObligations.lean`. (If the discharge is instead
staged in a coverage helper module that EngineObligations imports, these four must be reachable from THAT
module — the set is the same.) None of the four are in EO's current closure {EngineDefs,
EngineConstruction, O5Realization, RegionGlueAssembly}:

1. `import DLNFibre.DLN.RLCT.Engine.ChartBridgeWiring`  — `chartBridge_of_pieces`.
2. `import DLNFibre.DLN.RLCT.Engine.GeoChart`  — atlas + cover + LeafPullback/LeafJacobian; transitively
   pulls QNodeChart, CenterIndices, ShearReconcile, PivotCoverFold.
3. `import DLNFibre.DLN.RLCT.Engine.DivBirthReach`  — `leaves_chart_clauses_conRoot`; pulls NumDivFlatBound
   (already reachable).
4. `import DLNFibre.DLN.RLCT.Engine.PivotInjOn`  — `pivotChart_ae_injOn`; pulls
   Mathlib.MeasureTheory.Constructions.Pi.

⚠ **Import-hygiene note (ratified whitelist rule, [[import-hygiene]]).** Adding GeoChart drags the
analysis-heavy ShearReconcile cone (Mathlib FDeriv/Transvection/Determinant) into the currently-LIGHT
EngineObligations (31 transitive). Weight bump expected; the discharge commit owes a controller docstring
note per the rule, OR the discharge is homed in a coverage module (keeping EO light) that EngineDriver's
lane already pays for. Judge at discharge time.

### 2b. AxCheck watch flips — `+sorryAx` → MUST-clean-three

These four `#print axioms` lines change disposition when the discharge lands (rewrite the adjacent prose
too):

- `AxCheck.lean:1302` `Engine.chartBridge_buildTree` — comment `-- +sorryAx (← T3 coverage lane)` → clean-three.
- `AxCheck.lean:1307` `Engine.monomialization_terminates` — `-- +sorryAx via EXACTLY chartBridge_buildTree` → clean-three.
- `AxCheck.lean:1299` `Engine.engine_box_threshold_finite` — prose 1296-1298 ("this line flipping to clean-three IS the hbox event the mint re-point waits on") → clean-three.
- `AxCheck.lean:1295` `Engine.region_glue` — prose 1291-1294 (`+sorryAx` through the `resolutionOf` type) → clean-three.
- **VERIFY (not asserted):** `AxCheck.lean:1285` `Engine.canonicalResolution224` — "EXPECTS sorryAx until
  the P8 tide lands (its ChartBridge conjunct sorried)". Confirm whether the (2,2,4) witness's ChartBridge
  conjunct shares the `chartBridge_buildTree` discharge or is a SEPARATE concrete-witness sorry; only then
  decide if this line also flips.

Regression guards that MUST STAY clean-three (unchanged by the discharge): o5_realization (`:1306`),
isFullMonomialization_buildTree_conRoot (`:1310`), minAdm_le_terminalExponents (`:1311`),
leaves_numDiv_le_flatDim (`:1314`), qOfCenter (`:1317`), DivBirthInv_conOracle_stepChildren (`:1320`),
leaves_chart_clauses_conRoot (`:1323`), clearable_of_minimizer/`_tStar` (`:1326-1327`),
tStar_realized/o5_core_realized (`:1330-1331`).

### 2c. The clause (D) gate (task #10) — HONEST STATE (the dispatch's "already pre-staged" is NOT accurate)

- (D) is **NOT** in the `ChartBridge` def body. `EngineDefs.lean:96-109` is only conjuncts (A)∧(B)∧(C).
- (D) exists as **prose only** — `EngineDefs.lean:86-95` ("HONEST FORM (the (D)-less window)… GATE
  (cordon-checked): (D) must be IN this type BEFORE `chartBridge_buildTree`'s discharge lands").
- `chartBridge_of_pieces` (`ChartBridgeWiring.lean:27-41`) bundles only A/B/C: `⟨atlas, himg, hleaf,
  hexp⟩` — there is NO (D) argument pre-staged.
- The dispatch's "the (D)-conjunct + destructure line (already pre-staged, cite it)" — the only stable
  destructure is `monomialization_terminates`'s assembly `⟨…, chartBridge_buildTree M hL, …⟩`
  (`EngineObligations.lean:94-100`, the ChartBridge slot at `:98`). That line is (D)-**agnostic** and needs
  NO change when (D) lands additively. There is no other pre-staged (D). **Cartographer read: (D) is
  un-landed content, not pre-staged code.** Task #10 is genuinely open.
- When (D) lands (additive, def-only touch; `region_glue` + the CanonicalResolution projection are
  agnostic — `EngineDefs.lean:94`):
  (i) add the 4th conjunct to `ChartBridge` (`EngineDefs.lean:~109`) — the geometricLeafPaths fidelity
      (each piece's `chartMap` = the real `β∘ψ` fold of a `t`-path, not an opaque map);
  (ii) add the 4th arg `hfid` to `chartBridge_of_pieces` + `⟨atlas, himg, hleaf, hexp, hfid⟩`
      (`ChartBridgeWiring.lean:27-41`);
  (iii) the discharge must supply `hfid`.

### 2d. Retirement flags (task #15)

**(a) PivotCoverFold spine-fold — SURGICAL retire (do NOT delete the file).** The tree-fold statements
target the SUPERSEDED cover shape `⋃ l ∈ leaves t, l.chartMap '' l.srcBox` via `e.subst.localSub` (the
struck spine-localSub design); on the constructed tree every `e.subst.localSub = id`, so the fold collapses
to `⋃ e, leafPathImages e.child` and carries no geometry. The current type's (A) clause is the flat-atlas
`⋃ c ∈ atlas, c.chartMap '' c.srcBox` (`EngineDefs.lean:98-100`), built by GeoChart's own
`geometricLeafPaths`. RETIRE (no external consumer):
  - `leafPathImages`/`edgesImages` (`PivotCoverFold.lean:57-64`)
  - `leafPathImages_branch` (`:69-86`)
  - `OwnCovers` (`:91-92`), `ownCovers_branch` (`:99-110`)
  - `imgAcc`/`imgEdgesAcc` (`:122-144`), `leafPathImages_eq_biUnion_leafPaths` (`:148-151`)
  - `leafPaths_mapFst`/`edgesLeafPaths_mapFst` (`:156-171`)
  - `chartBridge_imageCover_of_ownCovers` (`:224-239`) — produces the wrong (superseded) clause shape.

**KEEP** `node_pivotCover_of_atom` (`:187-218`) — LIVE: consumed by `ShearReconcile`
(`node_pivotCover_of_atom_sheared` `:59`, used at ψ=refl) + `PivotLeafClauses`; the per-node
pivot-completeness atom the flat-atlas cover reuses via `reparam_image` (`ShearReconcile.lean:108`).
Coupling: `ShearReconcile.lean:30` docstring names `leafPathImages`/`ownCovers_branch` — update that line
when they retire.

**(b) EngineObligations caveat — REWRITE (current span `39-50`, not `40-49`).** The block describes the
STRUCK design: "PLACEHOLDER charts / coherence clause `p.1.chartMap = p.2` holds trivially / edges must
carry real `localSub`s / `leafOfState.chartMap` = root→leaf `localSub` fold (thread a path-accumulator
through `buildTree`)". The new type is the flat virtual-leaf atlas (GeoChart `geometricLeafPaths` →
`chartBridge_of_pieces`); there is NO coherence clause `chartMap = χ` (`ChartBridgeWiring.lean:11-12`), and
the ledger spine stays `chartMap`-blind BY DESIGN (atlas decoupled from `leaves t`). Rewrite to: the fill
is the atlas, the placeholder `leafOfState.chartMap = id` is fine, the spine needs no chart content. (The
"STABLE under carrier change" sentence at `:46-49` is correct — it strengthens.) This rewrite absorbs the
lone LIVE-Lean `path-accumulator` reference (`EngineObligations.lean:46`).

## 3. Dead/stale reference sweep (design vocabulary)

| struck design | LIVE Lean hits | correction owed |
|---|---|---|
| `qNodeOf` (node-keyed; landed edge-keyed) | `CenterIndices.lean:9`, `:14` (docstrings) | rename → `qOfCenter` (parametric, QNodeChart.lean:53) + `qEdgeOf` (per-edge, `:110`); `q_node`/`centerSplit` → same |
| `path-accumulator` (spine fold) | `EngineObligations.lean:46` only | folds into the caveat rewrite (2b) |
| `single ψ` (single-per-node gauge) | `ShearReconcile.lean:20`, `:30-35` | already flagged by RETIRE NOTE `ShearReconcile.lean:13-21`; `:30-35` provenance mention goes moot with the spine-fold retire |
| With-variants (`LeafPullbackWith`/`LeafJacobianWith`, `χ` param) | **NONE in live Lean** (re-typing batch merged) | corrected the stale card banked-families.md:313-316 (this pass) |
| target-side gauge / "carrier populates ChartSubst.localSub" | **NONE** (clean) | — |

Historical-only (leave as record): `qNodeOf`/`path-accumulator`/`single-ψ`/With-variants in expedition
thread specs, RULINGS, journal, and Codex logs (`threads/**`). These are the archive, not stale code.

Stale line-number cross-refs inside PivotCoverFold docstrings (moot once the spine-fold retires; fold into
that commit): `:12` cites `EngineDefs.lean:76` (actual image-cover clause `:98-100`); `:223` cites
`EngineObligations.lean:65` (actual `coverage_theorem` `:133-135`); `:184`/`:38` cite
`EngineConstruction.lean:286`.

## 4. Predecessor-card correction (diff-then-judge)

`banked-families.md:313-316` SYNC NOTE (cartographer-4, HEAD `0ae14ade9`) claimed coverage-t08's
re-typing batch is "NOT merged" with `LeafPullbackWith`/`LeafJacobianWith` + the `χ` parameter "still
present". FALSE at this HEAD: the current `ChartBridgeWiring.lean` (read in full) has no With-variants and
`chartBridge_of_pieces` has no `χ`. Corrected in this pass (marked superseded, not silently rewritten).
