# Overlay — wiring-endgame (cartographer-6, pass #5 + placement addendum)

*ADDENDUM (tick 289, elder charge-4 — assembly placement check): §2e added (the (D) R-split mechanics,
verdict = CLEAN IMPORT-ADD no cycle); §1a orphan table + §2 refreshed to tick 289 (cover DONE tick 288;
GeoLeafJacobian new). The pass-#5 body below was verified at tick 265; deltas since are marked inline.*

*Convened 2026-07-19 (journal tick 265+, standing cartographer office, OPERATOR-requested). Pass #4
(cartographer-5) was verified at tick 238 (`64fe1a7f2`) and PREDATES two landings navigator-4 flagged:
the **0∈U cover reshape** (task #31) and the **geoAtlas reshape** (GeoChart / GeoJacobian / GeoCover
split). This pass re-verifies FROM THE LIVE TREE at HEAD `c342c55fb` (tick 265 addendum), NOT from
memory or from pass #4. What changed since pass #4: (1) the two gate-orphans pass #4 flagged
(`PivotInjOn` / `ChartBridgeWiring`) were WIRED at tick 241 — no longer orphans; (2) `o5_realization`
went clean-three (its crux `o5_core_realized` landed, t06 s4) — the last hole of
`monomialization_terminates` is `chartBridge_buildTree` ALONE; (3) `o5_core` was DELETED from
`EngineConstruction` (move-at-landing done) — that file is 0-sorry again; (4) the discharge suppliers
reshaped into the geo-atlas family (`GeoChart`/`geoAtlas`, `GeoCoverSpec`, `GeoJacobianSpec`/`Fold`);
(5) FOUR new gate-orphans appeared (the fold-Jacobian spine + the cover SPECIFY + FlatCubeLeaf chain).*

## 0. The one-line state

`monomialization_terminates` / `engine_box_threshold_finite` are `+sorryAx` via **EXACTLY**
`chartBridge_buildTree` (`EngineObligations.lean:53`, a bare `sorry`). Discharging it flips the hbox
event the R5 mint re-point waits on. The discharge is via the (D) R-split (§2e): a HIGH
`ChartBridgeFaithful.lean` proves `chartBridgeFaithful_buildTree` (A∧B∧C∧D over `geoAtlas`), and
`chartBridge_buildTree` fills as its projection. **[tick 289 update]** The geo-atlas lane now owes only:
the fold-Jacobian regrouping cocycle (`geoAtlas_fold_det`, GeoLeafJacobian, task #43) and clause (D)
statement + node-walk (task #44). RESOLVED since pass #5: the clause-(A) cover is DONE
(`geoAtlas_imageCover` clean-three, tick 288); the per-pivot emission fix landed (task #35, the
parametric-gauge seam-fix); the fold spine is gate-wired (`13b86217a`, AxCheck:12).

## 1. The endgame module import/consumption graph (current tree)

**Aggregator closure path:** `DLNFibre.lean:741` → `AxCheck.lean`. `AxCheck.lean:1-11` imports (direct,
Engine): CanonicalWitness224, EngineDriver, ClearableReify, NumDivFlatBound, O5Realization, QNodeChart,
GeoChart, DivBirthReach, **PivotInjOn (:9)**, **ChartBridgeWiring (:10)**, **QNodeCarrier (:11)**. Also
`DLNFibre.lean:1474/1479` import Engine.EngineDefs + Engine.PivotCover direct. The green-gate is
`lake build DLNFibre` = this transitive closure ONLY (the `DLNFibre` lib has NO `globs` in
`lakefile.toml` — it builds the root module's imports, so a module imported by nothing ESCAPES the gate;
aggregator warns at `DLNFibre.lean:273-275`).

**Import edges of the Engine modules** (`X → Y` = X imports Y; grep-verified `^import`, HEAD `c342c55fb`):

    CanonicalWitness224 → EngineDefs
    ChartBridgeWiring   → EngineDefs
    ClearableReify      → EngineConstruction
    CoRank2Spike        → EngineDefs
    CenterIndices       → EngineConstruction
    DivBirthReach       → NumDivFlatBound
    EngineConstruction  → EngineDefs
    EngineDefs          → ResolutionTree (+ Validate.RouteMBoxReduction, RouteMLayerSplit)
    EngineDriver        → EngineObligations
    EngineObligations   → EngineDefs, EngineConstruction, O5Realization, RegionGlueAssembly
    FlatCubeLeaf        → PivotLeafClauses
    GeoChart            → QNodeChart, ShearReconcile, QNodeCarrier
    GeoCoverSpec        → GeoChart
    GeoJacobianSpec     → GeoChart (+ Validate.RouteMConjBlock)
    GeoJacobianFold     → GeoJacobianSpec
    NumDivFlatBound     → EngineConstruction
    O5Realization       → ClearableReify, NumDivFlatBound
    PivotCoverFold      → EngineDefs, PivotCover
    PivotInjOn          → PivotCover
    PivotLeafClauses    → EngineDefs, PivotCover
    QNodeCarrier        → QNodeChart, DivBirthReach
    QNodeChart          → CenterIndices
    RegionGlueAssembly  → RegionGluePerLeaf, RegionGlueGlobalize
    RegionGluePerLeaf   → EngineDefs
    ShearReconcile      → PivotCoverFold

### 1a. Gate-orphan sweep (charge #2) — the CURRENT orphans

Pass #4's two orphans are FIXED: `PivotInjOn` + `ChartBridgeWiring` were wired into `AxCheck` at
tick 241 (`063212ecf`, watch lines `AxCheck.lean:1329-1330`).

**⚠ FOLD-SPINE ORPHAN — CLOSED (amend, cartographer-6 follow-up, 2026-07-19).** The fold-Jacobian
spine (`GeoJacobianFold` + `GeoJacobianSpec`) was wired at commit **`13b86217a`** ("axcheck: watch
fidelity capstone + fold-Jacobian spine — import + 5 MUST-clean-three lines; verified LAKE-EXIT:0"),
which landed AFTER this office's worktree snapshot. Current HEAD (`6eb312dbe`, tick 269) has `import
DLNFibre.DLN.RLCT.Engine.GeoJacobianFold` at `AxCheck:12` (pulls GeoJacobianSpec transitively) + watch
lines for `geoChartMap_fderiv_det`/`_offcone`, `abs_det_fderiv_foldr_comp`, `geoChartMap_differentiable`,
`cNodeOf_eq_realCNode_of_conOracle`. **The underlying catch was still real** — journal tick 265 CLAIMED
the wiring before the commit existed (the edit sat uncommitted pending build verification until tick 267;
tick-265 commit `3c5789b59` had an empty AxCheck diffstat). Pattern for the journal: say "edited, commit
pending gate" when that is the truth, not "added".

Remaining orphans (current HEAD `aac2dc391`, tick 289):

| module | reachable from aggregator? | sorry? | disposition |
|---|---|---|---|
| **GeoCoverSpec** | **NO — ORPHAN** | **clean-three** (cover DONE, tick 288) | wire at discharge (via ChartBridgeFaithful → GeoCoverSpec). Its `:8` docstring "with its one `sorry`, t10 fills it" is now doc-rot. |
| **GeoLeafJacobian** | **NO — ORPHAN** | `:35` sorry (`geoAtlas_fold_det` cocycle, task #43) | EXPECTED-WIP; wire at discharge (its sorry then shows +sorryAx until #43 closes) |
| **GeoDiagSwap** | **NO** (only GeoLeafJacobian, itself orphan) | sorry-free | rides in when GeoLeafJacobian is wired |
| **CoRank2Spike** | **NO — ORPHAN** | sorry-free | SUPERSEDED → cordon (see below) |
| **FlatCubeLeaf** | **NO — ORPHAN** | sorry-free | SUPERSEDED → cordon (see below) |
| **PivotLeafClauses** | **NO** (only FlatCubeLeaf, itself orphan) | sorry-free | PARTIAL banked-to-wire (srcBox pair) + partial cordon (see below) |

*(Fold spine `GeoJacobianFold`/`GeoJacobianSpec` was wired at `13b86217a` — AxCheck:12. `FlatSwap` rides
the gate via GeoChart:12→FlatSwap.)*

### 1a-bis. Disposition of the three legacy orphans (charge follow-up — PROPOSE, don't wire)

*Wiring lands with the discharge batch; this is the proposal for the t12-assembly / #15 seat.*

- **CoRank2Spike → SUPERSEDED-to-cordon (join #15).** The rung-2C (3,3,4) coordinate-injectivity
  de-risk spike (`corank2Leaf` + `_divCoord_injective`/`_resCoord_injective`/`_disjoint_coords`/`_fits`).
  Its de-risk is SERVED: the general, proven `leaves_chart_clauses_conRoot` (DivBirthReach) is the real
  thing. NO module imports it — the only tree hit for "corank2" is `Validate/Case334RouteStep.lean`'s
  `pivotWitness4422_corank2` (an UNRELATED (4,4,2,2)-route pivot witness, not this module). Retire unless
  the team wants a concrete (3,3,4) coordinate GUARD kept green (then wire minimally, `rr4-precedent`-style).

- **FlatCubeLeaf → SUPERSEDED-to-cordon (join #15).** The pre-geoAtlas per-leaf machinery.
  `flatCubeLeafData` (the leaf smart-constructor) is called by NOTHING — the real leaf constructor is
  `leafOfState` (EngineConstruction) and the atlas pieces are `geoAtlas`'s `{ lc.1 with chartMap := lc.2 }`
  (GeoChart:100). `flatCubeLeafData_perLeafClause` bundles the 8 clauses for a `flatCubeLeafData` leaf,
  but the discharge assembles the 8 clauses PER geoAtlas PIECE from DivBirthReach (coords) + PivotInjOn
  (a.e.-InjOn) + the fold Jacobian (LeafJacobian) + the srcBox pair below — not via this bundle. geoAtlas
  superseded it.

- **PivotLeafClauses → PARTIAL banked-to-wire.** Consumed today ONLY by the superseded FlatCubeLeaf, but
  it holds ONE load-bearing pair the discharge NEEDS: `flatCubeSrcBox_measurableSet` + `flatCubeSrcBox_bounded`
  (`:35,:41`) prove the two clause-(B) FREE clauses (`MeasurableSet srcBox` + bounded-in-flat-cube) that
  `leaves_chart_clauses_conRoot` does NOT cover — and NO live gate-reachable module proves srcBox
  measurability otherwise (`leaves_srcBox_nonempty` gives nonempty, not measurable). These apply DIRECTLY:
  every geoAtlas piece inherits `leafOfState`'s `srcBox = paramsEquivFlat ⁻¹' cubeBox` (the exact shape
  these helpers target). So at discharge: WIRE PivotLeafClauses (re-home the srcBox pair under the
  discharge's import, replacing FlatCubeLeaf as the consumer). Its OTHER decls are superseded — the coord
  helpers (`coords_disjoint_of_ne`/`coord_clauses`) DUPLICATE DivBirthReach's coordinate clauses; the
  `q`-preimage helpers (`qPreimageSrcBox_measurableSet`/`measurableSet_pivotChartDom`) target the OLD
  `node_pivotCover_of_atom` childRegion shape (superseded by geoAtlas) and are consumed by nothing. Net:
  keep the srcBox pair (banked-to-wire), cordon the rest with FlatCubeLeaf. (If the discharge instead
  re-derives srcBox measurability inline, the whole module joins the cordon — the t12-assembly seat
  decides at discharge which srcBox route it takes.)

## 2. The `chartBridge_buildTree` discharge — WIRING CHECKLIST (the operative deliverable)

The discharge fills `EngineObligations.lean:53`. **[tick 289: via the (D) R-split — see §2e for the
placement mechanics.]** The faithful discharge `chartBridgeFaithful_buildTree` (HIGH module
`ChartBridgeFaithful.lean`) bundles (A)∧(B)∧(C)∧(D) over the `geoAtlas` (`GeoChart.lean:100`);
`chartBridge_buildTree` fills as its (D)-dropping projection. Piece-suppliers and homes:

| discharge input | supplier decl | home (file:line) | in EO closure now? |
|---|---|---|---|
| the bundler | `chartBridge_of_pieces` (+ a faithful sibling for (D)) | ChartBridgeWiring.lean:27 | **NO** |
| the atlas | `geoAtlas` | GeoChart.lean:100 | **NO** |
| (A) image-cover | `geoAtlas_imageCover` (**DONE, clean-three**, tick 288) | GeoCoverSpec.lean:370 | **NO** |
| (B) coord clauses: divCoord/resCoord inj + disjoint (per BUILT leaf) | `leaves_chart_clauses_conRoot` | DivBirthReach.lean:325 | **NO** (reachable via GeoChart→QNodeCarrier→DivBirthReach) |
| (B) a.e.-InjOn | `pivotChart_ae_injOn` (transported to the piece) | PivotInjOn.lean:47 | **NO** |
| (B) `LeafJacobian` `\|det Dβ\|` | `geoAtlas_fold_det` (**sorry**, cocycle #43) — over the banked atoms `geoChartMap_swap_fderiv_det` + `abs_det_fderiv_foldr_comp` | GeoLeafJacobian.lean:31 (atoms: GeoJacobianSpec/Fold, GeoDiagSwap) | **NO** |
| (B) `LeafPullback` | not yet built (loss-factorization; pnp-loss commissioned) | — | — |
| (D) fidelity node-walk | task #44 (statement-gate first) | ChartBridgeFaithful (planned) | **NO** |
| numDiv ≤ flatDim (underpins injective divCoord) | `leaves_numDiv_le_flatDim` | NumDivFlatBound.lean | YES (via O5Realization→NumDivFlatBound) |

### 2a. Import additions — the FAITHFUL module's cone (superseded by §2e for EO's own import)

**[tick 289: with the R-split, EngineObligations imports JUST `Engine.ChartBridgeFaithful` (§2e); the
list below is what that HIGH module imports.]** The proof site is
`chartBridge_buildTree` (`EngineObligations.lean:51-53`), filled by projection. EO's current closure is
{EngineDefs, EngineConstruction, O5Realization, RegionGlueAssembly}. The discharge needs (import into EO,
or into the coverage helper module that EO then imports — same set):

1. `Engine.ChartBridgeWiring` — `chartBridge_of_pieces`.
2. `Engine.GeoChart` — `geoAtlas`; transitively pulls QNodeChart, CenterIndices, ShearReconcile,
   PivotCoverFold, QNodeCarrier, DivBirthReach, NumDivFlatBound.
3. `Engine.GeoCoverSpec` — `geoAtlas_imageCover` (clause A). **[NEW vs pass #4 — pass #4 listed the
   pre-geoAtlas suppliers; the cover is now its own SPECIFY module.]**
4. `Engine.GeoJacobianFold` — `abs_det_fderiv_foldr_comp` + (transitively) `geoChartMap_fderiv_det`,
   for the `LeafJacobian` clause. **[NEW vs pass #4.]** Wiring this ALSO closes the fold-spine
   gate-orphan (§1a).
5. `Engine.DivBirthReach` — `leaves_chart_clauses_conRoot` (transitively reachable via GeoChart, but
   import explicitly for the (B) coord clauses).
6. `Engine.PivotInjOn` — `pivotChart_ae_injOn` (transitively reachable via GeoChart→ShearReconcile→
   PivotCoverFold→PivotCover, but PivotInjOn's `_ae_injOn` transport is the direct supplier).

⚠ **Import-hygiene note (ratified whitelist rule, [[import-hygiene]]).** GeoChart drags the
analysis-heavy ShearReconcile/PivotCover cone (Mathlib FDeriv/Transvection/Determinant) into the
currently-LIGHT EngineObligations. Weight bump expected; the discharge commit owes a controller
docstring note per the rule, OR the discharge is homed in a coverage module (keeping EO light) that
EngineDriver's lane already pays for. Judge at discharge time.

### 2b. AxCheck watch flips — `+sorryAx` → MUST-clean-three (CURRENT line numbers)

When the discharge lands, these `#print axioms` lines change disposition (rewrite the adjacent prose):

- `AxCheck.lean:1305` `Engine.chartBridge_buildTree` — `-- +sorryAx (← T3 coverage lane)` → clean-three.
- `AxCheck.lean:1310` `Engine.monomialization_terminates` — `-- +sorryAx via EXACTLY chartBridge_buildTree` → clean-three.
- `AxCheck.lean:1302` `Engine.engine_box_threshold_finite` — prose `:1299-1301` ("this line flipping to clean-three IS the hbox event the mint re-point waits on") → clean-three.
- `AxCheck.lean:1298` `Engine.region_glue` — prose `:1294-1297` (`+sorryAx` THROUGH THE TYPE via `resolutionOf`'s `.choose`, which carries the two named holes) → clean-three.
- **DOES NOT FLIP:** `AxCheck.lean:1288` `Engine.canonicalResolution224` — this EXPECTS `+sorryAx` via
  its OWN separate sorry (`CanonicalWitness224.lean:135`, an inline `by sorry` for the (2,2,4)
  ChartBridge conjunct), which does NOT share `chartBridge_buildTree`. RESOLVED (pass #4 left this a
  VERIFY): it is a SEPARATE concrete-witness sorry; it closes as the (2,2,4) cover corollary (the "P8
  tide"), NEVER auto-flips with the generic discharge (journal tick 261 confirms).

Regression guards that MUST STAY clean-three (unchanged by the discharge), CURRENT line numbers:
`region_glue_of_chartBridge` (`:1293`), `o5_realization` (`:1309` — now clean-three, was +sorryAx via
o5_core), `isFullMonomialization_buildTree_conRoot` (`:1313`), `minAdm_le_terminalExponents` (`:1314`),
`leaves_numDiv_le_flatDim` (`:1317`), `qOfCenter` (`:1320`), `DivBirthInv_conOracle_stepChildren`
(`:1323`), `leaves_chart_clauses_conRoot` (`:1326`), `pivotChart_ae_injOn`/`chartBridge_of_pieces`
(`:1329-1330`), `qNodeOf`/`dCenterOfNode_edgeSum` (`:1333-1334`), `qOfCenter_hasFDerivAt` (`:1337`),
`clearable_of_minimizer`/`clearable_tStar` (`:1340-1341`), `tStar_realized`/`o5_core_realized`
(`:1344-1345`). EXPECTS `+sorryAx` until R7: `realizedProfiles_eq_clearableAdm` (`:1350`).

### 2c. The clause (D) gate (task #10) — HONEST STATE (still un-landed)

- (D) is **NOT** in the `ChartBridge` def body. `EngineDefs.lean:96-109` is only conjuncts (A)∧(B)∧(C).
- (D) exists as **prose only** — `EngineDefs.lean:86-95` ("HONEST FORM (the (D)-less window)… GATE
  (cordon-checked): (D) must be IN this type BEFORE `chartBridge_buildTree`'s discharge lands").
- `chartBridge_of_pieces` (`ChartBridgeWiring.lean:27-41`) bundles only A/B/C: `⟨atlas, himg, hleaf,
  hexp⟩` — there is NO (D) argument pre-staged. **Task #10 is genuinely OPEN** (un-landed content, not
  pre-staged code).
- **⚠ dCenterOfEdge-GATED (D) obligation (journal tick 262, coverage's rollover counter-sign — MUST be
  in the t12-assembly brief).** (D)'s "intended chart at edge `e`" must be **`dCenterOfEdge`-GATED**:
  identity at `dCenterOfEdge = 0` (rollover OR a degenerate 0-factor case12/case2 — e.g. `resCols = 0`),
  a pivot-fan at `dCenterOfEdge ≥ 1`. (D) must **NOT** assert that every case12/case2 edge blows up a
  real pivot (`resCols = 0` falsifies that). The three-way consistency (geoChartMap's `dite`, the
  id-passthrough at a chartless edge, and the intended chart all agree at a 0-count blow-up) is the
  fidelity ground; it rests on `dCenterOfEdge` counting correctly (the already-closed elder defect
  chain — no new assumption). Coverage builds its nodes-walk + (D) statement to the gated form.
- When (D) lands (additive, def-only touch; `region_glue` + the `CanonicalResolution` projection are
  agnostic — `EngineDefs.lean:94`):
  (i) add the 4th conjunct to `ChartBridge` (`EngineDefs.lean:~109`) — the `geometricLeafPaths` fidelity
      (each piece's `chartMap` = the real `β∘ψ` geometric fold of a `t`-path, `dCenterOfEdge`-gated);
  (ii) add the 4th arg `hfid` to `chartBridge_of_pieces` + `⟨atlas, himg, hleaf, hexp, hfid⟩`
      (`ChartBridgeWiring.lean:27-41`);
  (iii) the discharge must supply `hfid`;
  (iv) **`region_glue_of_chartBridge`'s destructure gains a slot.** `RegionGlueAssembly.lean:107`
      currently destructures `⟨atlas, ⟨U, hUopen, hUlocus, hUcover⟩, hleaf, hexp⟩` (the 0∈U cover
      shape — already LANDED, see §2d). When (D) is added as a 5th `∃`-conjunct this becomes
      `⟨atlas, ⟨…⟩, hleaf, hexp, _hfid⟩` (region_glue does NOT consume (D), so `_`-ignore it). This is
      the "destructure arity edit" the assembly seat must not miss.

### 2d. The 0∈U cover reshape — LANDED (charge: the reshape pass #4 predates)

Clause (A) is now the OPEN-NEIGHBOURHOOD-of-the-zero-locus form, consistent across the type, the
bundler, the cover SPECIFY, and the consumer:
- `EngineDefs.lean:98-100` (in `ChartBridge`): `∃ U, IsOpen U ∧ {A ∈ paramsBoxM M 1 | frobSq(prod M
  A)=0} ⊆ U ∧ U ⊆ ⋃ c ∈ atlas, c.chartMap '' c.srcBox`.
- `GeoCoverSpec.lean:33-37` (`geoAtlas_imageCover`, the SPECIFY, `sorry` t10) — same shape, plus
  `htree : t = buildTree M (conOracle M) s` (pins the conOracle relatives).
- `RegionGlueAssembly.lean:107` destructures it; `:34` `exists_small_paramsBox_subset_open` consumes
  `0 ∈ U` (extracted at `:111-115` via `h0locus`: `0` is in the zero-locus since `prod M 0 = 0` for
  `L ≥ 1`). `region_glue_of_chartBridge` is PROVEN clean-three consuming this shape.
So the 0∈U reshape is fully wired on the assembly side — no pending edit there EXCEPT the additive (D)
slot (§2c(iv)).

### 2e. ASSEMBLY PLACEMENT VERDICT (elder charge-4) — the (D) R-split mechanics

*Verified on disk at HEAD `aac2dc391` (tick 289: charge-4 R-split adopted, projection-enforcement).
The (D) R-split: a HIGH module `ChartBridgeFaithful.lean` (NOT yet created) carries the faithful
discharge; `chartBridge_buildTree` (`EngineObligations:53`) fills as its PROJECTION.*

**VERDICT: CLEAN IMPORT-ADD — NO CYCLE. No statements/discharge split is FORCED by the module graph.**
`EngineObligations` can directly gain `import Engine.ChartBridgeFaithful` (which transitively pulls
GeoChart / GeoCoverSpec / GeoLeafJacobian / ChartBridgeWiring).

**Cycle proof (grep-verified, whole tree):**
- GeoChart's transitive cone = {QNodeChart, ShearReconcile, QNodeCarrier, FlatSwap, CenterIndices,
  EngineConstruction, EngineDefs, ResolutionTree, PivotCoverFold, PivotCover, DivBirthReach,
  NumDivFlatBound}. It BOTTOMS OUT at EngineConstruction / EngineDefs / ResolutionTree — all modules
  `EngineObligations` ALREADY sits above (it imports EngineDefs + EngineConstruction).
- GeoLeafJacobian's extra cone = {GeoDiagSwap, FlatSwap, GeoJacobianFold, GeoJacobianSpec} + GeoChart's.
  GeoCoverSpec's = GeoChart's. None reach EngineObligations.
- Consumers of the "downstream" modules: `EngineObligations` ← ONLY `EngineDriver`; `EngineDriver` ←
  ONLY `AxCheck`; `CanonicalWitness224` ← ONLY `AxCheck`; `CoRank2Spike` ← nothing. All consumers
  (EngineDriver, AxCheck) sit strictly ABOVE the whole Engine cone.
- NO module in the GeoChart / GeoCoverSpec / GeoLeafJacobian cone imports EngineObligations,
  EngineDriver, O5Realization, or RegionGlueAssembly (grep-confirmed empty).
- So the new edge `EngineObligations → ChartBridgeFaithful → GeoChart → … → EngineConstruction` is a
  DAG (a diamond over EngineConstruction), not a cycle.

**Why the R-split is still right (it is FIDELITY-forced, not cycle-forced).** The elder's "forced high
regardless" holds: the discharge inherently needs `geoAtlas` (GeoChart, analysis-heavy), so
`EngineObligations` — and via `EngineDriver`/`AxCheck` the payoff chain — INHERITS the GeoChart cone
whichever module discharges. That is an import-WEIGHT cost (owed a controller docstring note per
[[import-hygiene]]), not a cycle. The R-split's purpose is PROJECTION-ENFORCEMENT of clause (D): the
faithful theorem is proven once, high; the low obligation cannot silently skip (D).

**Decl-level placement (the discharge batch builds this):**
- NEW HIGH module `ChartBridgeFaithful.lean` — imports GeoChart, GeoCoverSpec, GeoLeafJacobian,
  ChartBridgeWiring:
  - `def ChartBridgeFaithful M t` = (A)∧(B)∧(C)∧(D). The (D) conjunct references
    `geometricLeafPaths`/`geoChartMap` (GeoChart) so the DEF is HIGH (cannot live in EngineDefs).
  - `theorem chartBridgeFaithful_buildTree M hL hMpos : ChartBridgeFaithful M (buildTree … conRoot)`
    — the faithful discharge, feeding (A) `geoAtlas_imageCover` (GeoCoverSpec, DONE) + (B) coords
    `leaves_chart_clauses_conRoot` (DivBirthReach) + a.e.-InjOn `pivotChart_ae_injOn` (PivotInjOn) +
    LeafJacobian `geoAtlas_fold_det` (GeoLeafJacobian, cocycle sorry #43) + LeafPullback (owed) + the
    (D) node-walk (task #44) into a faithful bundler.
  - `theorem ChartBridgeFaithful.toChartBridge {t} : ChartBridgeFaithful M t → ChartBridge M t` — the
    PROJECTION (drop (D)).
- `EngineObligations` (unchanged position, gains one import): `import Engine.ChartBridgeFaithful`; then
  `chartBridge_buildTree M hL := (chartBridgeFaithful_buildTree M hL hMpos).toChartBridge`.
  **SIGNATURE NOTE:** the faithful discharge needs `hMpos : ∀ i, 0 < M i` (same as o5_realization /
  the cover). So `chartBridge_buildTree` must GAIN `hMpos`, and its call site
  `monomialization_terminates` (`EngineObligations:98`, `chartBridge_buildTree M hL`) threads it
  (`hMpos` is in scope there, `:92`). This is the same signature-widening the o5 arc did.

**Final import-adds into `EngineObligations`:** just `Engine.ChartBridgeFaithful` (it pulls GeoChart /
GeoCoverSpec / GeoLeafJacobian / ChartBridgeWiring transitively). This ALSO closes the current orphans
GeoCoverSpec + GeoLeafJacobian + GeoDiagSwap (they enter the gate via EngineDriver → EngineObligations →
ChartBridgeFaithful). PivotLeafClauses's srcBox pair (§1a-bis) rides in if the faithful bundler consumes it.

**AxCheck watch flips (CURRENT line numbers, HEAD aac2dc391):**
- `chartBridge_buildTree` (`:1306`) → clean-three (was `+sorryAx (← T3 coverage lane)`).
- `monomialization_terminates` (`:1311`) → clean-three (`+sorryAx via EXACTLY chartBridge_buildTree`).
- `region_glue` (`:1298`) + `engine_box_threshold_finite` (`:1302`) → clean-three.
- **NEW watch line:** `#print axioms Engine.chartBridgeFaithful_buildTree` → MUST-clean-three (the REAL
  discharge; a sorryAx here = the hole reopened at the faithful level). Also watch
  `geoAtlas_fold_det` (GeoLeafJacobian) — currently an orphan sorry; it enters the gate at discharge and
  must be clean-three by then (task #43).
- `canonicalResolution224` (`:1288`) still does NOT flip (separate (2,2,4) sorry).

**Projection-form cordon note (LOAD-BEARING — put in the t12-assembly brief):** `chartBridge_buildTree`
MUST be filled via the `.toChartBridge` PROJECTION of `chartBridgeFaithful_buildTree`. A direct
`chartBridge_of_pieces ⟨geoAtlas, himg, hleaf, hexp⟩` fill that assembles only (A)∧(B)∧(C) is a
**FIDELITY REGRESSION** — it closes the hole WITHOUT ever proving (D), exactly the gate at
`EngineDefs:92-93` ("a proven discharge against a (D)-less type closes the hole with the `t`'s-cover tie
missing"). The cordon: the low fill's proof term must reference `chartBridgeFaithful_buildTree`.

**R5 #guard_msgs extension:** R5 installs the ENFORCED axiom-gate (a `#guard_msgs` on the headline's
`#print axioms`, replacing the confirmed-by-discipline `#print` diagnostic — [[banked-families]] R5
seat B). Extend it to `chartBridgeFaithful_buildTree` so its clean-three is BUILD-ENFORCED (a silent
reopen at the faithful level fails the build, not just the eyeball).

## 3. Dead/stale reference sweep — CURRENT drift (diff-then-judge)

| struck design | LIVE Lean hits (current) | correction owed |
|---|---|---|
| chartBridge_buildTree docstring = STRUCK placeholder-carrier plan | — (no placeholder text on disk) | **RESOLVED (carto, tick 348).** The "PLACEHOLDER charts / localSub = id / leafOfState.chartMap = id / path-accumulator" docstring is GONE — replaced by the R-split projection docstring (tick 289) and refreshed carto tick-348 (`EngineObligations.lean:37-52`: `chartBridge_buildTree := (chartBridgeFaithful_buildTree …).toChartBridge`, frontier = the `LeafPullback` conjunct). grep-verified: no placeholder/`localSub = id` string remains. |
| single-per-node ψ "is the right model" | `ShearReconcile.lean:30-35` (provenance docstring) | **RESOLVED (carto, tick 348; nav-6 "ALREADY fixed").** Not an unmanaged self-contradiction: the module's RETIRE NOTE (`:13-21`) GOVERNS the provenance docstring — `:21` reads "The docstring below is kept for provenance; read it through this note." Retained-provenance-under-a-governing-note; no owner action owed. (pnp-psi T2; R-b adopted; `_sheared` used only at `ψ=.refl`, `:59`.) |
| pass-#4 §3 sweep: "qNodeOf (node-keyed) STRUCK → rename to qOfCenter/qEdgeOf" | — | **CONTRADICTED by the current tree** (see [[naming]]): `qNodeOf` is LIVE and node-keyed (`QNodeCarrier.lean:505`), the form GeoChart's `geoAtlas`/fold CONSUME. The pass-#4 dead-route entry for qNodeOf is itself now stale — superseded here. |
| GeoJacobianSpec `∀ t` fold-det SPECIFY (finding 1) | RETIRED from the tree (the top-level SPECIFY sorry `GeoJacobianSpec:37` is GONE — deferred at tick 260) | recorded as a trap in [[dead-routes]] (geo-atlas emission-defect family). |

**ERRATUM (carto, tick 348).** Journal tick-338 wrote the faithful discharge's remaining sorry as
`ChartBridgeFaithful:82`; the disk sorry is `ChartBridgeFaithful.lean:92` (the `LeafPullback`
conjunct). `:82` is `theorem chartBridgeFaithful_buildTree`'s signature line; the sorry sits in its
proof body at `:92`. (Recorded by nav-6, tick 348; grep-verified.)

## 4. Predecessor-card corrections (diff-then-judge)

- **pass #4 §0 "one hole, one lane"** was accurate at tick 238 (chartBridge_buildTree) and STAYS
  accurate — but o5_realization is now clean-three (was flagged there as "went clean-three at tick
  218"; now the AxCheck line `:1309` reads clean-three with `o5_core_realized` landed). Consistent.
- **pass #4 §2b's line numbers** (1285/1295/1299/1302/1307) are STALE by ~3-8 lines after the tick-265
  spine watch-block additions; §2b above carries the current numbers (1288/1298/1302/1305/1310).
- **pass #4 §1 orphan table** (PivotInjOn/ChartBridgeWiring = ORPHAN) is SUPERSEDED — both wired at
  tick 241; the current orphans are the six in §1a.
- **[[banked-families]] D-ARC (a) "EngineConstruction = 1 sorry (o5_core :2611)"** is STALE:
  `o5_core` is DELETED (move-at-landing done, tick 189 ruling #3 executed); `EngineConstruction` is
  0-sorry. Corrected in [[banked-families]] this pass.
