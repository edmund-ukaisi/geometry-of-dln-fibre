# Overlay — naming forwarding-pointers (cartographer, curated layer)

*Every rename leaves a pointer here so old references stay resolvable. Created pass #1; **REFRESHED
pass #2 (2026-07-18)**: the council-adopted restructure has LANDED (tick 37 r2-validate), so pass-#1's
"Pending (unlanded)" block moved to Landed; added the new-this-expedition modules + the namespace
quirk + two pin moves.*

## Landed since pass #1 (was "Pending", now in the root tree)

- **Edge-labelled carrier — LANDED (tick 37, r2-VALIDATED).** `Edge {case, subst, child}` +
  `branch (n) (edges : List (Edge M))`; `StepData` carries no `case`; leaf `chartMap` = derived
  path-fold. `Engine/ResolutionTree.lean`. The unary `StepInvariant` is GONE from root
  (pass #1 flagged it still present — resolved).

- **`ChartsCover` → `ChartBridge` — LANDED + STRENGTHENED (tick 46).** Per-leaf CoV bridge (chartMap +
  MeasurableSet-bounded `srcBox` + resRank + LeafPullback + LeafJacobian + a.e.-InjOn + image cover).
  In `Engine/EngineObligations.lean`. Interface FROZEN + abstract-field-gate-cleared (tick 51).

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

## Watch (rename risk on landing)

- The full-`T` chooser (R1 open) + `genDivExp` redesign (R4) will re-shape `LeafData`/`StepData`
  ledger fields. The obligation projection names (`case_step_invariant`, `reduction_layer`,
  `coverage_theorem`, `exponent_ledger_bridge`, `resolutionOf`/`resolutionOf_spec`) are stable
  anchors; their statements are not. Re-verify at the next pass.
