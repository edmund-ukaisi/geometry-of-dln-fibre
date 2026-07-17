# Overlay — naming forwarding-pointers (cartographer, curated layer)

*Every rename leaves a pointer here so old references stay resolvable. Created pass #1. "Pending" = the
new name is adopted in the plan but NOT yet in the root Lean tree (restructure in flight, task #42).*

## Pending (adopted, unlanded in root)

- **`canonicalResolution_224` → SPLIT into two names** (precision ruling, tick 24; witness split in
  `necessity-and-encodings.md §Witness split`).
  - `canonicalResolution224_arithmetic` — the clean-three BANK piece: the FOUR carrier-independent
    conjuncts (IsFullMonomialization + StepInvariant-on-nodes + branch-rooted + exponent-hooks) at
    (2,2,4). Survives the restructure (its conjuncts don't touch edge/chart data). **This name inherits
    the AxCheck clean-three entry** currently on `canonicalResolution_224` (`AxCheck.lean:1274`).
  - `canonicalResolution224` (full) — a `@[blueprint]` FORECAST: the arithmetic four ∧ the ChartBridge
    conjunct, the latter's `LeafPullback`/`LeafJacobian` SORRIED pending the P8 lemma. Gets its own
    `expects-sorryAx` AxCheck entry; must NOT be in the clean-three list.
  - CURRENT root state: `canonicalResolution_224` (`Engine/CanonicalWitness224.lean:82`) is a single
    sorry-free theorem proving all 5 conjuncts on the TRIVIAL (univ-atlas) coverage — its ChartsCover
    conjunct rode the vacuity, so its de-risk was the arithmetic conjuncts only (honestly noted in the
    module docstring). Task #39 (`pending`) rebuilds it with real charts under the split.

- **`ChartsCover` → `ChartBridge`** (bridge cert, tick 18; edge restructure, tick 23). The abstract
  neighbourhood-cover predicate (`EngineObligations.lean:47`) becomes a per-leaf CoV bridge (chartMap +
  srcBox + resRank + LeafPullback + LeafJacobian + InjOn + image cover). Root still has `ChartsCover`;
  `ChartBridge` unlanded. See [[dead-routes]] (region_glue vacuity).

- **`StepInvariant` → `StepRel`** (council #2, tick 23). The unary per-node invariant
  (`EngineObligations.lean:63`) becomes a RELATIONAL invariant over edges (`State/StateInvariant`
  split). Root still has unary `StepInvariant`; `StepRel` unlanded. See [[dead-routes]] (unary-StepInvariant).

- **`StepData.case` (field) → `Edge.case` (edge label).** Under the adopted edge-labelled carrier the
  case tag moves from a node field to the incoming edge (`Edge {case, subst, child}`); the leaf's
  incoming case lives on its edge (no `LeafData.case`). `LeafData.chartDom` is REMOVED (leaf `chartMap`
  becomes a derived path-composite fold). Root still has `StepData.case` + `LeafData.chartDom`; the
  `Edge` structure is unlanded (task #42).

## Landed / stable (no forwarding needed, recorded for reference)

- **`RR4.lean` = `RouteMBoxThresholdRR4.lean`.** The compass/map write "RR4.lean:12–21"; the actual
  file is `Validate/RouteMBoxThresholdRR4.lean` (there is no bare `RR4.lean`). Line 12–21 is the
  "Why only (r,r,4)" scope note. Main assembly decl: `routeMBoxThresholdFinite_rr4_of_schurRecStep`.

- **`aoyagi_learning_coefficient` (mint anchor).** The bare name is at `Skeleton.lean:1685` (legacy
  stub re-pointing at mint); the hbox-conditional form used by the engine is
  `aoyagi_learning_coefficient_gen` (`HeadlineGenAssembly.lean:55`). `claims.yaml` `lean:` points at
  the bare name but `evidence:` at the `_gen` file — see [[landmark-cards]] mint card (anchor drift flag).

## Watch (rename risk on landing)

- When task #42 lands the edge carrier, the six obligation projections in `EngineObligations.lean`
  (`case_step_invariant`, `reduction_layer`, `coverage_theorem`, `exponent_ledger_bridge`, +
  `resolutionOf`/`resolutionOf_spec`) may change signature (edge-shaped `nodes`/`leaves` read-offs).
  Their `lean:` anchors in `claims.yaml` are the node names, which are stable; the Lean statements are
  not. Re-verify anchors at the next pass.
