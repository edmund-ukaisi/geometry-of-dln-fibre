# Cover SPECIFY — clause (A) over the geometric atlas (for t10)

*Author: `coverage-t08`. The SPECIFY handoff for the cover builder (t10). q-det-INDEPENDENT (the cover
reads pure `β` via `reparam_image`; the Jacobian/det is t11's fold-module). Everything the atlas needs is
banked: `GeoChart`/`geoChartMap`/`geometricLeafPaths`/`geoAtlas` (`Engine/GeoChart.lean`, green,
instantiated against t09's carrier), the R-b atoms (`ShearReconcile`), the per-node cover atom
(`PivotCoverFold`), and t09's lemmas. Statement + structure below; t10 fills the sorries + builds `tGeo`.*

## Goal (the theorem)

Clause (A) of the corrected `ChartBridge`, over the geometric atlas:

    theorem geoAtlas_imageCover (t : ResolutionTree M) (h : <t is a built tree / reachability witness>) :
      ∃ U : Set (Params M), IsOpen U ∧
        {A : Params M | A ∈ paramsBoxM M 1 ∧ frobSq (prod M A) = 0} ⊆ U ∧
        U ⊆ ⋃ c ∈ geoAtlas t, c.chartMap '' c.srcBox

`geoAtlas t = (geometricLeafPaths (dCenterOfNode M) (qNodeOf M) id t).map (fun lc => {lc.1 with chartMap := lc.2})`
(`GeoChart.lean`). The `h` witness is whatever pins the tree to `buildTree M (conOracle M) s` so t09's
`dCenterOfNode_edgeSum`/`dCenterOfNode_le_flatDim` (conOracle-relative) apply at each node — mirror how
`chartBridge_buildTree` will invoke it (`t = buildTree …`).

## STRUCTURAL DECISION (decided): build `tGeo`, reuse the banked tree-fold — NOT a List fold

**Recommendation: build the geometric fan-out TREE `tGeo` and reuse `chartBridge_imageCover_of_ownCovers`;
do NOT re-prove the cover over the `geometricLeafPaths` List.** Why: the banked cover machinery
(`PivotCoverFold`) is entirely tree-shaped — `node_pivotCover_of_atom` (per-node atom), `ownCovers_branch`
(the inductive fold), `chartBridge_imageCover_of_ownCovers` (the headline → `⋃ l ∈ leaves t, chartMap '' srcBox`).
A `tGeo` whose nodes' edges ARE the `d_center` pivot family plugs into all three verbatim; a List route
re-derives the fold from scratch. The one-time cost of `tGeo` (a structural recursion, below) is far less
than re-proving `ownCovers`/the headline over a List.

`tGeo` (bake the composite into leaves, `geoChartMap` onto edges) — the geometric refinement of `t`:

    tGeo (acc) : ResolutionTree M → ResolutionTree M
      | .leaf l      => .leaf { l with chartMap := acc }
      | .branch n es => .branch n (fannedEdges acc n 0 es)
    fannedEdges (acc) (n) (offset) : List (Edge M) → List (Edge M)
      | [] => []
      | .mk c s ch :: es =>
          ((List.finRange (dCenterOfEdge n (Edge.mk c s ch))).map fun p =>
             Edge.mk c { s with localSub := geoChartMap (dCenterOfNode M) (qNodeOf M)
                                   ⟨n, Edge.mk c s ch, offset + (p:ℕ)⟩ } (tGeo acc ch))
            ++ fannedEdges acc n (offset + dCenterOfEdge n (Edge.mk c s ch)) es

(Structural recursion needs the `Edge.mk` destructure — same pattern as `geometricLeafPaths`; the child
`tGeo acc ch` is recursed with the SAME `acc` and each edge's localSub bakes `geoChartMap`, so the leaf's
baked `chartMap` = the fold of the edge localSubs = the `leafPaths` composite → coherence holds.)

`leaves (tGeo id t)` = `geoAtlas t` up to the `chartMap` materialization — either **redefine**
`geoAtlas t := leaves (tGeo id t)` (cleanest; supersedes the `geometricLeafPaths`-based def) OR prove
`geometricLeafPaths id t = leafPaths id (tGeo id t)` and keep both. RECOMMEND the redefine.

## srcBox handling (decided): flat-cube `srcBox`, a superset of the pivot domains

Keep each atlas piece's `srcBox = leafOfState.srcBox` (the flat cube `paramsEquivFlat ⁻¹' cubeBox R`,
already what `geoAtlas` carries via `{lc.1 with …}`). It is a SUPERSET of the per-edge `childRegion`s
(`q ⁻¹' (pivotChartDom (pivotOf e) R ×ˢ univ)` — the max-modulus sub-cube), so:
- clause (A)'s `⋃ chartMap '' srcBox ⊇ ⋃ chartMap '' childRegion ⊇` (the fold's cover) — the superset
  direction is free (`Set.image_mono`);
- `ownCovers_branch`'s `hchild : childRegion ⊆ leafPathImages child` holds because a leaf's
  `leafPathImages = srcBox` = flat cube ⊇ `pivotChartDom`;
- the `srcBox` MeasurableSet + bounded clauses are the banked `FlatCubeLeaf`/`PivotLeafClauses` ones.
So NO folded-domain `srcBox` is needed; the flat cube carries everything.

## The exact pins (all banked / t09)

At each `tGeo` node, `node_pivotCover_of_atom` (`PivotCoverFold.lean:187`) discharges the node cover with:
- `q := qNodeOf M n` (the per-node center split; `d := dCenterOfNode M n`).
- `pivotOf e := ⟨the edge's global offset index, _⟩ : Fin (dCenterOfNode M n)` (the `fannedEdges` offset).
- `hbij` = **`dCenterOfNode_edgeSum`** (t09): `Σ_e dCenterOfEdge = dCenterOfNode` ⟹ the offsets tile
  `Fin (dCenterOfNode n)` (every `i` is hit by exactly one fanned edge).
- `hd` = **`dCenterOfNode_le_flatDim`** (t09) — supplies `qNodeOf`'s totality argument on-cone.
- `hloc` = **`geoChartMap`-is-the-conjugated-pivotChart** — by `geoChartMap`'s def (on-cone, via the two
  `dite`s discharged by `hd`/the pivot bound), `localSub e w = (qNodeOf M n).symm (Prod.map (pivotChart …) id ((qNodeOf M n) w))`. This is the fannedEdge's localSub by construction.
- `hdom` = `childRegion e := q ⁻¹' (pivotChartDom (pivotOf e) R ×ˢ univ)` — the srcBox superset above bridges it.
- `hV` = the node's zero-locus piece ⊆ the open center-slab (the `0 < R` open cube preimage).
Fold up with `ownCovers_branch`; convert to clause (A) with `chartBridge_imageCover_of_ownCovers` (needs
the coherence `∀ p ∈ leafPaths id (tGeo id t), p.1.chartMap = p.2`, which `tGeo`'s baked leaves give).

R-b note: the cover reads pure `β` (`geoChartMap` is currently pure `β` — the source gauge `α` is composed
in at the LeafPullback stage and does NOT move the image; `reparam_image` (`ShearReconcile`) is the lemma
if/when `α` is folded in, but the cover itself needs only the pure atom).

## Owed sub-steps for t10 (the PROVE grind)

1. `tGeo` + `fannedEdges` (structural recursion, Edge.mk destructure) + `geoAtlas = leaves (tGeo id t)`.
2. The coherence `∀ p ∈ leafPaths id (tGeo id t), p.1.chartMap = p.2` (baked-leaf + edge-localSub fold —
   the accumulator argument, mirror `imgAcc`/`leafPaths_mapFst` in `PivotCoverFold`).
3. The per-node cover: `node_pivotCover_of_atom` with the pins above (the `hbij` from `dCenterOfNode_edgeSum`
   is the one non-mechanical link — the offset→`Fin (dCenterOfNode)` bijection).
4. The fold: `ownCovers_branch` up `tGeo`; `hV` at the root = the zero-locus-in-unit-box.
5. `chartBridge_imageCover_of_ownCovers` → clause (A) over `geoAtlas`.
6. `hV`/`R` bookkeeping (the open center-slab; `0 < R`); the `h`-witness threading (tree = buildTree) for
   t09's conOracle-relative lemmas.

## Interface to the other lanes (clean seams)

- clause (B) 3 Props: separate (t11's LeafJacobian fold-module + the a.e.-InjOn/LeafPullback); the cover
  does NOT touch them.
- clause (C) exponent-agreement: separate (each piece's ledger `divExp` ∈ terminalExponents t — from the
  shared ledger-leaf data).
- The final `chartBridge_of_pieces` bundles (A)+(B)+(C)[+(D)] — the convergence point; the cover delivers (A).

## Addendum (2026-07-19, architect-t10 at the fill) — TWO corrections to the pins above

Building clause (A) surfaced two truth-signal corrections (both accepted by the controller); the pins
above are superseded where they conflict:

1. **Clause (A) is `0 ∈ U`, NOT `V ⊆ U`** (over-strong-statement class; compass counsel #7). The
   pinned childRegion `q ⁻¹' (pivotChartDom × Set.univ)` cannot sit inside the flat-cube leaf `srcBox`
   (unbounded spectator factor), and more fundamentally the atlas chart images equal the radius-1 flat
   cube while the zero-locus `V = {A ∈ box 1 ∧ frobSq(prod)=0}` TOUCHES that cube's boundary for `L ≥ 2`
   (kill-witness `M=(1,1,1)`, `(A₀,A₁)=(1,0)`: `prod = A₁·A₀ = 0`, `A₀ = 1 ∈ ∂`), so no open `U ⊇ V`
   fits. The consumer (`region_glue`, `RegionGlueAssembly:115`) uses ONLY `0 ∈ U` (an ε-box at the
   origin + `routeMLayerBoxIntegral_lt_top_of_small_box`'s scale-homogeneity — the singularity is local
   at the origin). So clause (A) was weakened to `(0 : Params M) ∈ U` in `EngineDefs.ChartBridge`,
   `ChartBridgeWiring`, `GeoCoverSpec`, `RegionGlueAssembly`. This also dissolves the spectator issue:
   the cover is the R=1 self-cover (`⋃ᵢ pivotChart i '' cubeBox d 1 = cubeBox d 1`, since
   `pivotChartDom i 1 = cubeBox d 1`) — no `pivotChartDom×univ`, no `node_pivotCover_of_atom` (its
   `×ˢ univ` is exactly why), no `ownCovers_branch`; instead `flatCube 1 ⊆ leafPathImages (tGeo id t)`
   by reachability induction. `node_pivotCover_of_atom` is banked-but-retired from the cover path.

2. **`tGeo`/`geometricLeafPaths` must PASS a chartless (rollover) edge through as ONE identity edge.**
   `dCenterOfEdge rollover = 0` ⟹ the `finRange 0 = []` fan-out DROPS the rollover child subtree; since
   layer transitions (S→S+1) are rollovers on the main path, this makes `leafPathImages = ∅` at every
   rollover and cascades the cover failure. Fixed in `tGeo.fannedEdges`: `if dCenterOfEdge n e = 0 then
   [Edge.mk c {s with localSub := id} (tGeo acc ch)] else <pivots>` — the faithful chartless geometry
   (rollover = `id` relabel). This grows `geoAtlas` (now includes rollover children — a correction; the
   old `geometricLeafPaths` silently dropped them).

STATUS at addendum: clause (A) fully WIRED green modulo two tracked `sorry`s in `GeoCoverSpec` — the
`fannedEdges_covers` membership-selection (pure Lean whnf/isDefEq friction on the sealed
`qOfCenter`/`centerPerm` machinery; math proven, Codex-consulted) and the `dCenterOfNode = 0` rollover
sub-case of the induction. Owed at green: the full-batch `AxCheck` gate (`region_glue_of_chartBridge`
clean-three re-probe).
