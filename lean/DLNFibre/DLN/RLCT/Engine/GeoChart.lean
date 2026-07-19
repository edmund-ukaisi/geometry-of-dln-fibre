import DLNFibre.DLN.RLCT.Engine.QNodeChart
import DLNFibre.DLN.RLCT.Engine.ShearReconcile
import DLNFibre.DLN.RLCT.Engine.QNodeCarrier
import DLNFibre.DLN.RLCT.Engine.FlatSwap

/-!
# `DLNFibre.DLN.RLCT.Engine.GeoChart` — the geometric fan-out atlas (coverage tide, post-gate9)

The flat virtual-leaf atlas realized under elder-gate9's two binding amendments:
* **Amendment 1 (per-edge emission).** The pivot family PARTITIONS across a node's edges; each edge `e`
  emits `dCenterOfEdge node e` charts (case-1(1)=1 `u`-pivot, case-1(2)=`runLen·resCols` d-family,
  case-2=`resRows·resCols`, rollover=0). `geometricLeafPaths` is EDGE-DRIVEN.
* **Amendment 2 (buck-stops).** A `GeoChart` carries only node-derived DATA (`node`, `edge`, `pivot`);
  its geometry `geoChartMap` is COMPUTED from that data + the banked atoms (`qEdgeOf` from the carrier,
  `pivotChart` from `PivotCover`, the source gauge from `ShearReconcile`) — never a free field, so a
  fabricated atlas cannot satisfy the fidelity clause. The fold is a function of `t` alone.

This file (staged coverage-lane module; wired into the aggregator when the discharge consumes it) builds
the atlas bottom-up: `GeoChart` + `geoChartMap` (this piece) → `geometricLeafPaths` → the `LeafData`
atlas → the cover / 3 Props / clauses into `ChartBridge`.
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT

variable {L : ℕ} {M : Fin (L + 1) → ℕ}

/-- **A geometric chart piece** (buck-stops recipe): node-derived DATA only — the parent blow-up `node`,
the `edge` (emission bookkeeping: which ledger edge fanned this chart, for the partition/hbij), and the
GLOBAL `pivot` index into the node's full center (`< dCenterOfNode node`). The chart `geoChartMap` is
COMPUTED from these + the carrier's `qNodeOf`; no stored free geometry. -/
structure GeoChart (M : Fin (L + 1) → ℕ) where
  /-- The parent blow-up node (keys `qNodeOf`). -/
  node : StepData M
  /-- The ledger edge that fanned this chart (emission bookkeeping / partition). -/
  edge : Edge M
  /-- The GLOBAL pivot index into the node's full center (`< dCenterOfNode node`). -/
  pivot : ℕ

/-- **The qNodeOf family** (assumed carrier signature, per-node cover ruling): a per-NODE center-split
`Homeomorph` of dimension `dCN node` (the full node center `d_center`), on the reachable cone
(`dCN node ≤ flatDim M`). Coverage consumes it; the carrier (`qOfCenter` + the concatenated selector)
supplies it. Parametrized here so the rework banks green before the carrier's `qNodeOf` lands. -/
abbrev QNodeFam (M : Fin (L + 1) → ℕ) (dCN : StepData M → ℕ) : Type :=
  ∀ node : StepData M, dCN node ≤ flatDim M →
    Params M ≃ₜ (Fin (dCN node) → ℝ) × (Fin (flatDim M - dCN node) → ℝ)

/-- **The diagonal-normalization TARGET** `d` (fork-15, buck-stops: node/edge-derived, no free field):
the `divBirthCoord` DIAGONAL cell of the divisor born at (or merged by) this edge — the canonical cell the
ledger references. case-1(1) merges divisor `mergeIdx`, so its target is that divisor's stored birth corner
`(a,b) ↦ flatCoordOf a b b` (mirrors `uCornerSel`; there the swap is a no-op — pivot = corner already);
case-1(2)/case-2 births a fresh divisor at corner `(layer, cleared) ↦ flatCoordOf layer cleared cleared`
(the block diagonal). Totality fallback (`Fin.castLE hd 0`) off the reachable cone / rollover (where
`geoChartMap` is `id`, so the target is unused). The source swap `S = (cNodeOf pivot ↔ diagTargetOf)`
relocates the exceptional divisor to this diagonal. Named (not inline) — consumed by the cocycle statement,
clause (D)'s gated intended-chart, and the fidelity story. -/
noncomputable def diagTargetOf (M : Fin (L + 1) → ℕ) (node : StepData M) (e : Edge M)
    (hd : 1 ≤ flatDim M) : Fin (flatDim M) :=
  match e.case with
  | StepCase.case11 =>
      if h : ∃ hm : e.subst.mergeIdx < node.numDiv,
          (node.divBirthCoord ⟨e.subst.mergeIdx, hm⟩).1 < L then
        let sc := node.divBirthCoord ⟨e.subst.mergeIdx, h.choose⟩
        if h2 : sc.2 < M (⟨sc.1, h.choose_spec⟩ : Fin L).castSucc ∧
            sc.2 < M (⟨sc.1, h.choose_spec⟩ : Fin L).succ then
          flatCoordOf M ⟨sc.1, h.choose_spec⟩ ⟨sc.2, h2.1⟩ ⟨sc.2, h2.2⟩
        else Fin.castLE hd 0
      else Fin.castLE hd 0
  | _ =>
      if h : node.layer < L then
        if h2 : node.cleared < M (⟨node.layer, h⟩ : Fin L).castSucc ∧
            node.cleared < M (⟨node.layer, h⟩ : Fin L).succ then
          flatCoordOf M ⟨node.layer, h⟩ ⟨node.cleared, h2.1⟩ ⟨node.cleared, h2.2⟩
        else Fin.castLE hd 0
      else Fin.castLE hd 0

/-- **The computed per-node chart** `β` (buck-stops: a function of the `GeoChart` data + banked atoms).
On the reachable cone (`dCN node ≤ flatDim M`, pivot in range) it is the `qNodeOf`-conjugated max-modulus
blow-up `pivotChart` on the node's FULL center coordinates (the per-node cover ruling: ONE `q` of dim
`dCN node`, all `dCenterOfNode` pivots share it), spectators passing through; off-cone / out-of-range it
is the identity (totality fallback). The R-b source gauge is composed in at the `LeafPullback` stage
(source reparam, doesn't move the image, so the cover reads `β` directly). -/
noncomputable def geoChartMap (dCN : StepData M → ℕ) (qN : QNodeFam M dCN)
    (g : GeoChart M) : Params M → Params M :=
  if hd : dCN g.node ≤ flatDim M then
    if hp : g.pivot < dCN g.node then
      let q := qN g.node hd
      fun w => q.symm (Prod.map (pivotChart ⟨g.pivot, hp⟩) id (q w))
    else id
  else id

/-- **The diagonal-NORMALIZED per-node chart** (fork-15): `(β ∘ S) ∘ (gauge g)` — the pure blow-up `β`
(`geoChartMap`) post-composed with the source swap `S = flatSwapCLE (cNodeOf pivot) (diagTargetOf)` (which
relocates the exceptional divisor to the ledger's `divBirthCoord` diagonal, `|det S| = 1`, cube-invariant)
and a COMPOSABLE det-1 source-gauge SLOT `gauge` (instantiated `fun _ => id` for the cover/Jacobian;
the R-b incidence shear `α` fills it later for `LeafPullback` — a parametric fill, no redefinition
ripple). Off-cone / out-of-range: `id` (the target is unused there). This is the atlas chart the
diagonal-normalized `tGeo`/`geoAtlas` fan out. -/
noncomputable def geoChartMapNorm (gauge : GeoChart M → Params M → Params M) (g : GeoChart M) :
    Params M → Params M :=
  if hd : dCenterOfNode M g.node ≤ flatDim M then
    if hp : g.pivot < dCenterOfNode M g.node then
      geoChartMap (dCenterOfNode M) (qNodeOf M) g ∘
        ⇑(flatSwapCLE M (cNodeOf M g.node hd ⟨g.pivot, hp⟩)
            (diagTargetOf M g.node g.edge (by omega))) ∘ gauge g
    else id
  else id

/-! **The geometric fan-out leaf paths** (amendment 1: EDGE-DRIVEN emission, per-NODE cover). Mirrors
`ResolutionTree.leafPaths` but at each edge fans out over the edge's `dCenterOfEdge` charts, assigning
each a GLOBAL pivot index into the node's `dCenterOfNode` center via a running `offset` (the disjoint
union partitioning `Fin (dCenterOfNode node)` across the node's edges — hbij), and composing
`geoChartMap` onto each child composite. The atlas is `geometricLeafPaths dCN qN id t`. The per-edge
child is recursed ONCE (with `id`); the fan-out + `acc`-composition is a post-`map` (structural). -/
mutual
/-- Geometric fan-out leaf paths of a subtree (see the section note above). -/
noncomputable def geometricLeafPaths (dCN : StepData M → ℕ) (qN : QNodeFam M dCN)
    (acc : Params M → Params M) :
    ResolutionTree M → List (LeafData M × (Params M → Params M))
  | .leaf l => [(l, acc)]
  | .branch n edges => geomEdges dCN qN acc n 0 edges
/-- Companion of `geometricLeafPaths` over an edge list (per-edge fan-out, global pivot offset). -/
noncomputable def geomEdges (dCN : StepData M → ℕ) (qN : QNodeFam M dCN)
    (acc : Params M → Params M) (n : StepData M) (offset : ℕ) :
    List (Edge M) → List (LeafData M × (Params M → Params M))
  | [] => []
  | .mk c s ch :: es =>
      ((geometricLeafPaths dCN qN id ch).flatMap fun lc =>
          (List.finRange (dCenterOfEdge n (Edge.mk c s ch))).map fun p =>
            (lc.1, acc ∘ geoChartMap dCN qN ⟨n, Edge.mk c s ch, offset + (p : ℕ)⟩ ∘ lc.2))
        ++ geomEdges dCN qN acc n (offset + dCenterOfEdge n (Edge.mk c s ch)) es
end

/-! ## Instantiation against the carrier (`QNodeCarrier`, t09)

The parametrization's payoff: pin `(dCN, qN) := (dCenterOfNode M, qNodeOf M)` (defeq
`QNodeFam M (dCenterOfNode M)`). The offset partition's range-correctness rides
`dCenterOfNode_edgeSum` (`Σ_e dCenterOfEdge = dCenterOfNode` on built branch nodes); the on-cone
`hd` is `dCenterOfNode_le_flatDim`. -/

/-! ## The geometric fan-out TREE `tGeo` (the cover fold's carrier, t10)

`geometricLeafPaths` above produces the flat atlas List directly; but clause (A)'s cover reuses the
banked tree-fold (`leafPathImages`/`ownCovers_branch`/`chartBridge_imageCover_of_ownCovers`,
`PivotCoverFold`), which is `ResolutionTree`-shaped. So the atlas is materialised as the LEAVES of an
auxiliary geometric fan-out tree `tGeo id t` (each node's edges fanned into its `dCenterOfNode` pivot
charts, `geoChartMap` on each fanned edge, the composite baked into each leaf's `chartMap` via the
accumulator). `tGeo` is a proof-internal device (not in `StepRel`/the spine); the atlas List IS
`leaves (tGeo id t)`, so the proven headline `chartBridge_imageCover_of_ownCovers (tGeo id t)` emits
clause (A) over `geoAtlas` verbatim (countersign item 2). -/
mutual
/-- **The geometric fan-out tree** of a subtree: refine each branch by fanning its edges into their
`dCenterOfEdge` pivot charts (each fanned edge's `localSub := geoChartMap` for one GLOBAL pivot index,
the running `offset`), threading the geometric composite into `acc` so a leaf's baked `chartMap` = the
root→leaf `geoChartMap` fold (coherence). -/
noncomputable def tGeo (acc : Params M → Params M) : ResolutionTree M → ResolutionTree M
  | .leaf l => .leaf { l with chartMap := acc }
  | .branch n edges => .branch n (fannedEdges acc n 0 edges)
/-- Companion of `tGeo` over an edge list (per-edge fan-out, global pivot offset — the disjoint
partition tiling `Fin (dCenterOfNode n)` across the node's edges, `dCenterOfNode_edgeSum`). A CHARTLESS
edge (`dCenterOfEdge = 0`, e.g. a rollover layer-relabel) is passed through as ONE identity edge — its
child subtree's charts belong to the atlas (composed with `id`); dropping it (`finRange 0 = []`) would
lose the whole subtree and break the cover (rollovers sit on the main path). -/
noncomputable def fannedEdges (acc : Params M → Params M) (n : StepData M) (offset : ℕ) :
    List (Edge M) → List (Edge M)
  | [] => []
  | .mk c s ch :: es =>
      -- The chartless branch forwards the child with `acc` UNCHANGED (`acc ∘ id = acc`) and does NOT
      -- advance the offset (`+ 0`), so charted siblings tile `Fin (dCenterOfNode n)` unchanged and the
      -- recursion is on the structurally-smaller child. CORNER for the (D) lane: `dCenterOfEdge = 0`
      -- occurs at a rollover node AND at a case-1(2)/case-2 edge with `resCols = 0`; at either the
      -- faithful chart is `id` (a 0-count blow-up IS geometrically the identity, matching `geoChartMap`
      -- at an out-of-range pivot). Clause (D)'s "intended chart at edge `e`" is `dCenterOfEdge`-GATED
      -- (`id` at 0, the pivot-fan at ≥ 1).
      (if dCenterOfEdge n (Edge.mk c s ch) = 0 then
        [Edge.mk c { s with localSub := id } (tGeo acc ch)]
      else
        (List.finRange (dCenterOfEdge n (Edge.mk c s ch))).map (fun p =>
          Edge.mk c { s with localSub := geoChartMapNorm (fun _ => id)
                               ⟨n, Edge.mk c s ch, offset + (p : ℕ)⟩ }
            (tGeo (acc ∘ geoChartMapNorm (fun _ => id)
                      ⟨n, Edge.mk c s ch, offset + (p : ℕ)⟩) ch)))
      ++ fannedEdges acc n (offset + dCenterOfEdge n (Edge.mk c s ch)) es
end

/-- **The flat virtual-leaf atlas** for `t`: the leaves of the geometric fan-out tree `tGeo id t`
(countersign item 2 — the atlas List realised as `leaves t_geo`, so the banked tree-fold headline
emits clause (A) verbatim). Each leaf carries its ledger data (`divCoord`/`resCoord`/`srcBox`/
exponents) with `chartMap` = the baked geometric `β`-fold composite (a function of `t` alone, via
`qNodeOf` — the buck-stops geometry). This is the `List (LeafData M)` the corrected `ChartBridge`
quantifies over. -/
noncomputable def geoAtlas (t : ResolutionTree M) : List (LeafData M) :=
  ResolutionTree.leaves (tGeo id t)

/-! ## `tGeo` coherence (the `chartBridge_imageCover_of_ownCovers` hypothesis)

Each `tGeo id t` leaf's baked `chartMap` equals its root→leaf `leafPaths id` composite — the coherence
`chartBridge_imageCover_of_ownCovers` (`PivotCoverFold`) demands to turn `leafPathImages` into
`⋃ l ∈ leaves, l.chartMap '' l.srcBox`. Two `leafPaths`-companion helpers, then the mutual induction
(mirroring `leafPaths_mapFst`/`imgAcc`). Fix-independent (holds for any atlas srcBox / cover shape). -/

/-- `edgesLeafPaths` distributes over list append. -/
theorem edgesLeafPaths_append (acc : Params M → Params M) (l1 l2 : List (Edge M)) :
    ResolutionTree.edgesLeafPaths acc (l1 ++ l2)
      = ResolutionTree.edgesLeafPaths acc l1 ++ ResolutionTree.edgesLeafPaths acc l2 := by
  induction l1 with
  | nil => simp [ResolutionTree.edgesLeafPaths]
  | cons e es ih =>
      obtain ⟨c, s, ch⟩ := e
      simp only [List.cons_append, ResolutionTree.edgesLeafPaths, ih, List.append_assoc]

/-- `edgesLeafPaths` of a `.mk`-built mapped edge-list is the `flatMap` of the per-element `leafPaths`. -/
theorem edgesLeafPaths_mapMk {α : Type*} (acc : Params M → Params M) (g : α → StepCase)
    (sub : α → ChartSubst M) (chi : α → ResolutionTree M) (l : List α) :
    ResolutionTree.edgesLeafPaths acc (l.map (fun a => Edge.mk (g a) (sub a) (chi a)))
      = l.flatMap (fun a => ResolutionTree.leafPaths (acc ∘ (sub a).localSub) (chi a)) := by
  induction l with
  | nil => simp [ResolutionTree.edgesLeafPaths]
  | cons a as ih =>
      simp only [List.map_cons, ResolutionTree.edgesLeafPaths, ih, List.flatMap_cons]

mutual
/-- **`tGeo` coherence**: every `tGeo acc t` leaf's baked `chartMap` equals its `leafPaths acc`
composite (so `chartBridge_imageCover_of_ownCovers` applies to `tGeo id t`). -/
theorem tGeo_coherence (acc : Params M → Params M) :
    ∀ t : ResolutionTree M, ∀ p ∈ ResolutionTree.leafPaths acc (tGeo acc t), p.1.chartMap = p.2
  | .leaf l => by
      intro p hp
      rw [tGeo, ResolutionTree.leafPaths] at hp
      simp only [List.mem_singleton] at hp
      subst hp; rfl
  | .branch n edges => by
      intro p hp
      rw [tGeo, ResolutionTree.leafPaths] at hp
      exact fannedEdges_coherence acc n 0 edges p hp
/-- Companion of `tGeo_coherence` over an edge list. -/
theorem fannedEdges_coherence (acc : Params M → Params M) (n : StepData M) (offset : ℕ) :
    ∀ edges : List (Edge M),
      ∀ p ∈ ResolutionTree.edgesLeafPaths acc (fannedEdges acc n offset edges), p.1.chartMap = p.2
  | [] => by intro p hp; rw [fannedEdges] at hp; simp [ResolutionTree.edgesLeafPaths] at hp
  | .mk c s ch :: es => by
      intro p hp
      rw [fannedEdges, edgesLeafPaths_append, List.mem_append] at hp
      rcases hp with hp | hp
      · by_cases hz : dCenterOfEdge n (Edge.mk c s ch) = 0
        · rw [if_pos hz] at hp
          simp only [ResolutionTree.edgesLeafPaths, List.append_nil] at hp
          exact tGeo_coherence acc ch p hp
        · rw [if_neg hz, edgesLeafPaths_mapMk, List.mem_flatMap] at hp
          obtain ⟨i, _, hp⟩ := hp
          exact tGeo_coherence _ ch p hp
      · exact fannedEdges_coherence acc n (offset + dCenterOfEdge n (Edge.mk c s ch)) es p hp
end

end DLNFibre.DLN.RLCT.Engine
