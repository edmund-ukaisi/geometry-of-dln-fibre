import DLNFibre.DLN.RLCT.Engine.QNodeChart
import DLNFibre.DLN.RLCT.Engine.ShearReconcile

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
the `edge` (its case/subst fix the family + the per-edge count, and key `qEdgeOf`), and the `pivot`
choice within the edge's family (`< dCenterOfEdge node edge`). The chart `geoChartMap` is COMPUTED from
these; no stored free geometry. -/
structure GeoChart (M : Fin (L + 1) → ℕ) where
  /-- The parent blow-up node (keys `qEdgeOf` + `divBirthCoord`). -/
  node : StepData M
  /-- The edge (its `case`/`subst` fix the per-edge family + count). -/
  edge : Edge M
  /-- The pivot choice within this edge's family (`< dCenterOfEdge node edge`). -/
  pivot : ℕ

/-- **The computed per-edge chart** `β_e` (buck-stops: a function of the `GeoChart` data + banked atoms).
On the reachable cone (`dCenterOfEdge node edge ≤ flatDim M`, and the pivot in range) it is the
`qEdgeOf`-conjugated max-modulus blow-up `pivotChart` on the edge's center coordinates, with the
spectators passing through; off-cone / out-of-range it is the identity (totality fallback, matching the
carrier's `qEdgeOf` fallback). The R-b source gauge is composed in at the `LeafPullback` stage (it is a
SOURCE reparam and does not move the chart image, so the cover reads `β_e` directly). -/
noncomputable def geoChartMap (g : GeoChart M) : Params M → Params M :=
  if hd : dCenterOfEdge g.node g.edge ≤ flatDim M then
    if hp : g.pivot < dCenterOfEdge g.node g.edge then
      let q := qEdgeOf g.node g.edge hd
      fun w => q.symm (Prod.map (pivotChart ⟨g.pivot, hp⟩) id (q w))
    else id
  else id

/-! **The geometric fan-out leaf paths** (amendment 1: EDGE-DRIVEN). Mirrors `ResolutionTree.leafPaths`
but at each edge fans out over the edge's `dCenterOfEdge` pivot family, composing `geoChartMap` onto
each child composite — one `(leaf, root→leaf composite)` pair per (leaf × pivot-choice sequence). The
atlas is `geometricLeafPaths id t`. The per-edge child is recursed ONCE (with `id`) and the fan-out +
`acc`-composition is a post-`map` (keeps the recursion structural). `geoChartMap` is COMPUTED — buck-stops. -/
mutual
/-- Geometric fan-out leaf paths of a subtree (see the section note above). -/
noncomputable def geometricLeafPaths (acc : Params M → Params M) :
    ResolutionTree M → List (LeafData M × (Params M → Params M))
  | .leaf l => [(l, acc)]
  | .branch n edges => geomEdges acc n edges
/-- Companion of `geometricLeafPaths` over an edge list (per-edge pivot fan-out). -/
noncomputable def geomEdges (acc : Params M → Params M) (n : StepData M) :
    List (Edge M) → List (LeafData M × (Params M → Params M))
  | [] => []
  | .mk c s ch :: es =>
      ((geometricLeafPaths id ch).flatMap fun lc =>
          (List.finRange (dCenterOfEdge n (Edge.mk c s ch))).map fun p =>
            (lc.1, acc ∘ geoChartMap ⟨n, Edge.mk c s ch, (p : ℕ)⟩ ∘ lc.2))
        ++ geomEdges acc n es
end

end DLNFibre.DLN.RLCT.Engine
