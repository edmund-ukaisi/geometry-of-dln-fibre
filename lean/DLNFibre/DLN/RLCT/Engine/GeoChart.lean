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

end DLNFibre.DLN.RLCT.Engine
