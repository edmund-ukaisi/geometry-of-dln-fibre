import DLNFibre.DLN.RLCT.Engine.GeoCoverSpec
import DLNFibre.DLN.RLCT.Engine.GeoLeafJacobian
import DLNFibre.DLN.RLCT.Engine.GeoLeafLedger
import DLNFibre.DLN.RLCT.Engine.GeoInjFold
import DLNFibre.DLN.RLCT.Engine.NodesCNodeWalk

/-!
# `DLNFibre.DLN.RLCT.Engine.ChartBridgeFaithful` — clause (D), the geometric-fidelity assembly

The elder charge-4 ruling (2026-07-19) ADOPTED the R-split: clause (D), the geometric-chart
fidelity tie, cannot be a conjunct of `ChartBridge` in `EngineDefs`. The intended names
(`geoChartMapNorm`, `diagTargetOf`, `geoAtlas`, `cNodeOf`, `realCNode`) all sit ABOVE `EngineDefs`
in the import DAG, and `ChartBridge` is pinned low by `CanonicalResolution`/`EngineConstruction`. So
(D) lives here as a HIGH-level predicate plus a faithful discharge, and enters the payoff's proof
CONE through the PROJECTION — strictly stronger than the old in-type form (undroppable).

* `ChartBridgeFidelity M t atlas` — two-sided honesty. (1) `atlas = geoAtlas t`: the atlas IS the
  gated geometric fan-out (each chart the `geoChartMapNorm` fold, `id` at `dCenterOfEdge = 0`
  implicit through `fannedEdges`, `diagTargetOf`-relocated — false on a generic atlas). (2) every
  internal node's center selector is the INTENDED one, `cNodeOf = realCNode` (blows up the
  ledger-born coords, not the injectivity fallback — false on a non-faithful tree). Conjunct 2's
  proof is the ALL-NODES LIFT (t09's `cNodeOf_eq_realCNode_of_conOracle`, Card-3 deferred item 2),
  i.e. `nodes_cNode_eq_realCNode`.
* `ChartBridgeFaithful M t` — `ChartBridge`'s `(A)∧(B)∧(C)` body over the SAME witnessing atlas,
  conjoined with `ChartBridgeFidelity`. `ChartBridgeFaithful.toChartBridge` projects it to
  `ChartBridge` (what `region_glue` consumes, destructure-and-discard, clean-three).
* `chartBridgeFaithful_buildTree` — the faithful discharge over the built tree. THE PROJECTION IS
  THE GATE (elder Q-a): when `chartBridge_buildTree` (`EngineObligations`) is filled, its proof term
  MUST be the projection of this, putting (D) on the payoff's cone.
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open MeasureTheory Set

variable {L : ℕ} {M : Fin (L + 1) → ℕ}

/-- **Clause (D) fidelity** (two-sided honesty; R-split high-level predicate). Conjunct 1 pins the
atlas to the gated geometric fan-out `geoAtlas t` (false on a generic atlas); conjunct 2 is the
all-nodes lift `cNodeOf = realCNode` (intended coords, not the fallback — false on a non-faithful
tree). -/
def ChartBridgeFidelity (M : Fin (L + 1) → ℕ) (t : ResolutionTree M)
    (atlas : List (LeafData M)) : Prop :=
  atlas = geoAtlas t ∧
    (∀ n ∈ ResolutionTree.nodes t, ∀ hd : dCenterOfNode M n ≤ flatDim M,
        cNodeOf M n hd = realCNode M n hd)

/-- **`ChartBridge` with clause (D)** (R-split): the `(A)∧(B)∧(C)` body over the SAME witnessing
atlas, conjoined with `ChartBridgeFidelity`. The body is copied verbatim from `ChartBridge`
(`EngineDefs`) so the projection to `ChartBridge` is definitional. -/
def ChartBridgeFaithful (M : Fin (L + 1) → ℕ) (t : ResolutionTree M) : Prop :=
  ∃ atlas : List (LeafData M),
    ((∃ U : Set (Params M), IsOpen U ∧ (0 : Params M) ∈ U ∧
        U ⊆ ⋃ c ∈ atlas, c.chartMap '' c.srcBox) ∧
      (∀ c ∈ atlas,
        MeasurableSet c.srcBox ∧
          (∃ R : ℝ, 0 < R ∧ c.srcBox ⊆ ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) R) ∧
          Function.Injective c.divCoord ∧ Function.Injective c.resCoord ∧
          Disjoint (Set.range c.divCoord) (Set.range c.resCoord) ∧
          (∃ N : Set (Params M), volume N = 0 ∧ Set.InjOn c.chartMap (c.srcBox \ N)) ∧
          LeafPullback c ∧ LeafJacobian c) ∧
      (∀ c ∈ atlas, (∀ k : Fin c.numDiv, c.divExp k ∈ ResolutionTree.terminalExponents t) ∧
        (0 < c.resRank → c.resRank ∈ ResolutionTree.terminalExponents t))) ∧
    ChartBridgeFidelity M t atlas

/-- **The projection is the gate**: `ChartBridgeFaithful` weakens to `ChartBridge` (drop clause
(D)) — what `region_glue` consumes. Definitional: the `(A)∧(B)∧(C)` body is copied verbatim. Named
`ChartBridgeFaithful.toChartBridge` (drop-D) so `h.toChartBridge` reads as the projection. -/
theorem ChartBridgeFaithful.toChartBridge (t : ResolutionTree M)
    (h : ChartBridgeFaithful M t) : ChartBridge M t :=
  let ⟨atlas, hABC, _⟩ := h; ⟨atlas, hABC⟩

/-- **The faithful discharge over the built tree** (the R-split gate object). (A) cover is
`geoAtlas_imageCover` (green, t10); clause (D) is fully PROVEN — conjunct 1 is `rfl`, conjunct 2 is
the all-nodes lift `nodes_cNode_eq_realCNode`. The remaining ingredient is the `(B)∧(C)` per-piece
props/exponents over `geoAtlas` (the two frontier sorries): the ledger props + exponents via a
`geoAtlas`-leaf↔ledger bridge, a.e.-injectivity + `LeafPullback` (geometric), and `LeafJacobian` =
t14's `geoAtlas_fold_det`. `hMpos` is threaded (the `(B)∧(C)` fill needs positive widths, as
`o5_realization`/the cover do); currently unused by the proven `(A)`/(D) parts.
`chartBridge_buildTree` is its `toChartBridge` projection, so (D) is on the payoff's proof cone. -/
theorem chartBridgeFaithful_buildTree (M : Fin (L + 1) → ℕ) (_hL : 0 < L)
    (_hMpos : ∀ i, 0 < M i) :
    ChartBridgeFaithful M (buildTree M (conOracle M) (conRoot : ConState L)) :=
  ⟨geoAtlas (buildTree M (conOracle M) conRoot),
    ⟨geoAtlas_imageCover (buildTree M (conOracle M) conRoot) conRoot rfl,
      -- (B) per-piece props: the 5 ledger props from the bridge (`geoAtlas_leaf_ledgerProps`) + the
      -- a.e.-injectivity clause (`geoAtlas_leaf_ae_injOn`, `GeoInjFold`); the 2 remaining geometric
      -- props are `LeafPullback` (loss-seat's α gauge) and `LeafJacobian` (t14's fold bundle).
      (fun c hc =>
        let ⟨hmeas, hbdd, hdiv, hres, hdisj, _, _⟩ := geoAtlas_leaf_ledgerProps c hc
        ⟨hmeas, hbdd, hdiv, hres, hdisj, geoAtlas_leaf_ae_injOn c hc, sorry, sorry⟩),
      -- (C) exponent agreement — from the bridge:
      (fun c hc =>
        let ⟨_, _, _, _, _, hexpDiv, hexpRes⟩ := geoAtlas_leaf_ledgerProps c hc
        ⟨hexpDiv, hexpRes⟩)⟩,
    rfl,
    nodes_cNode_eq_realCNode conRoot DivBirthInv_conRoot⟩

end DLNFibre.DLN.RLCT.Engine
