import DLNFibre.DLN.RLCT.Engine.GeoCoverSpec
import DLNFibre.DLN.RLCT.Engine.GeoLeafJacobian
import DLNFibre.DLN.RLCT.Engine.GeoLeafLedger
import DLNFibre.DLN.RLCT.Engine.GeoInjFold
import DLNFibre.DLN.RLCT.Engine.GeoAtlasTransfer
import DLNFibre.DLN.RLCT.Engine.NodesCNodeWalk

/-!
# `DLNFibre.DLN.RLCT.Engine.ChartBridgeFaithful` — clause (D), the geometric-fidelity assembly

The elder charge-4 ruling (2026-07-19) ADOPTED the R-split: clause (D), the geometric-chart
fidelity tie, cannot be a conjunct of `ChartBridge` in `EngineDefs`. The intended names
(`geoChartMapNorm`, `diagTargetOf`, `geoAtlas`, `cNodeOf`, `realCNode`) all sit ABOVE `EngineDefs`
in the import DAG, and `ChartBridge` is pinned low by `CanonicalResolution`/`EngineConstruction`. So
(D) lives here as a HIGH-level predicate plus a faithful discharge, and enters the payoff's proof
CONE through the PROJECTION — strictly stronger than the old in-type form (undroppable).

* `ChartBridgeFidelity M t atlas` — two-sided honesty. (1) `atlas = geoAtlasNorm alphaGauge t`: the
  atlas IS the α-normalized geometric fan-out (each chart the `geoChartMapNorm alphaGauge` fold — the
  diagonal-placement permutation `S` AND the incidence Schur gauge `α`, Aoyagi's integration chart
  reached only after the regular Q,P normalization; `id` at `dCenterOfEdge = 0` through
  `fannedEdgesG`, `diagTargetOf`-relocated — false on a generic atlas). The α witness supersedes the
  fork-15 id placeholder (atlas-seam ruling, compass fork 15 third amendment: `LeafPullback`-at-id is
  false). (2) every internal node's center selector is the INTENDED one, `cNodeOf = realCNode` (blows
  up the ledger-born coords, not the injectivity fallback — false on a non-faithful tree). Conjunct
  2's proof is the ALL-NODES LIFT (t09's `cNodeOf_eq_realCNode_of_conOracle`, Card-3 deferred item 2),
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
atlas to the α-normalized geometric fan-out `geoAtlasNorm alphaGauge t` — Aoyagi's integration chart
(the diagonal-placement permutation composed with the incidence Schur gauge `α`), NOT the fork-15 id
placeholder (atlas-seam ruling; false on a generic atlas). Conjunct 2 is the all-nodes lift
`cNodeOf = realCNode` (intended coords, not the fallback — false on a non-faithful tree). -/
def ChartBridgeFidelity (M : Fin (L + 1) → ℕ) (t : ResolutionTree M)
    (atlas : List (LeafData M)) : Prop :=
  atlas = geoAtlasNorm (alphaGauge (M := M)) t ∧
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

/-- **The faithful discharge over the built tree** (the R-split gate object), over the α-normalized
atlas `geoAtlasNorm alphaGauge` (atlas-seam ruling — Aoyagi's integration chart). Clause (D) is fully
PROVEN — conjunct 1 is `rfl` (the witness IS `geoAtlasNorm alphaGauge (buildTree …)`), conjunct 2 is
the all-nodes lift `nodes_cNode_eq_realCNode`. The `(B)`/`(C)` props transfer to the α atlas
(`GeoAtlasTransfer`): ledger props + exponents (`geoAtlasNorm_leaf_ledgerProps`, verbatim from the
original leaf — the α gauge touches only `chartMap`), a.e.-injectivity (`geoAtlasNorm_leaf_ae_injOn`, α
an injective QMP homeomorph), `LeafPullback` = loss-t15's `leafPullback_geoAtlasNorm` (its `sorry` is
`leafDiagFrob_geoAtlasNorm`). TWO transfer-owed frontiers: clause (A) `geoAtlasNorm_imageCover` (cover
open-homeo route, SURFACED) and `LeafJacobian` = `geoAtlasNorm_leaf_leafJacobian` (gauge-generalized
cocycle, pending elder counter-sign). `hMpos` is threaded for `LeafJacobian`'s positive-width need.
`chartBridge_buildTree` is its `toChartBridge` projection, so (D) is on the payoff's proof cone. -/
theorem chartBridgeFaithful_buildTree (M : Fin (L + 1) → ℕ) (_hL : 0 < L)
    (_hMpos : ∀ i, 0 < M i) :
    ChartBridgeFaithful M (buildTree M (conOracle M) (conRoot : ConState L)) :=
  ⟨geoAtlasNorm (alphaGauge (M := M)) (buildTree M (conOracle M) conRoot),
    ⟨geoAtlasNorm_imageCover (buildTree M (conOracle M) conRoot) conRoot rfl,
      -- (B) per-piece props over the α atlas: the 5 ledger props (`geoAtlasNorm_leaf_ledgerProps`) +
      -- a.e.-injectivity (`geoAtlasNorm_leaf_ae_injOn`); `LeafPullback` = loss-t15's
      -- `leafPullback_geoAtlasNorm` DIRECTLY (same atlas — membership definitional); `LeafJacobian` =
      -- the α-atlas transfer `geoAtlasNorm_leaf_leafJacobian`.
      (fun c hc =>
        let ⟨hmeas, hbdd, hdiv, hres, hdisj, _, _⟩ :=
          geoAtlasNorm_leaf_ledgerProps (alphaGauge (M := M)) c hc
        ⟨hmeas, hbdd, hdiv, hres, hdisj, geoAtlasNorm_leaf_ae_injOn c hc,
          -- REFUTED-AS-STATED (#3a, cert-full-value-walk §6): this `LeafPullback`
          -- conjunct routes through `leafDiagFrob_geoAtlasNorm`'s `sorry` — the chart-CoV
          -- value half, category-false for ALL charts (no chart bounds the residual core
          -- below on an open set), not fillable. Honest lower bound = ideal-level (Lemma 1).
          leafPullback_geoAtlasNorm c hc,
          geoAtlasNorm_leaf_leafJacobian (flatDim_pos_of_append _hL
            (show (0 : ℕ) < widthMinUpto M (0 + 1) by
              rw [widthMinUpto, Finset.lt_inf'_iff]; exact fun i _ => _hMpos i)) c hc⟩),
      -- (C) exponent agreement — from the α-atlas ledger transfer:
      (fun c hc =>
        let ⟨_, _, _, _, _, hexpDiv, hexpRes⟩ :=
          geoAtlasNorm_leaf_ledgerProps (alphaGauge (M := M)) c hc
        ⟨hexpDiv, hexpRes⟩)⟩,
    rfl,
    nodes_cNode_eq_realCNode conRoot DivBirthInv_conRoot⟩

end DLNFibre.DLN.RLCT.Engine
