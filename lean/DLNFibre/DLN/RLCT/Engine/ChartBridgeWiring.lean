import DLNFibre.DLN.RLCT.Engine.EngineDefs

/-!
# `DLNFibre.DLN.RLCT.Engine.ChartBridgeWiring` — the whole-`ChartBridge` wiring skeleton (rung 3)

The flat virtual-leaf atlas assembly: `chartBridge_of_pieces` builds `ChartBridge M t` from the
coverage atlas, so the discharge closes the moment the carrier + coverage supply the pieces. Under the
corrected type (`EngineDefs.ChartBridge` = a flat `List (LeafData M)` of geometric chart pieces) this
is a BUNDLING — each atlas piece carries its OWN real `chartMap`, so the three fed Props
(`a.e.-InjOn` / `LeafPullback` / `LeafJacobian`) are stated directly against the piece, with no
fold-form `χ` indirection and no stored/fold coherence rewrite (the frozen type needed those only to
route around the ledger leaf's placeholder `chartMap`).
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open MeasureTheory Set

variable {L : ℕ} {M : Fin (L + 1) → ℕ}

/-- **The whole-`ChartBridge` wiring skeleton** (flat virtual-leaf atlas). Given the `atlas` of
geometric chart pieces, the image-cover over it (`himg`, clause A), the eight per-piece clauses
(`hleaf`, clause B — the three carrier-fed Props `a.e.-InjOn` / `LeafPullback` / `LeafJacobian` enter
here, each over the piece's OWN chart), and the exponent-agreement (`hexp`, clause C), `ChartBridge M t`
holds. A bundling: no `χ`, no coherence rewrite, because each piece carries the real chart. -/
theorem chartBridge_of_pieces (t : ResolutionTree M) (atlas : List (LeafData M))
    (himg : ∃ U : Set (Params M), IsOpen U ∧
      {A : Params M | A ∈ paramsBoxM M 1 ∧ frobSq (prod M A) = 0} ⊆ U ∧
      U ⊆ ⋃ c ∈ atlas, c.chartMap '' c.srcBox)
    (hleaf : ∀ c ∈ atlas,
      MeasurableSet c.srcBox ∧
        (∃ R : ℝ, 0 < R ∧ c.srcBox ⊆ ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) R) ∧
        Function.Injective c.divCoord ∧ Function.Injective c.resCoord ∧
        Disjoint (Set.range c.divCoord) (Set.range c.resCoord) ∧
        (∃ N : Set (Params M), volume N = 0 ∧ Set.InjOn c.chartMap (c.srcBox \ N)) ∧
        LeafPullback c ∧ LeafJacobian c)
    (hexp : ∀ c ∈ atlas, (∀ k : Fin c.numDiv, c.divExp k ∈ ResolutionTree.terminalExponents t) ∧
      (0 < c.resRank → c.resRank ∈ ResolutionTree.terminalExponents t)) :
    ChartBridge M t :=
  ⟨atlas, himg, hleaf, hexp⟩

end DLNFibre.DLN.RLCT.Engine
