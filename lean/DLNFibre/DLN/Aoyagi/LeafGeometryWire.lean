import DLNFibre.DLN.Aoyagi.MonumentAtlas
import DLNFibre.DLN.Aoyagi.GeometricAtlasD12

/-!
# `DLN.Aoyagi.LeafGeometryWire` — L8 (+ L6) standalone leaf proofs (SEAT-L3T, fresh lane)

The exponent-ledger leaf (L8) and the chart-geometry leaf (L6) of the monument, proved standalone
(statement-identical to `MonumentAtlas`, primed to avoid the import clash — arch-C swaps the leaf
sorries to `:= …'` at integration). L8 is the combinatorial ledger match; it consumes `FoldProduced`'s
own read-off clauses + the banked `leaf_divExp_mem_terminalExponents`, generalizing the landed
`GeometricAtlasD12.exists_atlasRealizesExponents_d12`.
-/

open MeasureTheory Set Filter Topology RLCT
open DLNFibre.Core DLNFibre.Core.Aoyagi DLNFibre.DLN.RLCT DLNFibre.DLN.RLCT.Engine

namespace DLNFibre.DLN.Aoyagi

variable {N : ℕ}

/-- **L8 — the atlas exponents realize the built tree's terminal spectrum** (statement-identical to
`MonumentAtlas.leafPath_realizesExponents`; primed). Both clauses read off `FoldProduced`: clause (i)
via `hjac_mem` + `leaf_divExp_mem_terminalExponents`; clause (ii) via `hsurj` + `hjac_onto`. -/
theorem leafPath_realizesExponents' (d : Fin (N + 1) → ℕ) (hN : 0 < N)
    (hpos : ∀ k, 0 < d k) (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (atlas : GeoAtlasData d e)
    (hfold : FoldProduced d e atlas) :
    (∀ (c : Fin atlas.n) (a : Fin (flatDim d)), a ∈ bindingAxes (atlas.bexp c) →
        (atlas.jac c a + 1) ∈
          ResolutionTree.terminalExponents (buildTree d (conOracle d) (conRoot : ConState N))) ∧
      (∀ l ∈ ResolutionTree.leaves (buildTree d (conOracle d) (conRoot : ConState N)),
        ∀ k : Fin l.numDiv, l.divExp k = minAdm d →
          ∃ (c : Fin atlas.n) (a : Fin (flatDim d)),
            a ∈ bindingAxes (atlas.bexp c) ∧ atlas.jac c a + 1 = l.divExp k) := by
  obtain ⟨leafOf, hmem, hsurj, hjac_mem, hjac_onto, _hdom_ball, _hstep, _hjac_tie, _hcard⟩ := hfold
  refine ⟨?_, ?_⟩
  · -- clause (i): jac c a + 1 = leafOf c divExp k ∈ terminalExponents (leafOf c ∈ leaves)
    intro c a ha
    obtain ⟨k, hk⟩ := hjac_mem c a ha
    rw [hk]
    exact leaf_divExp_mem_terminalExponents _ (leafOf c) (hmem c) k
  · -- clause (ii): the minAdm leaf is reached by a chart (hsurj) whose binding axis realizes it (hjac_onto)
    intro l hl k _hlk
    obtain ⟨c, hc⟩ := hsurj l hl
    subst hc
    obtain ⟨a, ha, ha2⟩ := hjac_onto c k
    exact ⟨c, a, ha, ha2⟩

end DLNFibre.DLN.Aoyagi
