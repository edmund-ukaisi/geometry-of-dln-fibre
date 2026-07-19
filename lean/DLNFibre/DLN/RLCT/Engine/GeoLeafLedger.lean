import DLNFibre.DLN.RLCT.Engine.GeoCoverSpec
import DLNFibre.DLN.RLCT.Engine.PivotLeafClauses
import DLNFibre.DLN.RLCT.Engine.NodesCNodeWalk

/-!
# `DLNFibre.DLN.RLCT.Engine.GeoLeafLedger` — the geoAtlas-leaf↔ledger bridge ((B)/(C) keystone)

Each geometric atlas piece is `tGeo`'s `{ l with chartMap := … }` at a leaf, so its ledger FIELDS
(`numDiv`/`divCoord`/`divExp`/`srcBox`/`resCoord`/`resRank`) are inherited VERBATIM from an original
`t`-leaf; only `chartMap` differs. `tGeo_leaf_update` proves this correspondence (mutual induction
over `tGeo`/`fannedEdges`, mirroring `tGeo_coherence`); the (B) ledger props + all of (C) then
transfer from the original leaf — `flatCubeSrcBox_*` for measurable/bounded (the srcBox is the flat
cube), `leaves_chart_clauses_conRoot` for divCoord/resCoord inj+disjoint, `terminalExponents`'
`flatMap` for the exponents. The geometric props (a.e.-inj, `LeafPullback`, `LeafJacobian`) live
elsewhere.
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT

variable {L : ℕ} {M : Fin (L + 1) → ℕ}

/-- `edgesLeaves` distributes over list append. -/
theorem edgesLeaves_append (l1 l2 : List (Edge M)) :
    ResolutionTree.edgesLeaves (l1 ++ l2)
      = ResolutionTree.edgesLeaves l1 ++ ResolutionTree.edgesLeaves l2 := by
  induction l1 with
  | nil => simp [ResolutionTree.edgesLeaves]
  | cons e es ih =>
      obtain ⟨c, s, ch⟩ := e
      simp only [List.cons_append, ResolutionTree.edgesLeaves, ih, List.append_assoc]

/-- `edgesLeaves` of a `.mk`-built mapped edge-list is the `flatMap` of the per-element children. -/
theorem edgesLeaves_mapMk {α : Type*} (g : α → StepCase) (sub : α → ChartSubst M)
    (chi : α → ResolutionTree M) (l : List α) :
    ResolutionTree.edgesLeaves (l.map (fun a => Edge.mk (g a) (sub a) (chi a)))
      = l.flatMap (fun a => ResolutionTree.leaves (chi a)) := by
  induction l with
  | nil => simp [ResolutionTree.edgesLeaves]
  | cons a as ih =>
      simp only [List.map_cons, ResolutionTree.edgesLeaves, ih, List.flatMap_cons]

mutual
/-- **The ledger correspondence**: every `tGeo acc t` leaf is `{ l with chartMap := f }` for some
original `t`-leaf `l` — the ledger fields are inherited verbatim. -/
theorem tGeo_leaf_update (acc : Params M → Params M) :
    ∀ t : ResolutionTree M, ∀ c ∈ ResolutionTree.leaves (tGeo acc t),
      ∃ l ∈ ResolutionTree.leaves t, ∃ f : Params M → Params M, c = { l with chartMap := f }
  | .leaf l => by
      intro c hc
      rw [tGeo, ResolutionTree.leaves, List.mem_singleton] at hc
      subst hc
      exact ⟨l, by simp [ResolutionTree.leaves], acc, rfl⟩
  | .branch n edges => by
      intro c hc
      rw [tGeo, ResolutionTree.leaves] at hc
      obtain ⟨l, hl, f, hf⟩ := fannedEdges_leaf_update acc n 0 edges c hc
      exact ⟨l, by rw [ResolutionTree.leaves]; exact hl, f, hf⟩
/-- Companion of `tGeo_leaf_update` over an edge list (per-edge fan-out). -/
theorem fannedEdges_leaf_update (acc : Params M → Params M) (n : StepData M) (offset : ℕ) :
    ∀ edges : List (Edge M),
      ∀ c ∈ ResolutionTree.edgesLeaves (fannedEdges acc n offset edges),
        ∃ l ∈ ResolutionTree.edgesLeaves edges, ∃ f : Params M → Params M,
          c = { l with chartMap := f }
  | [] => by intro c hc; rw [fannedEdges] at hc; cases hc
  | .mk ec esub ch :: rest => by
      intro c hc
      rw [fannedEdges, edgesLeaves_append, List.mem_append] at hc
      rcases hc with hc | hc
      · -- `c` in the fanned copies of `ch`'s leaves — reduce to a `tGeo acc' ch` leaf via the IH
        have hch : ∃ acc', c ∈ ResolutionTree.leaves (tGeo acc' ch) := by
          by_cases hz : dCenterOfEdge n (Edge.mk ec esub ch) = 0
          · rw [if_pos hz] at hc
            simp only [ResolutionTree.edgesLeaves, List.append_nil] at hc
            exact ⟨acc, hc⟩
          · rw [if_neg hz, edgesLeaves_mapMk, List.mem_flatMap] at hc
            obtain ⟨p, _, hcp⟩ := hc
            exact ⟨_, hcp⟩
        obtain ⟨acc', hcp⟩ := hch
        obtain ⟨l, hl, f, hf⟩ := tGeo_leaf_update acc' ch c hcp
        exact ⟨l, by rw [ResolutionTree.edgesLeaves]; exact List.mem_append_left _ hl, f, hf⟩
      · obtain ⟨l, hl, f, hf⟩ :=
          fannedEdges_leaf_update acc n (offset + dCenterOfEdge n (Edge.mk ec esub ch)) rest c hc
        exact ⟨l, by rw [ResolutionTree.edgesLeaves]; exact List.mem_append_right _ hl, f, hf⟩
end

/-- **The geoAtlas-leaf correspondence** (`acc = id` specialization): every `geoAtlas t` piece is
`{ l with chartMap := f }` for an original `t`-leaf `l`. -/
theorem geoAtlas_leaf_update (t : ResolutionTree M) :
    ∀ c ∈ geoAtlas t, ∃ l ∈ ResolutionTree.leaves t, ∃ f : Params M → Params M,
      c = { l with chartMap := f } := by
  rw [geoAtlas]; exact tGeo_leaf_update id t

end DLNFibre.DLN.RLCT.Engine
