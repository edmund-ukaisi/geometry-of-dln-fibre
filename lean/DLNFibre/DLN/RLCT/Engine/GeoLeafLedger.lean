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

/-! ## The transfers — the (B) ledger props + (C) exponents over `geoAtlas` -/

/-- **Every built-tree leaf's source box is the flat unit cube** (mirrors `leaves_srcBox_nonempty`,
`leafOfState_srcBox` at the terminal). -/
theorem leaves_srcBox_flatCube (s : ConState L) :
    ∀ l ∈ ResolutionTree.leaves (buildTree M (conOracle M) s),
      l.srcBox = ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) 1 := by
  induction s using (conRel_wf M).induction with
  | _ s ih =>
    intro l hl
    cases hoc : conOracle M s with
    | terminal l' hleaf =>
        rw [buildTree_terminal M (conOracle M) s l' hleaf hoc] at hl
        simp only [ResolutionTree.leaves, List.mem_singleton] at hl
        subst hl
        rw [conOracle_terminal_leaf s hoc]
        exact leafOfState_srcBox s
    | step node children hnode hlayer hstep =>
        rw [buildTree_step M (conOracle M) s node children hoc] at hl
        rw [ResolutionTree.leaves, edgesLeaves_eq, List.mem_flatMap] at hl
        obtain ⟨e, he, hle⟩ := hl
        rw [List.mem_map] at he
        obtain ⟨c, hc, rfl⟩ := he
        exact ih c.child c.hdesc l hle

/-- A leaf's divisor exponent is a terminal exponent (the `flatMap`-`++` membership). -/
theorem divExp_mem_terminalExponents (t : ResolutionTree M) (l : LeafData M)
    (hl : l ∈ ResolutionTree.leaves t) (k : Fin l.numDiv) :
    l.divExp k ∈ ResolutionTree.terminalExponents t := by
  rw [ResolutionTree.terminalExponents, List.mem_flatMap]
  exact ⟨l, hl, List.mem_append_left _ (List.mem_map_of_mem (List.mem_finRange k))⟩

/-- A leaf's positive residual rank is a terminal exponent (the `flatMap`-`++` `if`-branch). -/
theorem resRank_mem_terminalExponents (t : ResolutionTree M) (l : LeafData M)
    (hl : l ∈ ResolutionTree.leaves t) (hpos : 0 < l.resRank) :
    l.resRank ∈ ResolutionTree.terminalExponents t := by
  rw [ResolutionTree.terminalExponents, List.mem_flatMap]
  exact ⟨l, hl, List.mem_append_right _ (by rw [if_pos hpos]; exact List.mem_singleton.mpr rfl)⟩

/-- **The (B) ledger props + (C) exponents transfer** to every `geoAtlas` piece via the
correspondence: srcBox measurable+bounded (`flatCubeSrcBox_*`, the box is the flat cube),
divCoord/resCoord inj+disjoint (`leaves_chart_clauses_conRoot`), and the exponents
(`divExp`/`resRank` membership). The geometric props (a.e.-inj, `LeafPullback`, `LeafJacobian`)
are elsewhere. -/
theorem geoAtlas_leaf_ledgerProps (c : LeafData M)
    (hc : c ∈ geoAtlas (buildTree M (conOracle M) (conRoot : ConState L))) :
    MeasurableSet c.srcBox ∧
      (∃ R : ℝ, 0 < R ∧ c.srcBox ⊆ ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) R) ∧
      Function.Injective c.divCoord ∧ Function.Injective c.resCoord ∧
      Disjoint (Set.range c.divCoord) (Set.range c.resCoord) ∧
      (∀ k : Fin c.numDiv,
          c.divExp k ∈ ResolutionTree.terminalExponents (buildTree M (conOracle M) conRoot)) ∧
      (0 < c.resRank →
          c.resRank ∈ ResolutionTree.terminalExponents (buildTree M (conOracle M) conRoot)) := by
  obtain ⟨l, hl, f, hf⟩ := geoAtlas_leaf_update _ c hc
  obtain ⟨hdiv, hres, hdisj⟩ := leaves_chart_clauses_conRoot l hl
  have hsrc : l.srcBox = ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) 1 :=
    leaves_srcBox_flatCube conRoot l hl
  subst hf
  refine ⟨?_, ⟨1, one_pos, ?_⟩, hdiv, hres, hdisj, ?_, ?_⟩
  · show MeasurableSet l.srcBox; rw [hsrc]; exact flatCubeSrcBox_measurableSet 1
  · show l.srcBox ⊆ _; rw [hsrc]
  · exact fun k => divExp_mem_terminalExponents _ l hl k
  · exact fun hpos => resRank_mem_terminalExponents _ l hl hpos

end DLNFibre.DLN.RLCT.Engine
