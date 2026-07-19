import DLNFibre.DLN.RLCT.Engine.QNodeCarrier

/-!
# `DLNFibre.DLN.RLCT.Engine.NodesCNodeWalk` — clause (D) node-walk (STAGED, R-split-invariant)

The conjunct-2 fidelity of clause (D): every internal node of the built tree has
`cNodeOf = realCNode` — the per-node center split blows up the INTENDED (ledger-born) coordinates,
never the injectivity fallback. Proven by well-founded induction over `ConState` (mirroring
`DivBirthReach.leaves_chart_clauses`), threading `DivBirthInv` down the tree and consuming the
per-node atom `QNodeCarrier.cNodeOf_eq_realCNode_of_conOracle` at each step-node.

This walk is R-split-invariant (it is conjunct 2 of clause (D) under every design variant, and reads
only `QNodeCarrier` + `DivBirthReach` — no `GeoChart`), so it is drafted here ahead of the statement
gate; its final home moves with the ratified (D) module placement.
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT

variable {L : ℕ} {M : Fin (L + 1) → ℕ}

/-- `edgesNodes` of an edge list is the `flatMap` of the per-edge child `nodes` (the node analog of
`edgesLeaves_eq`). -/
theorem edgesNodes_eq (es : List (Edge M)) :
    ResolutionTree.edgesNodes es = es.flatMap (fun e => ResolutionTree.nodes e.child) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      cases e with
      | mk c σ ch => rw [ResolutionTree.edgesNodes, ih, List.flatMap_cons]; rfl

/-- **Clause (D) node-walk**: every internal node of the built tree from `s` has
`cNodeOf = realCNode` (blows up the intended blow-up coordinates), by WF-induction threading
`DivBirthInv`, consuming the per-node atom `cNodeOf_eq_realCNode_of_conOracle`. -/
theorem nodes_cNode_eq_realCNode (s : ConState L) (inv : DivBirthInv M s) :
    ∀ n ∈ ResolutionTree.nodes (buildTree M (conOracle M) s),
      ∀ hd : dCenterOfNode M n ≤ flatDim M, cNodeOf M n hd = realCNode M n hd := by
  induction s using (conRel_wf M).induction with
  | _ s ih =>
    intro n hn hd
    cases hoc : conOracle M s with
    | terminal l' hleaf =>
        rw [buildTree_terminal M (conOracle M) s l' hleaf hoc] at hn
        simp [ResolutionTree.nodes] at hn
    | step node children hnode hlayer hstep =>
        rw [buildTree_step M (conOracle M) s node children hoc,
            ResolutionTree.nodes, edgesNodes_eq, List.mem_cons, List.mem_flatMap] at hn
        rcases hn with rfl | ⟨e, he, hne⟩
        · exact cNodeOf_eq_realCNode_of_conOracle s inv n _
            (buildTree_step M (conOracle M) s n children hoc) hd
        · rw [List.mem_map] at he
          obtain ⟨c, hc, rfl⟩ := he
          have hcstep : c ∈ (conOracle M s).stepChildren := by rw [hoc]; exact hc
          exact ih c.child c.hdesc (DivBirthInv_conOracle_stepChildren s inv c hcstep) n hne hd

end DLNFibre.DLN.RLCT.Engine
