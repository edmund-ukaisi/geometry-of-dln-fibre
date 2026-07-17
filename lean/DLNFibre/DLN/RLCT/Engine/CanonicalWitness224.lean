import DLNFibre.DLN.RLCT.Engine.EngineObligations

/-!
# `DLNFibre.DLN.RLCT.Engine.CanonicalWitness224` — the `(2,2,4)` model, split (edge-labelled)

Witness split (precision ruling): `canonicalResolution224_arithmetic` — a clean-three BANK piece
(the
four carrier-independent conjuncts: full monomialisation, edge-relational `StepRel`, branch-rooted
base, exponent hooks); `canonicalResolution224` — a `@[blueprint]` FORECAST whose `ChartBridge`
conjunct is sorried pending the P8 CoV lemma. Plus the in-file MIXED-CASE positive witness. Rebuilt
against the edge-labelled / self-map-chart carrier (route (b)).

`M = (2,2,4)`: `minAdm = 4`, deepest profile `(0,0)` with `Mval = 4`.
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open scoped BigOperators

/-- The width vector `(2,2,4)`. -/
abbrev M224 : Fin 3 → ℕ := ![2, 2, 4]

/-- The root blow-up node (edge-labelled carrier: no `case` field). -/
def rootNode224 : StepData M224 where
  layer := 0; cleared := 0; resRows := 1; resCols := 1
  numDiv := 1; numB := 1; bExp := fun _ _ => 0; bChain := fun _ _ _ _ => le_refl _
  divExp := fun _ => 1; divTilde := fun _ => 0; numGen := 1; support := fun _ => {0}

/-- The terminal leaf: exponent `4 = Mval((0,0)) = minAdm`, deepest profile; placeholder chart data
(the arithmetic conjuncts do not read it; the real chart is the P8 tide's). -/
noncomputable def leaf224 : LeafData M224 where
  numDiv := 1; divExp := fun _ => 4; divProfile := fun _ => ![0, 0]
  numB := 1; bExp := fun _ _ => 0; bChain := fun _ _ _ _ => le_refl _
  chartMap := id; srcBox := Set.univ; resRank := 0
  divCoord := fun _ => ⟨0, by decide⟩; resCoord := Fin.elim0

/-- The chart substitution ledger on the edge (placeholder self-map; `StepRel` reads the parent). -/
def subst224 : ChartSubst M224 where
  localSub := id; jacDivCount := 1; jacPow := fun _ => 3

/-- The witness tree: the root Case-2 blow-up over its single terminal chart (edge-labelled). -/
noncomputable def tree224 : ResolutionTree M224 :=
  ResolutionTree.branch rootNode224 [Edge.mk StepCase.case2 subst224 (ResolutionTree.leaf leaf224)]

@[simp] theorem leaves_tree224 : ResolutionTree.leaves tree224 = [leaf224] := by
  simp [tree224, ResolutionTree.leaves, ResolutionTree.edgesLeaves]

@[simp] theorem stepEdges_tree224 :
    ResolutionTree.stepEdges tree224
      = [(rootNode224, Edge.mk StepCase.case2 subst224 (ResolutionTree.leaf leaf224))] := by
  simp [tree224, ResolutionTree.stepEdges, ResolutionTree.edgesStepEdges]

theorem terminalExponents_tree224 : ResolutionTree.terminalExponents tree224 = [4] := by
  simp [ResolutionTree.terminalExponents, leaves_tree224, leaf224, List.finRange]

/-- `minAdm (2,2,4) = 4`, via the banked layer-peeling recursion. -/
theorem minAdm_M224 : minAdm M224 = 4 := by
  rw [← minAdmRec_eq_minAdm]; decide

/-- The root Case-2 edge satisfies `StepRel` (its case-2 clause is real; case-1 clauses vacuous). -/
theorem rootEdge224_stepRel :
    StepRel rootNode224 (Edge.mk StepCase.case2 subst224 (ResolutionTree.leaf leaf224)) := by
  unfold StepRel rootNode224
  refine ⟨fun _ => ⟨0, rfl, fun _ => Finset.mem_singleton_self 0⟩, ?_, ?_⟩
  · intro h; simp [Edge.case] at h
  · intro h; simp [Edge.case] at h

/-- **The arithmetic bank piece** (clean-three): at `M = (2,2,4)` the FOUR carrier-independent
conjuncts of `CanonicalResolution` are jointly satisfiable — full monomialisation, the
edge-relational
`StepRel` on every parent–edge pair, the branch-rooted base, and the exponent hooks. Survives the
restructure (it never touches the chart/CoV data). -/
theorem canonicalResolution224_arithmetic : ∃ t : ResolutionTree M224,
    IsFullMonomialization t ∧
      (∀ p ∈ ResolutionTree.stepEdges t, StepRel p.1 p.2) ∧
        (∃ (n : StepData M224) (edges : List (Edge M224)),
            t = ResolutionTree.branch n edges ∧ n.layer = 0 ∧ n.cleared = 0) ∧
          ((∀ e ∈ ResolutionTree.terminalExponents t, minAdm M224 ≤ e) ∧
            minAdm M224 ∈ ResolutionTree.terminalExponents t) := by
  refine ⟨tree224, ?_, ?_, ?_, ?_⟩
  · intro l hl k
    rw [leaves_tree224, List.mem_singleton] at hl
    subst hl
    fin_cases k
    decide
  · intro p hp
    rw [stepEdges_tree224, List.mem_singleton] at hp
    subst hp
    exact rootEdge224_stepRel
  · exact ⟨rootNode224, [Edge.mk StepCase.case2 subst224 (ResolutionTree.leaf leaf224)],
      rfl, rfl, rfl⟩
  · rw [terminalExponents_tree224, minAdm_M224]
    refine ⟨?_, ?_⟩
    · intro e he; rw [List.mem_singleton] at he; subst he; exact le_refl 4
    · simp

/-- **The full `CanonicalResolution` witness** at `(2,2,4)` — a `@[blueprint]` FORECAST. The four
arithmetic conjuncts are the bank piece above; the `ChartBridge` conjunct is sorried pending the P8
CoV lemma (the real `(2,2,4)` chart's pullback / Jacobian / coherence). -/
@[blueprint] theorem canonicalResolution224 :
    ∃ t : ResolutionTree M224, CanonicalResolution M224 t := by
  obtain ⟨t, hmono, hstep, hroot, hexp⟩ := canonicalResolution224_arithmetic
  exact ⟨t, hmono, hstep, hroot, by sorry, hexp⟩

/-! ## The in-file mixed-case Case-1 positive witness (fresh-review checklist) -/

/-- A second placeholder substitution (distinct from `subst224`) for the case-1(2) edge. -/
def subst224b : ChartSubst M224 where
  localSub := id; jacDivCount := 1; jacPow := fun _ => 1

/-- **A mixed-case Case-1 blow-up**: one node with TWO edges of distinct case + substitution, which
the edge-labelled carrier records faithfully — the constructive complement of the necessity witness.
-/
noncomputable def mixedCaseTree : ResolutionTree M224 :=
  ResolutionTree.branch rootNode224
    [Edge.mk StepCase.case11 subst224 (ResolutionTree.leaf leaf224),
     Edge.mk StepCase.case12 subst224b (ResolutionTree.leaf leaf224)]

/-- The carrier records BOTH cases of the one blow-up (the edge tags are recoverable). -/
theorem mixedCaseTree_records_both :
    (ResolutionTree.stepEdges mixedCaseTree).map (fun p => p.2.case)
      = [StepCase.case11, StepCase.case12] := by
  simp [mixedCaseTree, ResolutionTree.stepEdges, ResolutionTree.edgesStepEdges, Edge.case]

/-! ## case-contradicts-subst rejection (fresh-review checklist) -/

/-- A node whose ledger does NOT provide a Case-2 divisor: residual `1×1` (so `resRows·resCols = 1`)
but its one divisor has exponent `2 ≠ 1`. -/
def badNode224 : StepData M224 where
  layer := 0; cleared := 0; resRows := 1; resCols := 1
  numDiv := 1; numB := 1; bExp := fun _ _ => 0; bChain := fun _ _ _ _ => le_refl _
  divExp := fun _ => 2; divTilde := fun _ => 0; numGen := 1; support := fun _ => {0}

/-- **case-contradicts-subst rejection**: a Case-2 edge on `badNode224` is REJECTED by `StepRel` —
the
case tag cannot contradict the ledger (the required exponent `resRows·resCols = 1` is not realised
by
any divisor, whose exponent is `2`). So a mislabelled chart cannot slip through the invariant. -/
theorem stepRel_rejects_mismatched_case2 :
    ¬ StepRel badNode224 (Edge.mk StepCase.case2 subst224 (ResolutionTree.leaf leaf224)) := by
  rintro ⟨hc2, _, _⟩
  obtain ⟨k, hk, _⟩ := hc2 rfl
  simp [badNode224] at hk

end DLNFibre.DLN.RLCT.Engine
