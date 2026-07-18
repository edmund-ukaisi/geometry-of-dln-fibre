import DLNFibre.DLN.RLCT.Engine.EngineObligations

/-!
# `DLNFibre.DLN.RLCT.Engine.CanonicalWitness224` — the `(2,2,4)` model, split

Witness split (precision ruling): `canonicalResolution224_arithmetic` — a clean-three BANK piece
(the carrier-independent conjuncts: full monomialisation with `divProfile ∈ Adm`, the child-reading
`StepRel`, the branch-rooted base, the exponent hooks, and the LIVE attainment);
`canonicalResolution224` — a `@[blueprint]` FORECAST whose `ChartBridge` conjunct is sorried pending
the P8 CoV lemma.

REAL root step (ruling 4): a genuine Case-2 blow-up with a `2×2` residual (`resRows = resCols = 2`,
so codim `= 4 = minAdm(2,2,4)`), whose CHILD leaf carries the exponent-`4` divisor — certifying the
STRENGTHENED `StepRel` (which reads the child). Plus a Case-1(1) child-merge witness
(`M' = M + J₁·resCols`, `5 + 2·3 = 11`; worked.tex:505–507) — kills the old childless `StepRel`.
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open scoped BigOperators

/-- The width vector `(2,2,4)`. -/
abbrev M224 : Fin 3 → ℕ := ![2, 2, 4]

/-- The REAL root blow-up node: a Case-2 step with a `2×2` residual (codim `4 = minAdm(2,2,4)`). -/
def rootNode224 : StepData M224 where
  layer := 0; cleared := 0; resRows := 2; resCols := 2
  numDiv := 1; numB := 1; bExp := fun _ _ => 0; bChain := fun _ _ _ _ => le_refl _
  divExp := fun _ => 4; divTilde := fun _ => 0; numGen := 1; support := fun _ => {0}

/-- The terminal leaf: the CHILD divisor of exponent `4 = resRows·resCols = Mval((0,0)) = minAdm`,
deepest ADMISSIBLE profile `(0,0)`; placeholder chart data (the arithmetic conjuncts do not read
it). -/
noncomputable def leaf224 : LeafData M224 where
  numDiv := 1; divExp := fun _ => 4; divProfile := fun _ => ![0, 0]
  numB := 1; bExp := fun _ _ => 0; bChain := fun _ _ _ _ => le_refl _
  chartMap := id; srcBox := Set.univ; resRank := 0
  divCoord := fun _ => ⟨0, by decide⟩; resCoord := Fin.elim0

/-- The Case-2 edge substitution ledger (placeholder self-map; `runLen` unused by case-2). -/
def subst224 : ChartSubst M224 where
  localSub := id; runLen := 0; jacDivCount := 1; jacPow := fun _ => 3

/-- The witness tree: the real Case-2 root over its single terminal chart. -/
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

/-- The real Case-2 root edge satisfies the STRENGTHENED `StepRel` — parent sharing + the CHILD's
new divisor at exponent `resRows·resCols = 4`. -/
theorem rootEdge224_stepRel :
    StepRel rootNode224 (Edge.mk StepCase.case2 subst224 (ResolutionTree.leaf leaf224)) := by
  unfold StepRel rootNode224
  refine ⟨fun _ => ⟨⟨0, fun _ => Finset.mem_singleton_self 0⟩, ⟨0, ?_, ?_⟩⟩,
    fun h => by simp [Edge.case] at h, fun h => by simp [Edge.case] at h⟩
  · simp [Edge.child, ResolutionTree.rootNumDiv, leaf224]
  · simp [Edge.child, ResolutionTree.rootDivExp, leaf224]

/-- **The arithmetic bank piece** (clean-three): at `M = (2,2,4)` the carrier-independent conjuncts
are jointly satisfiable — full monomialisation (`divExp = Mval`, `divProfile ∈ Adm`), the
child-reading `StepRel`, the branch-rooted base, the exponent hooks, and the live attainment.
Survives the restructure. -/
theorem canonicalResolution224_arithmetic : ∃ t : ResolutionTree M224,
    IsFullMonomialization t ∧
      (∀ p ∈ ResolutionTree.stepEdges t, StepRel p.1 p.2) ∧
        (∃ (n : StepData M224) (edges : List (Edge M224)),
            t = ResolutionTree.branch n edges ∧ n.layer = 0 ∧ n.cleared = 0) ∧
          ((∀ e ∈ ResolutionTree.terminalExponents t, minAdm M224 ≤ e) ∧
            minAdm M224 ∈ ResolutionTree.terminalExponents t) ∧
          (∃ l ∈ ResolutionTree.leaves t, l.srcBox.Nonempty ∧
            minAdm M224 ∈ (List.finRange l.numDiv).map l.divExp) := by
  refine ⟨tree224, ?_, ?_, ?_, ?_, ?_⟩
  · intro l hl k
    rw [leaves_tree224, List.mem_singleton] at hl
    subst hl
    fin_cases k
    exact ⟨by decide, by decide⟩
  · intro p hp
    rw [stepEdges_tree224, List.mem_singleton] at hp
    subst hp
    exact rootEdge224_stepRel
  · exact ⟨rootNode224, [Edge.mk StepCase.case2 subst224 (ResolutionTree.leaf leaf224)],
      rfl, rfl, rfl⟩
  · rw [terminalExponents_tree224, minAdm_M224]
    exact ⟨fun e he => by rw [List.mem_singleton] at he; subst he; exact le_refl 4, by simp⟩
  · refine ⟨leaf224, ?_, ?_, ?_⟩
    · rw [leaves_tree224]; exact List.mem_singleton_self _
    · exact ⟨0, trivial⟩
    · rw [minAdm_M224]; simp [leaf224, List.finRange]

/-- **The full `CanonicalResolution` witness** at `(2,2,4)` — a `@[blueprint]` FORECAST. The
carrier-independent conjuncts are the bank piece above; the `ChartBridge` conjunct is sorried
pending the P8 CoV lemma. -/
@[blueprint] theorem canonicalResolution224 :
    ∃ t : ResolutionTree M224, CanonicalResolution M224 t := by
  obtain ⟨t, hmono, hstep, hroot, hexp, hlive⟩ := canonicalResolution224_arithmetic
  exact ⟨t, hmono, hstep, hroot, by sorry, hexp, hlive⟩

/-! ## Case-1(1) child-merge witness (ruling 4 — kills the old childless `StepRel`) -/

/-- A Case-1(1) parent: one divisor `divExp 0 = 5` at clearing level `0`, residual width
`resCols = 3`. -/
def mergeNode : StepData M224 where
  layer := 0; cleared := 0; resRows := 1; resCols := 3
  numDiv := 1; numB := 1; bExp := fun _ _ => 0; bChain := fun _ _ _ _ => le_refl _
  divExp := fun _ => 5; divTilde := fun _ => 0; numGen := 1; support := fun _ => {0}

/-- The merged child leaf: exponent `11 = 5 + 2·3 = parent divExp + J₁·resCols`. -/
noncomputable def mergeLeaf : LeafData M224 where
  numDiv := 1; divExp := fun _ => 11; divProfile := fun _ => ![0, 0]
  numB := 1; bExp := fun _ _ => 0; bChain := fun _ _ _ _ => le_refl _
  chartMap := id; srcBox := Set.univ; resRank := 0
  divCoord := fun _ => ⟨0, by decide⟩; resCoord := Fin.elim0

/-- The Case-1(1) edge: `runLen = J₁ = 2`. -/
def mergeSubst : ChartSubst M224 where
  localSub := id; runLen := 2; jacDivCount := 1; jacPow := fun _ => 0

/-- **Case-1(1) child-merge witness** (worked.tex:505–507; `M' = M + J₁·(M^{(S+1)}−J)`, numerically
`5 + 2·3 = 11`): the merged child exponent equals `parent divExp + runLen·resCols`, so a Case-1(1)
edge satisfies the STRENGTHENED `StepRel`. The OLD childless clause could not see this. -/
theorem mergeEdge_stepRel :
    StepRel mergeNode (Edge.mk StepCase.case11 mergeSubst (ResolutionTree.leaf mergeLeaf)) := by
  unfold StepRel mergeNode
  refine ⟨fun h => by simp [Edge.case] at h, fun _ => ⟨0, rfl, ⟨0, ?_, ?_⟩⟩,
    fun h => by simp [Edge.case] at h⟩
  · simp [Edge.child, ResolutionTree.rootNumDiv, mergeLeaf]
  · simp [Edge.child, Edge.subst, ResolutionTree.rootDivExp, mergeLeaf, mergeSubst]

/-! ## The in-file mixed-case Case-1 positive witness + rejection (fresh-review checklist) -/

/-- A second placeholder substitution (distinct from `subst224`) for the case-1(2) edge. -/
def subst224b : ChartSubst M224 where
  localSub := id; runLen := 1; jacDivCount := 1; jacPow := fun _ => 1

/-- **A mixed-case Case-1 blow-up**: one node with TWO edges of distinct case + substitution, which
the edge-labelled carrier records faithfully. -/
noncomputable def mixedCaseTree : ResolutionTree M224 :=
  ResolutionTree.branch rootNode224
    [Edge.mk StepCase.case11 subst224 (ResolutionTree.leaf leaf224),
     Edge.mk StepCase.case12 subst224b (ResolutionTree.leaf leaf224)]

/-- The carrier records BOTH cases of the one blow-up (the edge tags are recoverable). -/
theorem mixedCaseTree_records_both :
    (ResolutionTree.stepEdges mixedCaseTree).map (fun p => p.2.case)
      = [StepCase.case11, StepCase.case12] := by
  simp [mixedCaseTree, ResolutionTree.stepEdges, ResolutionTree.edgesStepEdges, Edge.case]

/-- A node whose CHILD does NOT carry the Case-2 codim exponent: `resRows·resCols = 4` but the child
leaf's divisor exponent is `2 ≠ 4`. -/
noncomputable def badLeaf : LeafData M224 where
  numDiv := 1; divExp := fun _ => 2; divProfile := fun _ => ![0, 0]
  numB := 1; bExp := fun _ _ => 0; bChain := fun _ _ _ _ => le_refl _
  chartMap := id; srcBox := Set.univ; resRank := 0
  divCoord := fun _ => ⟨0, by decide⟩; resCoord := Fin.elim0

/-- **case-contradicts-child rejection**: a Case-2 edge whose CHILD lacks the codim exponent
(`resRows·resCols = 4`, child exponent `2`) is REJECTED by the STRENGTHENED `StepRel` — the case tag
cannot contradict the emitted child. (Now reads the child, unlike the old childless form.) -/
theorem stepRel_rejects_mismatched_case2 :
    ¬ StepRel rootNode224 (Edge.mk StepCase.case2 subst224 (ResolutionTree.leaf badLeaf)) := by
  rintro ⟨hc2, _, _⟩
  obtain ⟨_, ⟨kc, hlt, hexp⟩⟩ := hc2 rfl
  simp only [Edge.child, ResolutionTree.rootNumDiv, badLeaf] at hlt
  interval_cases kc <;>
    simp [Edge.child, ResolutionTree.rootDivExp, badLeaf, rootNode224] at hexp

end DLNFibre.DLN.RLCT.Engine
