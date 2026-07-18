import DLNFibre.DLN.RLCT.Engine.EngineDefs

/-!
# `DLNFibre.DLN.RLCT.Engine.CanonicalWitness224` — the `(2,2,4)` model (faithful `stepUpdate`)

Witness split (precision ruling): `canonicalResolution224_arithmetic` — a clean-three BANK piece
(the carrier-independent conjuncts: full monomialisation with `divProfile ∈ Adm`, the FAITHFUL
`StepRel` (`rootLedger child = stepUpdate parent`), the branch-rooted base, the exponent hooks, and
the LIVE attainment); `canonicalResolution224` — a `@[blueprint]` FORECAST whose `ChartBridge`
conjunct is sorried pending the P8 CoV lemma.

RUNG-1 truth-signal: each child leaf's ledger fields are DEFINITIONALLY the projections of
`stepUpdate parent`, so the faithful `StepRel` discharges by structure-eta `rfl` — exactly fork 9's
"the construction computes child ledgers definitionally". The root is the BASE node (`numDiv = 0`);
its case-2 edge appends the one shared divisor of exponent `resRows·resCols = 4 = minAdm(2,2,4)`.

Kill-conditions (dummy-divisor rejection): a child with an EXTRA or MISSING divisor changes
`rootLedger.numDiv` and is provably rejected (`dummyDivisor_not_stepRel` / `vanishingDivisor_...`).
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open scoped BigOperators

/-- The width vector `(2,2,4)`. -/
abbrev M224 : Fin 3 → ℕ := ![2, 2, 4]

/-- The BASE root node (`S = J = 0`, no exceptional divisors yet): its case-2 edge blows up the full
`2×2` residual. -/
def rootNode224 : StepData M224 where
  layer := 0; cleared := 0; resRows := 2; resCols := 2
  numDiv := 0; numB := 1; bExp := fun _ _ => 0; bChain := fun _ _ _ _ => le_refl _
  divExp := fun k => k.elim0; divProfile := fun k => k.elim0
  numGen := 0; genDivExp := fun k => k.elim0

/-- The Case-2 edge substitution (placeholder self-map; `mergeIdx` unused by case-2). -/
def subst224 : ChartSubst M224 where
  localSub := id; runLen := 0; mergeIdx := 0; jacDivCount := 1; jacPow := fun _ => 3

/-- The terminal leaf: its LEDGER is DEFINITIONALLY `stepUpdate rootNode224 case2 subst224` — so the
faithful `StepRel` is rfl. The one appended shared divisor has exponent
`4 = resRows·resCols = minAdm`, deepest ADMISSIBLE profile `(0,0)`. -/
noncomputable def leaf224 : LeafData M224 where
  numDiv := (stepUpdate rootNode224 StepCase.case2 subst224).numDiv
  divExp := (stepUpdate rootNode224 StepCase.case2 subst224).divExp
  cleared := (stepUpdate rootNode224 StepCase.case2 subst224).cleared
  divProfile := (stepUpdate rootNode224 StepCase.case2 subst224).divProfile
  -- full ledger = analytic here (the single divisor is t̃=0)
  fullNumDiv := (stepUpdate rootNode224 StepCase.case2 subst224).numDiv
  fullDivExp := (stepUpdate rootNode224 StepCase.case2 subst224).divExp
  fullDivProfile := (stepUpdate rootNode224 StepCase.case2 subst224).divProfile
  numB := 1; bExp := fun _ _ => 0; bChain := fun _ _ _ _ => le_refl _
  chartMap := id
  srcBox := ⇑(paramsEquivFlat M224) ⁻¹' cubeBox (flatDim M224) 1
  resRank := 0
  divCoord := fun _ => ⟨0, by decide⟩; resCoord := Fin.elim0

/-- The witness tree: the real Case-2 root over its single terminal chart. -/
noncomputable def tree224 : ResolutionTree M224 :=
  ResolutionTree.branch rootNode224 [Edge.mk StepCase.case2 subst224 (ResolutionTree.leaf leaf224)]

@[simp] theorem leaves_tree224 : ResolutionTree.leaves tree224 = [leaf224] := by
  simp [tree224, ResolutionTree.leaves, ResolutionTree.edgesLeaves]

@[simp] theorem stepEdges_tree224 :
    ResolutionTree.stepEdges tree224
      = [(rootNode224, Edge.mk StepCase.case2 subst224 (ResolutionTree.leaf leaf224))] := by
  simp [tree224, ResolutionTree.stepEdges, ResolutionTree.edgesStepEdges]

/-- `leaf224.numDiv = 1` (the base root's case-2 appends exactly one divisor). -/
@[simp] theorem numDiv_leaf224 : leaf224.numDiv = 1 := rfl

/-- `leaf224`'s single divisor has exponent `4` (`= resRows·resCols`). -/
@[simp] theorem divExp_leaf224 (k : Fin leaf224.numDiv) : leaf224.divExp k = 4 := by
  fin_cases k; decide

theorem terminalExponents_tree224 : ResolutionTree.terminalExponents tree224 = [4] := by
  rw [ResolutionTree.terminalExponents, leaves_tree224]; decide

/-- `minAdm (2,2,4) = 4`, via the banked layer-peeling recursion. -/
theorem minAdm_M224 : minAdm M224 = 4 := by
  rw [← minAdmRec_eq_minAdm]; decide

/-- **The FAITHFUL case-2 root edge**: the child leaf's ledger IS `stepUpdate rootNode224 case2
subst224` by construction (ledger equality by structure-eta `rfl`); the case-1 eligibility clause is
vacuous (the edge is case-2, neither case-1(1) nor case-1(2)). -/
theorem rootEdge224_stepRel :
    StepRel rootNode224 (Edge.mk StepCase.case2 subst224 (ResolutionTree.leaf leaf224)) :=
  ⟨rfl, fun h => by rcases h with h | h <;> simp [Edge.case] at h,
    fun h => by simp [Edge.case] at h⟩

/-- **The arithmetic bank piece** (clean-three): at `M = (2,2,4)` the carrier-independent conjuncts
are jointly satisfiable — full monomialisation (`divExp = Mval`, `divProfile ∈ Adm`), the FAITHFUL
`StepRel`, the branch-rooted base, the exponent hooks, and the live attainment. -/
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
  · intro l hl
    rw [leaves_tree224, List.mem_singleton] at hl
    subst hl
    -- analytic = full here (single t̃=0 divisor): the coherence matches are the identity.
    refine ⟨fun k => ?_, fun k => ⟨k, rfl, rfl, ?_⟩, fun j _ => ⟨j, rfl, rfl⟩⟩
    · rw [divExp_leaf224]; exact ⟨by fin_cases k; decide, by fin_cases k; decide⟩
    · fin_cases k; decide
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
    · refine Set.Nonempty.preimage ⟨fun _ => 0, ?_⟩ (paramsEquivFlat M224).surjective
      simp only [cubeBox, Set.pi_univ_Icc, Set.mem_Icc]
      refine ⟨fun i => ?_, fun i => ?_⟩ <;> norm_num
    · rw [minAdm_M224]
      exact List.mem_map.mpr ⟨⟨0, by decide⟩, List.mem_finRange _, divExp_leaf224 _⟩

/-- **The full `CanonicalResolution` witness** at `(2,2,4)` — a `@[blueprint]` FORECAST. The
carrier-independent conjuncts are the bank piece above; the `ChartBridge` conjunct is sorried
pending the P8 CoV lemma. -/
@[blueprint] theorem canonicalResolution224 :
    ∃ t : ResolutionTree M224, CanonicalResolution M224 t := by
  obtain ⟨t, hmono, hstep, hroot, hexp, hlive⟩ := canonicalResolution224_arithmetic
  exact ⟨t, hmono, hstep, hroot, by sorry, hexp, hlive⟩

/-! ## Case-1(1) child-merge witness (faithful; kills the old childless `StepRel`) -/

/-- A Case-1(1) parent: one divisor `divExp 0 = 5` at clearing level `t̃ = J + J₁ = 2` (the p.15
eligibility precondition for merging with `runLen = J₁ = 2` at `cleared = J = 0`), residual width
`resCols = 3`. -/
def mergeNode : StepData M224 where
  layer := 0; cleared := 0; resRows := 1; resCols := 3
  numDiv := 1; numB := 1; bExp := fun _ _ => 0; bChain := fun _ _ _ _ => le_refl _
  divExp := fun _ => 5; divProfile := fun _ => ![2, 2]; numGen := 1; genDivExp := fun _ _ => 1

/-- The Case-1(1) edge: `runLen = J₁ = 2`, merging INTO divisor `mergeIdx = 0`. -/
def mergeSubst : ChartSubst M224 where
  localSub := id; runLen := 2; mergeIdx := 0; jacDivCount := 1; jacPow := fun _ => 0

/-- The merged child leaf: its ledger IS `stepUpdate mergeNode case11 mergeSubst`; divisor `0`'s
exponent becomes `11 = 5 + 2·3 = parent divExp + runLen·resCols` (preprint p.16
`M' = M + J₁·(M^{(S+1)}−J)`). -/
noncomputable def mergeLeaf : LeafData M224 where
  numDiv := (stepUpdate mergeNode StepCase.case11 mergeSubst).numDiv
  divExp := (stepUpdate mergeNode StepCase.case11 mergeSubst).divExp
  cleared := (stepUpdate mergeNode StepCase.case11 mergeSubst).cleared
  divProfile := (stepUpdate mergeNode StepCase.case11 mergeSubst).divProfile
  fullNumDiv := (stepUpdate mergeNode StepCase.case11 mergeSubst).numDiv
  fullDivExp := (stepUpdate mergeNode StepCase.case11 mergeSubst).divExp
  fullDivProfile := (stepUpdate mergeNode StepCase.case11 mergeSubst).divProfile
  numB := 1; bExp := fun _ _ => 0; bChain := fun _ _ _ _ => le_refl _
  chartMap := id; srcBox := Set.univ; resRank := 0
  divCoord := fun _ => ⟨0, by decide⟩; resCoord := Fin.elim0

/-- **Case-1(1) child-merge witness** (faithful; `5 + 2·3 = 11`): the child leaf's ledger IS
`stepUpdate mergeNode case11 mergeSubst` (ledger equality by structure-eta `rfl`), and the merge
target is ELIGIBLE — `mergeIdx = 0 < 1` with `t̃ 0 = 2 = cleared + runLen` (p.15). -/
theorem mergeEdge_stepRel :
    StepRel mergeNode (Edge.mk StepCase.case11 mergeSubst (ResolutionTree.leaf mergeLeaf)) :=
  ⟨rfl, fun _ => ⟨by decide, by decide⟩, fun h => by simp [Edge.case] at h⟩

/-- The merged child's divisor exponent is `11` (numeric pin of the page-image merge equation). -/
theorem mergeLeaf_divExp : mergeLeaf.divExp ⟨0, by decide⟩ = 11 := by decide

/-! ## Out-of-range case-1(2) rejection (the rider's kill-condition) -/

/-- An OUT-OF-RANGE case-1(2) substitution on `mergeNode`: `mergeIdx = 1 ≥ numDiv = 1`. `stepUpdate`
case12 reads `divExp(mergeIdx)` as the new pivot's base exponent, but the `dite` defaults to `0`
when out of range — silently dropping the parent divisor's exponent. -/
def oobSplitSubst : ChartSubst M224 where
  localSub := id; runLen := 2; mergeIdx := 1; jacDivCount := 1; jacPow := fun _ => 0

/-- The out-of-range split child: its ledger IS `stepUpdate mergeNode case12 oobSplitSubst`, so the
ledger conjunct holds; the appended pivot exponent is `6 = 0 + 2·3` (base DROPPED), not the faithful
`11 = 5 + 2·3`. -/
noncomputable def oobSplitLeaf : LeafData M224 where
  numDiv := (stepUpdate mergeNode StepCase.case12 oobSplitSubst).numDiv
  divExp := (stepUpdate mergeNode StepCase.case12 oobSplitSubst).divExp
  cleared := (stepUpdate mergeNode StepCase.case12 oobSplitSubst).cleared
  divProfile := (stepUpdate mergeNode StepCase.case12 oobSplitSubst).divProfile
  fullNumDiv := (stepUpdate mergeNode StepCase.case12 oobSplitSubst).numDiv
  fullDivExp := (stepUpdate mergeNode StepCase.case12 oobSplitSubst).divExp
  fullDivProfile := (stepUpdate mergeNode StepCase.case12 oobSplitSubst).divProfile
  numB := 1; bExp := fun _ _ => 0; bChain := fun _ _ _ _ => le_refl _
  chartMap := id; srcBox := Set.univ; resRank := 0
  divCoord := fun _ => ⟨0, by decide⟩; resCoord := Fin.elim0

/-- The out-of-range split's appended pivot exponent is `6 = 0 + 2·3` — the base `divExp 0 = 5`
DROPPED by the `dite` default, vs the faithful `11`. This is the corruption the extended guard
rejects. -/
theorem oobSplitLeaf_divExp : oobSplitLeaf.divExp ⟨1, by decide⟩ = 6 := by decide

/-- **Out-of-range case-1(2) rejection** (the rider's kill-condition): a case-1(2) edge whose
`mergeIdx` is out of range is REJECTED by the extended eligibility guard — even though the ledger
conjunct holds (the child IS `stepUpdate`), the guard needs `mergeIdx < numDiv` and `1 < 1` is
false. WITHOUT the case12 extension `StepRel` ACCEPTED it (base silently `6`, not `11`). -/
theorem oobSplit_not_stepRel :
    ¬ StepRel mergeNode
      (Edge.mk StepCase.case12 oobSplitSubst (ResolutionTree.leaf oobSplitLeaf)) := by
  intro h
  obtain ⟨hlt, _⟩ := h.2.1 (Or.inr rfl)
  exact absurd hlt (by decide)

/-! ## Dummy-divisor rejection (the rung-1 kill-condition, both directions) -/

/-- A child with an EXTRA divisor (`numDiv = 2`) not produced by the case-1(1) transition (which
preserves `numDiv = 1`). -/
noncomputable def dummyMergeLeaf : LeafData M224 where
  numDiv := 2; divExp := fun _ => 11; cleared := 0
  divProfile := fun _ => ![0, 0]
  fullNumDiv := 2; fullDivExp := fun _ => 11; fullDivProfile := fun _ => ![0, 0]
  numB := 1; bExp := fun _ _ => 0; bChain := fun _ _ _ _ => le_refl _
  chartMap := id; srcBox := Set.univ; resRank := 0
  divCoord := fun _ => ⟨0, by decide⟩; resCoord := Fin.elim0

/-- **Dummy-divisor rejection (appearing)**: a case-1(1) edge whose child has an EXTRA divisor is
REJECTED — `rootLedger.numDiv` (`2`) ≠ `stepUpdate.numDiv` (`1`). The faithful `StepRel` sees the
divisor the old existential form could not. -/
theorem dummyDivisor_not_stepRel :
    ¬ StepRel mergeNode
      (Edge.mk StepCase.case11 mergeSubst (ResolutionTree.leaf dummyMergeLeaf)) := by
  unfold StepRel
  intro h
  have hn : (2 : ℕ) = 1 := congrArg ResolutionTree.RootLedger.numDiv h.1
  exact absurd hn (by decide)

/-- A child MISSING the appended divisor (`numDiv = 0`) where case-2 must append one
(`numDiv = 1`). -/
noncomputable def vanishingLeaf : LeafData M224 where
  numDiv := 0; divExp := fun k => k.elim0; cleared := 0
  divProfile := fun k => k.elim0
  fullNumDiv := 0; fullDivExp := fun k => k.elim0; fullDivProfile := fun k => k.elim0
  numB := 1; bExp := fun _ _ => 0; bChain := fun _ _ _ _ => le_refl _
  chartMap := id; srcBox := Set.univ; resRank := 0
  divCoord := fun k => k.elim0; resCoord := Fin.elim0

/-- **Dummy-divisor rejection (vanishing)**: a case-2 edge whose child DROPS the appended divisor is
REJECTED — `rootLedger.numDiv` (`0`) ≠ `stepUpdate.numDiv` (`1`). -/
theorem vanishingDivisor_not_stepRel :
    ¬ StepRel rootNode224
      (Edge.mk StepCase.case2 subst224 (ResolutionTree.leaf vanishingLeaf)) := by
  unfold StepRel
  intro h
  have hn : (0 : ℕ) = 1 := congrArg ResolutionTree.RootLedger.numDiv h.1
  exact absurd hn (by decide)

/-! ## Early-rollover rejection (elder-gate6 at-exhaustion guard kill-witness) -/

/-- A rollover substitution (chartless — `localSub = id`, no merge/gap data). -/
def rolloverSubst : ChartSubst M224 where
  localSub := id; runLen := 0; mergeIdx := 0; jacDivCount := 0; jacPow := Fin.elim0

/-- The rollover child of the base root: its ledger IS `stepUpdate rootNode224 rollover`
(divisors unchanged, `cleared := 0`) — so the LEDGER conjunct holds. But the rollover is EARLY: at
`rootNode224` the layer is unexhausted (`cleared = 0 < widthMinUpto M224 1 = 2`). -/
noncomputable def earlyRolloverLeaf : LeafData M224 where
  numDiv := 0; divExp := Fin.elim0; cleared := 0; divProfile := Fin.elim0
  fullNumDiv := 0; fullDivExp := Fin.elim0; fullDivProfile := Fin.elim0
  numB := 1; bExp := fun _ _ => 0; bChain := fun _ _ _ _ => le_refl _
  chartMap := id; srcBox := Set.univ; resRank := 0
  divCoord := Fin.elim0; resCoord := Fin.elim0

/-- **Early-rollover rejection** (the at-exhaustion guard's kill-condition): a `rollover` edge from
the UNEXHAUSTED base root is REJECTED — even though the ledger conjunct holds (the child IS
`stepUpdate rootNode224 rollover`), the guard needs `widthMinUpto M224 1 ≤ cleared` and `2 ≤ 0` is
false. WITHOUT the guard `StepRel` would ACCEPT this early rollover, stranding the layer's pending
pivots into a ledger-consistent non-Aoyagi tree (compass 13(Q3); the fork-9 infidelity class). -/
theorem earlyRollover_not_stepRel :
    ¬ StepRel rootNode224
      (Edge.mk StepCase.rollover rolloverSubst (ResolutionTree.leaf earlyRolloverLeaf)) := by
  intro h
  exact absurd (h.2.2 rfl) (by decide)

/-! ## The in-file mixed-case Case-1 record (carrier records both cases of one blow-up) -/

/-- A second substitution (distinct from `subst224`) for the case-1(2) edge. -/
def subst224b : ChartSubst M224 where
  localSub := id; runLen := 1; mergeIdx := 0; jacDivCount := 1; jacPow := fun _ => 1

/-- **A mixed-case Case-1 blow-up**: one node with TWO edges of distinct case + substitution, which
the edge-labelled carrier records faithfully (a carrier-shape witness; not a `StepRel` witness). -/
noncomputable def mixedCaseTree : ResolutionTree M224 :=
  ResolutionTree.branch rootNode224
    [Edge.mk StepCase.case11 subst224 (ResolutionTree.leaf leaf224),
     Edge.mk StepCase.case12 subst224b (ResolutionTree.leaf leaf224)]

/-- The carrier records BOTH cases of the one blow-up (the edge tags are recoverable). -/
theorem mixedCaseTree_records_both :
    (ResolutionTree.stepEdges mixedCaseTree).map (fun p => p.2.case)
      = [StepCase.case11, StepCase.case12] := by
  simp [mixedCaseTree, ResolutionTree.stepEdges, ResolutionTree.edgesStepEdges, Edge.case]

end DLNFibre.DLN.RLCT.Engine
