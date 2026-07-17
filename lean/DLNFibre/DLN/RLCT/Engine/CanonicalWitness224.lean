import DLNFibre.DLN.RLCT.Engine.EngineObligations

/-!
# `DLNFibre.DLN.RLCT.Engine.CanonicalWitness224` — a concrete `CanonicalResolution` model

**A bank piece (sorry-free), NOT a blueprint forecast.** The `CanonicalResolution` bundle
(`Engine.EngineObligations`) conjoins five properties the engine's obligations project from; this
module exhibits a concrete tree satisfying all five at `M = (2,2,4)` — the joint 5-conjunct
satisfiability check the bundle had never had (navigator lane 1). It proves the conjuncts have a
*model* (no hidden logical/type incompatibility) and serves as the construction tide's base-case
template.

**Why `(2,2,4)`.** It is the smallest *nontrivial* member of the banked `(r,r,4)` family (`r = 2`):
`r = 1` gives the degenerate `1×1` residual, whereas `r = 2` is the first genuine corank-2 stratum —
the coupled case the sharing map exists for. `minAdm (2,2,4) = 4` (banked `minAdm_rr4_eq`, and here by
the `minAdmRec` recursion); its deepest rank profile is `t = (0,0)` with `Mval = 4 = minAdm`.

**Scope / honesty.** This witness makes the ARITHMETIC conjuncts genuine — `divExp = Mval(profile)`
(IsFullMonomialization) and `min terminalExponents = minAdm` (the exponent hooks) must and do
coexist, with `Mval((0,0)) = minAdm = 4` proved by kernel `decide`. The coverage conjunct is
satisfied by the TRIVIAL atlas (`chartDom = univ`): `ChartsCover` as stated is satisfiable by the
whole space, so it does not by itself force blow-up charts — the geometric covering content lives in
the `monomialization_terminates` construction, not in the predicate. (Finding surfaced upstream.)
The deepest-stratum contract holds: nothing here re-proves the non-deepest domination
(`deepest_le_of_homogeneous_core`) or a region integral (Layer-B fence).
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open scoped BigOperators

/-- The width vector `(2,2,4)` — the `r = 2` member of the banked `(r,r,4)` family. -/
abbrev M224 : Fin 3 → ℕ := ![2, 2, 4]

/-- The root blow-up node: a Case-2 step at the base of the invariant (`S = J = 0`), residual `1×1`,
one divisor of exponent `1 = resRows·resCols` dividing the one generator. -/
def rootNode224 : StepData M224 where
  layer := 0; cleared := 0; case := StepCase.case2; resRows := 1; resCols := 1
  numDiv := 1; numB := 1; bExp := fun _ _ => 0; bChain := fun _ _ _ _ => le_refl _
  divExp := fun _ => 1; divTilde := fun _ => 0; numGen := 1; support := fun _ => {0}

/-- The terminal leaf: one divisor of exponent `4 = Mval((0,0)) = minAdm (2,2,4)`, rank profile the
deepest `(0,0)`; a (trivially) chain leaf; trivial chart domain (the whole space). -/
def leaf224 : LeafData M224 where
  numDiv := 1
  divExp := fun _ => 4
  divProfile := fun _ => ![0, 0]
  numB := 1; bExp := fun _ _ => 0; bChain := fun _ _ _ _ => le_refl _
  chartDom := Set.univ

/-- The witness tree: the root blow-up over its single terminal chart. -/
def tree224 : ResolutionTree M224 :=
  ResolutionTree.branch rootNode224 [ResolutionTree.leaf leaf224]

@[simp] theorem leaves_tree224 : ResolutionTree.leaves tree224 = [leaf224] := by
  simp [tree224, ResolutionTree.leaves]

@[simp] theorem nodes_tree224 : ResolutionTree.nodes tree224 = [rootNode224] := by
  simp [tree224, ResolutionTree.nodes]

theorem terminalExponents_tree224 : ResolutionTree.terminalExponents tree224 = [4] := by
  simp [ResolutionTree.terminalExponents, leaves_tree224, leaf224, List.finRange]

/-- `minAdm (2,2,4) = 4`, via the banked layer-peeling recursion (`minAdmRec_eq_minAdm`). -/
theorem minAdm_M224 : minAdm M224 = 4 := by
  rw [← minAdmRec_eq_minAdm]; decide

/-- `rootNode224` satisfies the per-step invariant (its Case-2 clause is real; the Case-1 clauses are
vacuous). -/
theorem rootNode224_stepInvariant : StepInvariant rootNode224 := by
  unfold StepInvariant rootNode224
  refine ⟨fun _ => ⟨0, rfl, fun _ => Finset.mem_singleton_self 0⟩, ?_, ?_⟩
  · intro h; simp at h
  · intro h; simp at h

/-- **The joint satisfiability witness** (navigator lane 1): the `CanonicalResolution` bundle has a
concrete model at `M = (2,2,4)`. Sorry-free — the five conjuncts (full monomialisation with
`divExp = Mval`, per-node invariant, branch-rooted base, neighbourhood coverage, and the
`minAdm = min terminalExponents` exponent hooks) are jointly satisfiable, with the binding arithmetic
`Mval((0,0)) = minAdm = 4` discharged by kernel computation. -/
theorem canonicalResolution_224 : ∃ t : ResolutionTree M224, CanonicalResolution M224 t := by
  refine ⟨tree224, ?_, ?_, ?_, ?_, ?_⟩
  · -- IsFullMonomialization: divExp = Mval(profile) at the single leaf's single divisor
    intro l hl k
    rw [leaves_tree224, List.mem_singleton] at hl
    subst hl
    fin_cases k
    decide
  · -- StepInvariant on every node
    intro n hn
    rw [nodes_tree224, List.mem_singleton] at hn
    subst hn
    exact rootNode224_stepInvariant
  · -- branch-rooted at the base of the invariant
    exact ⟨rootNode224, [ResolutionTree.leaf leaf224], rfl, rfl, rfl⟩
  · -- ChartsCover: the trivial atlas covers (chartDom = univ)
    refine ⟨?_, Set.univ, isOpen_univ, Set.subset_univ _, ?_⟩
    · intro l hl
      rw [leaves_tree224, List.mem_singleton] at hl
      subst hl
      exact isOpen_univ
    · intro A _
      rw [leaves_tree224]
      simp [leaf224]
  · -- exponent hooks: minAdm = min terminalExponents = 4
    rw [terminalExponents_tree224, minAdm_M224]
    refine ⟨?_, ?_⟩
    · intro e he
      rw [List.mem_singleton] at he
      subst he
      exact le_refl 4
    · simp

end DLNFibre.DLN.RLCT.Engine
