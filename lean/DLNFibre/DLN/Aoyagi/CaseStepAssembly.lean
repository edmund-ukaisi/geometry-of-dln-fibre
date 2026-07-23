import DLNFibre.DLN.Aoyagi.MultiAffineStepWire

/-!
# CaseStepAssembly — route the case-preservation step through the PROVED step twin

`Case1Wire.case1_preserves_stepInv'` / `Case2Wire.case2_preserves_stepInv'` discharge conjunct B (the
child `Deg1SupportedSlot` descent) through the UNPRIMED `MonumentAtlas.realBranch_multiAffine_step`
(a `sorry`), because they live UPSTREAM of the proved twin `MultiAffineStepWire.realBranch_multiAffine_step'`
(`MultiAffineStepWire` imports `Case1Wire`/`Case2Wire` for the fold-extend primitives, so the twin cannot
be reached from the case wires without an import cycle).

This module sits DOWNSTREAM of the twin and re-proves the two case-preservation lemmas with conjunct B
routed to `realBranch_multiAffine_step'`. The summit (`MonumentAssembly`) re-points to these, moving the
unprimed step off the summit cone; the summit's remaining `sorryAx` on this path is then the single
canonical frontier `realBranch_appendResidDescent` (consumed inside the twin's descent).

**Wall compatibility (never edits `Case1Wire`).** Conjunct A stays `case1_conjA` / `case2_conjA`
byte-identical to the primed originals — so when the wall lane lands `boostReady_case11` into `Case1Wire`
(`case1_conjA`'s obligation), nothing here moves. This module only imports `Case1Wire`, never edits it.

No homogeneity pull: the step returns the FULL `Deg1SupportedSlot` (both conjuncts) from the parent slot
`hinv.2`; `foldResid_layerHomogeneous`/`'` is a separate, already-consumer-less pair not on this path.
-/

open MeasureTheory Set Filter Topology RLCT
open DLNFibre.Core DLNFibre.Core.Aoyagi DLNFibre.DLN.RLCT DLNFibre.DLN.RLCT.Engine

namespace DLNFibre.DLN.Aoyagi

/-- `= Case1Wire.case1_preserves_stepInv'` with conjunct B's step call routed to the proved twin
`realBranch_multiAffine_step'` (MultiAffineStepWire). Conjunct A is `case1_conjA`, byte-identical. -/
theorem case1_preserves_stepInv'' {N : ℕ}
    (d : Fin (N + 1) → ℕ) (hN : 0 < N) (hpos : ∀ k, 0 < d k)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d)
    (p : TreePath d) (ed : TreeEdge d p) (hcase1 : ed.isCase1)
    (hlayer : ed.nextState.layer + 1 < N)
    (hinv : FoldStepInvAt d e (supportAt d p.conState.layer p.conState.cleared) p)
    (hbranch : (p.extend ed).IsRealBranch e) :
    FoldStepInvAt d e
      (supportAt d (p.extend ed).conState.layer (p.extend ed).conState.cleared) (p.extend ed) := by
  refine ⟨case1_conjA d e p ed hcase1 hlayer hinv hbranch, ?_⟩
  exact realBranch_multiAffine_step' hpos e p ed hlayer hbranch hinv.2

/-- `= Case2Wire.case2_preserves_stepInv'` with conjunct B's step call routed to the proved twin
`realBranch_multiAffine_step'` (MultiAffineStepWire). Conjunct A is `case2_conjA`, byte-identical. -/
theorem case2_preserves_stepInv'' {N : ℕ}
    (d : Fin (N + 1) → ℕ) (hN : 0 < N) (hpos : ∀ k, 0 < d k)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d)
    (p : TreePath d) (ed : TreeEdge d p) (hcase2 : ed.isCase2)
    (hlayer : ed.nextState.layer + 1 < N)
    (hinv : FoldStepInvAt d e (supportAt d p.conState.layer p.conState.cleared) p)
    (hbranch : (p.extend ed).IsRealBranch e) :
    FoldStepInvAt d e
      (supportAt d (p.extend ed).conState.layer (p.extend ed).conState.cleared) (p.extend ed) := by
  refine ⟨case2_conjA d hpos e p ed hcase2 hlayer hinv hbranch, ?_⟩
  exact realBranch_multiAffine_step' hpos e p ed hlayer hbranch hinv.2

end DLNFibre.DLN.Aoyagi
