import DLNFibre.DLN.Aoyagi.MultiAffineStepWire
import DLNFibre.DLN.Aoyagi.ClearedFold

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

/-- **Returns the CLEARED step invariant `FoldStepInvAt_cleared`** (27th-catch re-point, CFF): consumes
`ClearedFold.case1_preserves_cleared` (the raw `case1_conjA` chain is REFUTED-raw + DELETED — the cleared
object is where property (D) holds). `he : e = canonFlatten d` bridges to the canonFlatten-pinned cleared
trio. Conjunct B rides `realBranch_multiAffine_step_cleared` inside `case1_preserves_cleared` (a CAPF
frontier). -/
theorem case1_preserves_stepInv'' {N : ℕ}
    (d : Fin (N + 1) → ℕ) (hN : 0 < N) (hpos : ∀ k, 0 < d k)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (he : e = canonFlatten d)
    (p : TreePath d) (ed : TreeEdge d p) (hcase1 : ed.isCase1)
    (hlayer : ed.nextState.layer + 1 < N)
    (hinv : FoldStepInvAt_cleared d (supportAt d p.conState.layer p.conState.cleared) p)
    (hbranch : (p.extend ed).IsRealBranch e) :
    FoldStepInvAt_cleared d
      (supportAt d (p.extend ed).conState.layer (p.extend ed).conState.cleared) (p.extend ed) := by
  subst he
  exact case1_preserves_cleared d hN hpos p ed hcase1 hlayer hinv hbranch

/-- **Returns the CLEARED step invariant `FoldStepInvAt_cleared`** (27th-catch re-point, CFF): consumes
`ClearedFold.case2_preserves_cleared` (the easy case; same locus route). `he : e = canonFlatten d` bridges
to the canonFlatten-pinned cleared trio. Uniform with the case-1 twin so the summit carries one cleared
invariant across both case families. -/
theorem case2_preserves_stepInv'' {N : ℕ}
    (d : Fin (N + 1) → ℕ) (hN : 0 < N) (hpos : ∀ k, 0 < d k)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (he : e = canonFlatten d)
    (p : TreePath d) (ed : TreeEdge d p) (hcase2 : ed.isCase2)
    (hlayer : ed.nextState.layer + 1 < N)
    (hinv : FoldStepInvAt_cleared d (supportAt d p.conState.layer p.conState.cleared) p)
    (hbranch : (p.extend ed).IsRealBranch e) :
    FoldStepInvAt_cleared d
      (supportAt d (p.extend ed).conState.layer (p.extend ed).conState.cleared) (p.extend ed) := by
  subst he
  exact case2_preserves_cleared d hN hpos p ed hcase2 hlayer hinv hbranch

end DLNFibre.DLN.Aoyagi
