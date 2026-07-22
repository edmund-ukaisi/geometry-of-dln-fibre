import DLNFibre.DLN.Aoyagi.Case1Wire

/-!
# `DLN.Aoyagi.Case1WallStaged` — the WALL dispatch, staged (SEAT-L4)

**STAGING FILE (seat-L4's branch, team-lead-invited 2026-07-22).** Proves the FULL wall
`case1_preserves_stepInv` conclusion by DISPATCH, consuming my banked conjunct-1 lemmas plus TWO
named frontier obligations that are elder-ruling-pending — so the closed edit is staged and the
dispatch is verified correct BEFORE those obligations land. NOT in the aggregator; NOT in
`MonumentAtlas` (that statement lives in the elder→render→arch-C→delta-read lane). When the two
obligations land, the body of `MonumentAtlas.case1_preserves_stepInv` becomes this dispatch verbatim.

The wall (case1 = case11 ∨ case12) splits:
* **conjunct-1** (`∃q, StepInv`): `δ=0` → `stepInv_child_delta0` (case-generic pullback, BANKED);
  `δ=1` case12 → `stepInv_child_delta1_append` fed `deg1SupportedOn_center_of_hslot` (cover route,
  BANKED); `δ=1` case11 → `stepInv_child_delta1_append` fed the BOOST-READINESS obligation below
  (Codex-corrected mechanism: the residual IS degree-1 on the boost center via the b-chain, so the
  SAME append lemma closes it — only the `Deg1SupportedOn ed.center` source differs).
* **conjunct-2** (`∀j, Deg1SupportedSlot` on the CHILD support): the node-form multi-affine
  obligation below, applied at the child `p.extend ed` (its `IsRealBranch` is exactly `hbranch`).

Both obligations take the wall's LOCKED hypotheses (`hbranch`/dispatch guards) as input — no new wall
hypothesis. They are the two `sorry`s here; everything else is banked clean-three.
-/

open MeasureTheory Set Filter Topology RLCT
open DLNFibre.Core DLNFibre.Core.Aoyagi DLNFibre.DLN.RLCT DLNFibre.DLN.RLCT.Engine

namespace DLNFibre.DLN.Aoyagi

variable {N : ℕ}

/-- **FRONTIER OBLIGATION 1 — case11 δ=1 BOOST-READINESS** (Codex xhigh 2026-07-22, elder-ruling-pending).
For a real case1(1) edge at δ=1, the parent residual is `Deg1SupportedOn` the LEDGER (boost) center
`ed.center = {pivot} ∪ partial-block` — even though its GEOMETRIC support `supportAt` is the larger full
layer block: the untouched (`support ∖ center`) terms carry `u_pivot` in their non-dominant b-chain
coefficient `b_i/b_1`. NOT derivable from `hinv`'s `supportAt`-`Deg1SupportedSlot` nor from
`IsRealBranch` as pinned (Codex); the honest home (new carried-invariant conjunct / stronger
`IsRealBranch` shear pin / this stub) is the elder's call. Feeds `stepInv_child_delta1_append`
exactly like the case12 cover route. -/
theorem realBranch_boostReady_case11 (d : Fin (N + 1) → ℕ)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) {p : TreePath d} (ed : TreeEdge d p)
    (hδ : edgeδ d p = true) (hc11 : ed.case = StepCase.case11)
    (hbranch : (p.extend ed).IsRealBranch e) :
    Deg1SupportedOn (foldResid d e p) ed.center (foldRegion d e p) := by
  -- map: B-derived-boostReady-case11 (δ=1 boost-center Deg1 via b-chain; TRACKED-OPEN, elder-pending)
  sorry

/-- **FRONTIER OBLIGATION 2 — node-form multi-affine (conjunct-2)** (elder-routed 2026-07-22, node-form
verbatim). For ANY real-branch node, the residual is `Deg1SupportedSlot` on its own `supportAt` window.
This subsumes both the parent (= `hinv.2`) and the child; the wall's conjunct-2 is this at `p.extend ed`.
The DESCENT content (case12/case2-δ1: residual layer S → degree-1 on layer S+1 via the strict
transform) lives HERE. Zero consumers of the prior child-branch `realBranch_multiAffine` shape → the
node-form restatement is the mint. -/
theorem realBranch_multiAffine_node (d : Fin (N + 1) → ℕ)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (p : TreePath d) (hb : p.IsRealBranch e) :
    ∀ j, Deg1SupportedSlot d (foldResid d e p) j
      (supportAt d p.conState.layer p.conState.cleared) (supportLayerOf p.conState)
      (foldRegion d e p) := by
  -- map: B-derived-multiAffine-node (node-form residual deg-1 on supportAt; TRACKED-OPEN, elder-routed)
  sorry

/-- **⟨THE WALL — staged dispatch⟩** `case1_preserves_stepInv`, proven by dispatch consuming the two
frontier obligations above + my banked conjunct-1 lemmas. Byte-identical signature to
`MonumentAtlas.case1_preserves_stepInv`; when the obligations land this body wires in verbatim. -/
theorem case1_preserves_stepInv_staged
    (d : Fin (N + 1) → ℕ) (hN : 0 < N) (hpos : ∀ k, 0 < d k)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d)
    (p : TreePath d) (ed : TreeEdge d p) (hcase1 : ed.isCase1)
    (hlayer : ed.nextState.layer + 1 < N)
    (hinv : FoldStepInvAt d e (supportAt d p.conState.layer p.conState.cleared) p)
    (hbranch : (p.extend ed).IsRealBranch e) :
    FoldStepInvAt d e
      (supportAt d (p.extend ed).conState.layer (p.extend ed).conState.cleared) (p.extend ed) := by
  have hlt : ¬ N ≤ ed.nextState.layer := Nat.not_le.mpr (by omega)
  obtain ⟨⟨q, hq⟩, hslot⟩ := hinv
  refine ⟨?_, realBranch_multiAffine_node d e (p.extend ed) hbranch⟩
  by_cases hδ : edgeδ d p = true
  · rcases hcase1 with hc11 | hc12
    · -- δ=1 case11: boost-readiness → append crux
      exact stepInv_child_delta1_append d e ed hlt hδ
        (realBranch_boostReady_case11 d e ed hδ hc11 hbranch) q hq
    · -- δ=1 case12: cover route → append crux
      exact stepInv_child_delta1_append d e ed hlt hδ
        (deg1SupportedOn_center_of_hslot d e ed hδ (Or.inl hc12) hbranch hslot) q hq
  · -- δ=0: pure pullback (case-generic)
    have hδ0 : edgeδ d p = false := by simp only [Bool.not_eq_true] at hδ; exact hδ
    exact stepInv_child_delta0 d e ed hlt hδ0 q hq

end DLNFibre.DLN.Aoyagi
