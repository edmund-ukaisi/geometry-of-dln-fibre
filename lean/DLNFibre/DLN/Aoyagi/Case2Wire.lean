import DLNFibre.DLN.Aoyagi.MonumentAtlas
import DLNFibre.DLN.Aoyagi.Case1Wire
import DLNFibre.DLN.Aoyagi.Case2TransportWire

/-!
# `DLN.Aoyagi.Case2Wire` — L3 (`case2_preserves_stepInv`) wired to the fold defs (SEAT-L3T2)

The primed leaf `case2_preserves_stepInv'` (statement-identical to
`MonumentAtlas.case2_preserves_stepInv`; the controller swaps the MonumentAtlas `sorry` to
`:= case2_preserves_stepInv' …` at integration — same pattern as L8's `leafPath_realizesExponents'`).
Kept here (not in `MonumentAtlas`) because the divisibility engine it consumes — `Case1Wire`'s
`stepInv_child_delta0`/`exists_ignoresCoords_decomp`/`canonCenterOf_append_subset_layerCoords` and
`Case2TransportWire`'s `case_child_stepInv_divisibility` — all IMPORT `MonumentAtlas`, so the proof
cannot live upstream of them.

**CONJUNCT A (divisibility ∃q) — CLOSED, both δ:**
* δ=0 (`edgeδ d p = false`, the parent has cleared a pivot): pure pullback, `q' = q∘stepMap` —
  `Case1Wire.stepInv_child_delta0` (case-generic; no crux).
* δ=1 (`edgeδ d p = true`, `cleared = 0`): the `u_pivot` crux. `Case2TransportWire`'s
  `case_child_stepInv_divisibility` consumes `Deg1SupportedOn (foldResid p) ed.center`, which we DERIVE
  from `hinv` here: at δ=1 `ed.center = supportAt = blockCoords(layer)` (`realBranch`'s center-pin +
  the cover equality, `cleared = 0`), and `FoldStepInvAt`'s `Deg1SupportedSlot` (a support-decomp on
  `supportAt` + `AffineOn` on the support layer `⊇ supportAt`) upgrades to the IgnoresCoords form via
  seat-L4's banked bridge `exists_ignoresCoords_decomp`.

**CONJUNCT B (child `Deg1SupportedSlot` on the descended `supportAt(child)`) — seat-L4's WALL.** The
child-residual re-factoring (the graded-decomposition companion to `Case1Wire.exists_graded_decomp`
PLUS its `PerLayerDeg1From` layerwise-affine strengthening). Owned by seat-L4, stated
CASE-GENERICALLY so this file consumes it. Left as the single tracked `sorry` below (the wall's
`-- map:` node); it closes when seat-L4's companion lands.
-/

open MeasureTheory Set Filter Topology RLCT
open DLNFibre.Core DLNFibre.Core.Aoyagi DLNFibre.DLN.RLCT DLNFibre.DLN.RLCT.Engine

namespace DLNFibre.DLN.Aoyagi

variable {N : ℕ}

/-- **L3 conjunct A (divisibility ∃q) — CLOSED, both δ.** The child `StepInv` against the fold's own
`foldG`/`foldB`/`foldResid` at a case-2 interior edge. δ=0 is the pure pullback (`stepInv_child_delta0`);
δ=1 is the `u_pivot` crux (`case_child_stepInv_divisibility`), whose `Deg1SupportedOn (foldResid p)
ed.center` input is derived from `hinv` here — at δ=1 `ed.center = supportAt = blockCoords(layer)`
(center-pin + the cover equality, `cleared = 0`), and `Deg1SupportedSlot` upgrades to the IgnoresCoords
form via seat-L4's `exists_ignoresCoords_decomp`. Consumes NO sorried stub — axiom-clean. -/
theorem case2_conjA
    {N : ℕ} (d : Fin (N + 1) → ℕ) (hpos : ∀ k, 0 < d k)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d)
    (p : TreePath d) (ed : TreeEdge d p) (hcase2 : ed.isCase2)
    (hlayer : ed.nextState.layer + 1 < N)
    (hinv : FoldStepInvAt d e (supportAt d p.conState.layer p.conState.cleared) p)
    (hbranch : (p.extend ed).IsRealBranch e) :
    ∃ q : Fin (d (Fin.last N) * d 0) → Fin (foldNR d (p.extend ed)) → (Fin (flatDim d) → ℝ) → ℝ,
      StepInv (coreGen d e) (foldG d e (p.extend ed)) (foldB d e (p.extend ed))
        (foldResid d e (p.extend ed)) q (foldRegion d e (p.extend ed)) := by
  classical
  have hcase2' : ed.case = StepCase.case2 := hcase2
  by_cases hδ : edgeδ d p = true
  · -- δ=1: the u_pivot crux; derive `Deg1SupportedOn (foldResid p) ed.center` from `hinv`.
    have hcl : p.conState.cleared = 0 := of_decide_eq_true hδ
    obtain ⟨-, ⟨sc, hsc, hecase, hchild, hcenter, -⟩, -⟩ := hbranch
    have hsce : sc.ecase = StepCase.case2 := hecase.trans hcase2'
    have hsl : supportLayerOf p.conState = p.conState.layer := by
      unfold supportLayerOf; rw [if_pos hcl]
    -- ed.center = supportAt (blockCoords(layer)) at δ=1 — the cover equality
    have hce : ed.center = supportAt d p.conState.layer p.conState.cleared := by
      rw [hcenter, supportAt, if_pos hcl, blockCoords]
      simp only [canonCenterOf, hsce]
      congr 1
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hcl, Nat.zero_le, true_and]
    have hSX : supportAt d p.conState.layer p.conState.cleared ⊆ layerCoords d p.conState.layer := by
      rw [← hce, hcenter]
      exact canonCenterOf_append_subset_layerCoords d p.conState sc (Or.inr hsce)
    have hguniv : foldRegion d e p = Set.univ := foldRegion_eq_univ e p
    have hdeg1 : Deg1SupportedOn (foldResid d e p) ed.center (foldRegion d e p) := by
      rw [hce, hguniv]
      intro j
      obtain ⟨⟨c, hc_cont, hc_repr⟩, hperlayer⟩ := hinv.2 j
      have haff : AffineOn (foldResid d e p j) (layerCoords d p.conState.layer) Set.univ := by
        have h := hperlayer p.conState.layer (by rw [hsl])
        rwa [hguniv] at h
      obtain ⟨c', hc'_cont, hc'_repr, hc'_ign⟩ := exists_ignoresCoords_decomp
        (foldResid d e p j) (supportAt d p.conState.layer p.conState.cleared)
        (layerCoords d p.conState.layer) hSX c
        (fun i => continuousOn_univ.mp (by rw [← hguniv]; exact hc_cont i))
        (fun u => hc_repr u (by rw [hguniv]; exact Set.mem_univ u)) haff
      exact ⟨c', fun i => (hc'_cont i).continuousOn, fun u _ => hc'_repr u, hc'_ign⟩
    exact case_child_stepInv_divisibility d e p ed (by omega) hdeg1 hinv.1
  · -- δ=0: pure pullback, no crux.
    have hδ0 : edgeδ d p = false := by
      cases h : edgeδ d p with
      | false => rfl
      | true => exact absurd h hδ
    obtain ⟨q, hq⟩ := hinv.1
    exact stepInv_child_delta0 d e ed (by omega) hδ0 q hq

/-- **L3 — a case-2 edge preserves the foldState invariant** (primed; statement-identical to
`MonumentAtlas.case2_preserves_stepInv`). Conjunct A is `case2_conjA` (closed, axiom-clean); conjunct B
is seat-L4's shared re-factoring wall (the single tracked `sorry`). -/
theorem case2_preserves_stepInv'
    {N : ℕ} (d : Fin (N + 1) → ℕ) (hN : 0 < N) (hpos : ∀ k, 0 < d k)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d)
    (p : TreePath d) (ed : TreeEdge d p) (hcase2 : ed.isCase2)
    (hlayer : ed.nextState.layer + 1 < N)
    (hinv : FoldStepInvAt d e (supportAt d p.conState.layer p.conState.cleared) p)
    (hbranch : (p.extend ed).IsRealBranch e) :
    FoldStepInvAt d e
      (supportAt d (p.extend ed).conState.layer (p.extend ed).conState.cleared) (p.extend ed) := by
  refine ⟨case2_conjA d hpos e p ed hcase2 hlayer hinv hbranch, ?_⟩
  -- CONJUNCT B — child `Deg1SupportedSlot` on `supportAt(child)` (the descended block); CLOSED via the
  -- step-form `realBranch_multiAffine_step`: parent slot (`hinv.2`) + child branch (`hbranch`) → child slot.
  exact realBranch_multiAffine_step hpos e p ed hbranch hinv.2

/-- **Consume-fit regression (lane 4, seat-L3T2).** The `GeneratorCleared` datum EMITTED by
`lastLayer_clear_preserves` at an `S = L` clear (child `q.extend ed₁`) is EXACTLY the shape
`terminal_edge_stepInv` CONSUMES as `hgen` at that node — and likewise its `LastLayerInv` output is the
`hinv` input. The composition elaborates with NO defeq surgery, so the two ∃-shapes cannot drift (the
point of the single `GeneratorCleared` def, family ruling item 4). A permanent wiring check: statement
TRUE without proving either leaf (both sorried upstream), so it is a fit regression, not new content. -/
example {N : ℕ} (d : Fin (N + 1) → ℕ) (hN : 0 < N) (hpos : ∀ k, 0 < d k)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d)
    (q : TreePath d) (ed₁ : TreeEdge d q) (hlast : ed₁.nextState.layer + 1 = N)
    (hinv : LastLayerInv d e (supportAt d q.conState.layer q.conState.cleared) q)
    (hbranch₁ : (q.extend ed₁).IsRealBranch e)
    (ed₂ : TreeEdge d (q.extend ed₁)) (hterm : N ≤ ed₂.nextState.layer)
    (hbranch₂ : ((q.extend ed₁).extend ed₂).IsRealBranch e) :
    ∃ (r : Fin (d (Fin.last N) * d 0) → Fin 1 → (Fin (flatDim d) → ℝ) → ℝ)
      (i₀ : Fin (d (Fin.last N) * d 0)) (unit : (Fin (flatDim d) → ℝ) → ℝ),
      StepInv (coreGen d e) (foldG d e ((q.extend ed₁).extend ed₂))
          (foldB d e ((q.extend ed₁).extend ed₂))
          (fun _ : Fin 1 ↦ (1 : (Fin (flatDim d) → ℝ) → ℝ)) r
          (foldRegion d e ((q.extend ed₁).extend ed₂))
        ∧ ContinuousOn unit (foldRegion d e ((q.extend ed₁).extend ed₂))
        ∧ unit 0 ≠ 0
        ∧ (∀ u ∈ foldRegion d e ((q.extend ed₁).extend ed₂),
            (coreGen d e i₀ ∘ foldG d e ((q.extend ed₁).extend ed₂)) u
              = foldB d e ((q.extend ed₁).extend ed₂) u * unit u) := by
  obtain ⟨hinv₂, hgen₂⟩ := lastLayer_clear_preserves d hN hpos e q ed₁ hlast hinv hbranch₁
  exact terminal_edge_stepInv d hN hpos e (q.extend ed₁) ed₂ hterm hinv₂ hgen₂ hbranch₂

end DLNFibre.DLN.Aoyagi
