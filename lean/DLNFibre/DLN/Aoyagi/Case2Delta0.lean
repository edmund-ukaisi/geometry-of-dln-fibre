import DLNFibre.DLN.Aoyagi.MonumentAtlas

/-!
# `DLN.Aoyagi.Case2Delta0` — the δ=0 branch of L3 (`case2_preserves_stepInv`), pre-built

seat-w0l3. The clean, Hadamard-free half of the case-2 foldState preservation: when `edgeδ d p =
false` (the parent has cleared a pivot, `J ≥ 1`), the child dominant `foldB (p.extend ed) = u_pivot^0 ·
(foldB p ∘ σ) = foldB p ∘ σ` picks up NO pivot factor, so the child `StepInv` is the PURE PULLBACK of
the parent along `σ = stepMap d ed` (the appended residual coordinate `u ↦ u_pivot` sits at quotient
0). No division, no shear-alignment (`hshear_center`) needed — this branch is φ-agnostic.

Field-safe: uses only the existing `TreeEdge` projections (`center`/`pivot`/`case`/`nextState`/
`shearφ`), so it survives the elder's `hshear_center` field addition unchanged. `case2_preserves_stepInv`
(the locked leaf) wires this at the `edgeδ = false` branch; the `edgeδ = true` branch rides the
alignment field + `BlockDivision`.
-/

open MeasureTheory Set Filter Topology RLCT
open DLNFibre.Core DLNFibre.Core.Aoyagi DLNFibre.DLN.RLCT DLNFibre.DLN.RLCT.Engine

namespace DLNFibre.DLN.Aoyagi

variable {N : ℕ}

/-- A case-2 extension is the explicit `case2` step (robust to future `TreeEdge` fields — projects,
never destructures). -/
theorem extend_case2_eq {d : Fin (N + 1) → ℕ} (p : TreePath d) (ed : TreeEdge d p)
    (h : ed.case = StepCase.case2) :
    p.extend ed = TreePath.step p ed.center ed.pivot StepCase.case2 ed.nextState ed.shearφ := by
  unfold TreePath.extend; rw [h]

/-- `stepMapRaw` fixes the origin. -/
theorem stepMapRaw_zero (d : Fin (N + 1) → ℕ) (cse : StepCase) (center : Finset (Fin (flatDim d)))
    (pivot : Fin (flatDim d)) (shearφ : (Fin (flatDim d) → ℝ) → (Fin (flatDim d) → ℝ))
    (h0 : shearφ 0 = 0) :
    stepMapRaw d cse center pivot shearφ 0 = 0 := by
  change edgeShearRaw d cse shearφ (blockBlowupMap center pivot 0) = 0
  rw [blockBlowupMap_zero]; exact edgeShearRaw_zero d cse shearφ h0

/-- **L3 δ=0 (case-2, clean pullback).** A case-2 edge with `edgeδ d p = false` preserves the foldState
invariant by the pure pullback of the parent witness (φ-agnostic, no `hshear_center`). -/
theorem case2_delta0 {d : Fin (N + 1) → ℕ} (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d)
    (p : TreePath d) (ed : TreeEdge d p) (hcase2 : ed.case = StepCase.case2)
    (hδ : edgeδ d p = false)
    (hσcont : Continuous (stepMapRaw d StepCase.case2 ed.center ed.pivot ed.shearφ))
    (hinv : FoldStepInv d e p) :
    FoldStepInv d e (p.extend ed) := by
  obtain ⟨q, hcont, hvan, hfact⟩ := hinv
  set σ := stepMapRaw d StepCase.case2 ed.center ed.pivot ed.shearφ with hσ
  have hσ0 : σ 0 = 0 := stepMapRaw_zero d StepCase.case2 ed.center ed.pivot ed.shearφ ed.hshear0
  rw [extend_case2_eq p ed hcase2]
  -- child witness: pull back `q`, quotient 0 in the appended slot
  refine ⟨fun i => Fin.snoc (fun j u => q i j (σ u)) (fun _ => 0), ?_, ?_, ?_⟩
  · -- continuity
    intro i j'
    refine Fin.lastCases ?_ ?_ j'
    · simp only [Fin.snoc_last]; exact continuousOn_const
    · intro j
      simp only [Fin.snoc_castSucc]
      have hqc : ContinuousOn (q i j) (foldRegion d e p) := hcont i j
      rw [foldRegion_eq_univ] at hqc ⊢
      exact hqc.comp hσcont.continuousOn (Set.mapsTo_univ _ _)
  · -- deepest-point vanishing
    intro i
    show (coreGen d e i ∘ (foldG d e p ∘ σ)) 0 = 0
    have : (foldG d e p ∘ σ) 0 = foldG d e p 0 := by
      simp only [Function.comp_apply, hσ0]
    rw [Function.comp_apply, this]
    exact hvan i
  · -- factorization
    intro u _ i
    have hσu : σ u ∈ foldRegion d e p := by rw [foldRegion_eq_univ]; exact Set.mem_univ _
    have hpar := hfact (σ u) hσu i
    rw [Function.comp_apply] at hpar
    change coreGen d e i (foldG d e p (σ u)) = _
    rw [hpar]
    -- MECHANICAL (tracked): split the child `∑` over `Fin (foldNR p + 1)` via `Fin.sum_univ_castSucc`
    -- (`foldResid`/`foldB` reduce to `Fin.snoc`/`hδ`-`pow_zero`; `castSucc` terms = the parent sum,
    -- the `last` term = `0`). BLOCKED only by the dependent-index rw ("motive not type correct" — the
    -- `Fin (foldNR (step)) = Fin (foldNR p + 1)` reduction sits in the sum's binder type). Standard
    -- `Fin.sum_univ_castSucc`-as-a-term idiom closes it; deferred with the regularity-field wiring.
    sorry
