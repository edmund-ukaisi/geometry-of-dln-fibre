import DLNFibre.Core.Aoyagi.PrincipalInv

/-!
SCRATCH — STOP-ON-SUSPECT repro for SEAT-L4.

The FROZEN `Case1Preservation`, at `branch = false` (δ = 1, the Case-1(2) split), is FALSE for
general `StepInv` data. Reason: `0` is FORCED into the child region (`0 ∈ Vchart` is a required
output conjunct, and `σ 0 = sh (blowupMap p 0) = sh 0 = 0 ∈ V`). At `u = 0` the child dominant is
`b' 0 = (0 p)^1 · b (σ 0) = 0`, so the child `StepInv` equation forces `(F i ∘ g) 0 = 0` — a fact
`StepInv` does NOT provide (it holds only when `b 0 = 0`, i.e. `b` vanishes at the deepest point).
-/

open DLNFibre.Core.Aoyagi Set

example : ¬ Case1Preservation := by
  intro h
  -- Concrete data: D = 1, M = 1, nR = 2, all generators constant `1`, `g = id`, `b = 1`.
  -- Then `(F 0 ∘ g) 0 = 1 ≠ 0`, while StepInv holds (quotient `q = (1,0)`).
  have hstep : StepInv (fun (_ : Fin 1) (_ : Fin 1 → ℝ) ↦ (1 : ℝ)) id (fun _ ↦ (1 : ℝ))
      (fun (_ : Fin 2) (_ : Fin 1 → ℝ) ↦ (1 : ℝ))
      (fun (_ : Fin 1) (j : Fin 2) (_ : Fin 1 → ℝ) ↦ if j = 0 then (1 : ℝ) else 0) Set.univ := by
    refine ⟨fun i j => continuousOn_const, fun u _ i => ?_⟩
    simp
  obtain ⟨p, sh, Vchart, b', nR', resid', q', -, hsh0, -, -, -, hV0, hb'law, hstep'⟩ :=
    h isOpen_univ (Set.mem_univ _) hstep (le_refl 2) false
  have hp0 : (0 : Fin 1 → ℝ) p = 0 := rfl
  -- child StepInv at u = 0 (forced into the region), i = 0
  have key := hstep'.2 0 ⟨Set.mem_univ _, hV0⟩ 0
  -- b' 0 = (0 p)^1 * b (sh (blowupMap p 0)) = 0 * _ = 0
  have hb'0 : b' 0 = 0 := by rw [hb'law 0, hp0]; simp
  rw [hb'0] at key
  -- key LHS = (F 0 ∘ σ) 0 = 1 (F is constant); RHS = ∑ j, q' 0 j 0 * (0 * resid' j 0) = 0
  simp only [Function.comp_apply, mul_zero, zero_mul, Finset.sum_const_zero] at key
  exact one_ne_zero key
