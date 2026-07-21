import DLNFibre.Core.Aoyagi.PrincipalInv
open DLNFibre.Core.Aoyagi

/-- ROOT-INSTANCE non-vacuity probe (elder root check: U=V=I, b_{k₀}=1, divisibility into ⟨1⟩).
    g = id, b ≡ 1, residual = the generators F themselves, q = Kronecker identity.
    S3 UPDATE: the family must VANISH at 0 (`hF0` — the real `coreGen` does; the old constant witness
    died under the added deepest-point clause). -/
example {M D : ℕ} (F : Fin M → (Fin D → ℝ) → ℝ) (V : Set (Fin D → ℝ))
    (hF0 : ∀ i, F i 0 = 0) :
    StepInv F id (fun _ ↦ 1) F (fun i j _ ↦ if i = j then (1:ℝ) else 0) V := by
  refine ⟨fun i j => continuousOn_const, fun i => hF0 i, ?_⟩
  intro u hu i
  simp only [Function.comp_apply, id_eq, one_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [if_neg (fun h => hji h.symm), zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- Also confirm the TERMINAL PrincipalInv is inhabitable at the trivial instance
    (single generator that IS b, q=1, r=1): principality born. -/
example {D : ℕ} (b : (Fin D → ℝ) → ℝ) (V : Set (Fin D → ℝ)) :
    PrincipalInv (fun _ : Fin 1 => b) id b (fun _ => 1) (fun _ => 1) V := by
  refine ⟨fun i => continuousOn_const, fun i => continuousOn_const, ?_, ?_⟩
  · intro u hu i; simp
  · intro u hu; simp
