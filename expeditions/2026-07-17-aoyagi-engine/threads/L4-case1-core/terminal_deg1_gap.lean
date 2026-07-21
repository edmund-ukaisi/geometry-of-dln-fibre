import DLNFibre.Core.Aoyagi.PrincipalInv
open DLNFibre.Core.Aoyagi Set

-- The terminal-reaching branch sets foldResid = (fun _ ↦ 1) over Fin 1. That residual CANNOT satisfy
-- Deg1SupportedOn (needed by FoldStepInvAt's conjunct 2): 1 = ∑_{i∈C} c_i·u_i fails at u = 0.
example (D : ℕ) (C : Finset (Fin D)) :
    ¬ Deg1SupportedOn (fun (_ : Fin 1) (_ : Fin D → ℝ) ↦ (1 : ℝ)) C (Set.univ) := by
  intro h
  obtain ⟨c, _, hrepr, _⟩ := h 0
  have h0 := hrepr 0 (Set.mem_univ _)
  simp at h0   -- 1 = ∑_{i∈C} c_i(0)·(0 i) = ∑ c_i(0)·0 = 0
