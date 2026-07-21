import DLNFibre.Core.Aoyagi.PrincipalInv
open DLNFibre.Core.Aoyagi

/- Elder check #1a: the IDEAL-MEMBERSHIP SupportedOn EXCLUDES the constant/spectator residual that the
   round-4 refutation used — `1 ∉ ⟨u₀⟩` (a unit is not a center-coordinate combination). So the δ=1
   free-center refutation dies EXACTLY at hsupp. -/
example : ¬ SupportedOn (fun (_ : Fin 1) _ => (1:ℝ)) ({0} : Finset (Fin 2)) (Set.univ) := by
  rintro ⟨c, _hcont, hrep⟩
  have h := hrep 0 0 (Set.mem_univ _)
  simp only [Finset.sum_singleton, Pi.zero_apply, mul_zero] at h
  exact one_ne_zero h

/- Elder check #1b: /u_pivot EXACTNESS — a center-supported entry, composed with the block blow-up,
   gains the pivot factor EXACTLY (every center coordinate → u_pivot·…). Here center={0,1}, pivot=0,
   the entry `u ↦ u 1` (∈ ⟨center coords⟩) pulls back to `u₀·u₁ ∈ ⟨u₀⟩`. -/
example (u : Fin 2 → ℝ) :
    (fun w : Fin 2 → ℝ => w 1) (blockBlowupMap ({0,1} : Finset (Fin 2)) 0 u) = u 0 * u 1 := by
  simp [blockBlowupMap]
