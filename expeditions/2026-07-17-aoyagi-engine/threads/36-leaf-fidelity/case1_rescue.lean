import DLNFibre.Core.Aoyagi.PrincipalInv
/- ROUND-3 Case1 witness RESCUED by a shear: sh = rotation (x₀,x₁,x₂)↦(x₀,x₂,-x₁),
   σu=(u₀,u₂,-u₀u₁), entry = 2(σu)₀(σu)₂ = -2u₀²u₁, b' = u₀·(σu)₀ = u₀². Entry ∈ ⟨u₀²⟩ (ratio -2u₁). -/
example (u : Fin 3 → ℝ) : (2 : ℝ) * (u 0) * (-(u 0 * u 1)) = (u 0)^2 * (-2 * u 1) := by ring
