import DLNFibre.Core.Aoyagi.PrincipalInv

/-!
SEAT-L4 — Lean-checked crux of the `SupportedOn` gap in the edge-indexed L3/L4
(`DLN.Aoyagi.MonumentAtlas.Case1Preservation`).

`SupportedOn resid center V` (resid depends only on center coordinates) is NECESSARY but INSUFFICIENT
for the δ=1 child divisibility `BlockChild` demands: the residual `resid = fun u ↦ 1 + u 1` is
`SupportedOn {0,1}` and continuous, yet its pullback through `blockBlowupMap {0,1} 0` is NOT divisible
by the pivot coordinate `u 0` — it fails to vanish on `{u 0 = 0}` (the SupportedOn docstring's claim
"residⱼ ∘ blockBlowupMap is divisible by u_p" is false for a general SupportedOn residual). The δ=1
child then needs `(F∘g∘σ)/(u_p·(b∘σ))` continuous, which this residual denies (order deficit).
FIX: pin resid to a center-coordinate combination (analytic + vanishing at 0), which is exactly
`Core.Aoyagi.BlockDivision`'s assumption.
-/

open DLNFibre.Core.Aoyagi Set

/-- The witness residual is genuinely `SupportedOn {0,1}` (independent of the spectator coord `2`). -/
example : SupportedOn (fun (_ : Fin 1) (u : Fin 3 → ℝ) ↦ 1 + u 1) ({0, 1} : Finset (Fin 3))
    Set.univ := by
  intro j u _ d hd t
  have hd1 : (1 : Fin 3) ≠ d := by rintro rfl; exact hd (by decide)
  simp only [Function.update_apply, if_neg hd1]

/-- …and it is continuous. -/
example : Continuous (fun u : Fin 3 → ℝ ↦ 1 + u 1) := continuous_const.add (continuous_apply 1)

/-- **The crux, kernel-checked:** this `SupportedOn` + continuous residual pulled back through
`blockBlowupMap {0,1} 0` is NOT divisible by the pivot coordinate `u 0` (no quotient `c`, continuous
or not) — it equals `1` at a point with `u 0 = 0`, where any `u 0 · c` is `0`. -/
example :
    ¬ ∃ c : (Fin 3 → ℝ) → ℝ,
      ∀ w : Fin 3 → ℝ,
        (fun u : Fin 3 → ℝ ↦ 1 + u 1) (blockBlowupMap ({0, 1} : Finset (Fin 3)) 0 w) = w 0 * c w := by
  rintro ⟨c, hc⟩
  have h := hc ![0, 7, 0]
  simp [blockBlowupMap] at h
