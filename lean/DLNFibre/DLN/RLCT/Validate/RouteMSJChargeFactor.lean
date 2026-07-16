import DLNFibre.DLN.RLCT.Validate.RouteMSJIncidenceAssembly

set_option linter.style.longLine false

/-!
# `RouteMSJChargeFactor` — the charge/loss factoring of `frontChargeIntegrand`

The front-charge integrand (step-2 output, `RouteMSJIncidenceAssembly`) is an `x`-integral of
`ofReal( det(Q_bQ_bᵀ)^{−a/2} · Cresid · (E_top(x)+E_tr(x))^{−q} )` (`a = M₀−u`, `q = c'−ab/2`,
`Q_b = (hsQ …).submatrix Sum.inr id = A_cor·Z_deep`). The determinant CHARGE is `x`-INDEPENDENT, so it
factors OUT of the `x`-integral EXACTLY:

  frontChargeIntegrand M u c' p = ofReal( det(Q_bQ_bᵀ)^{−a/2} · Cresid ) · frontLossIntegral M u c' p,

where `frontLossIntegral` = `∫_x ofReal((E_top+E_tr)^{−q})` is the pure LOSS integral. This banks the
charge/loss SEPARATION exactly (pen-and-paper + decorrelated Codex, `threads/genm-deephier/codex/`);
it does NOT reduce `∫_box frontCharge` to a factored `[bound]·[chargeFreeBox]`. Reason (intloss's
numerical witness): `frontLossIntegral p` is per-`p` FINITE (generic rank ⟹ `2q < rank L`) but NOT
uniformly bounded in `p` — it blows up `~ σ_min(L_p)^{−2q} → ∞` as `p → the loss-degeneracy locus`, so no
`p`-independent `D` exists. The interior finiteness is instead the COUPLED integral
`∫_box frontCharge = ∫_{z,A_cor} charge(p)·frontLossIntegral(p) < ⊤`: near the locus the charge
`det(Q_bQ_bᵀ)^{−a/2}` stays BOUNDED (`Q_b = A_cor·Z_deep` generic there) while the loss blow-up is
`p`-integrable (blow-up-exponent < dim `z`). That coupled boundary-RLCT estimate is owned by
couplerad/corankrec/schurrec, NOT this file. (Also settled: `E_top` is load-bearing — the naive
"drop `E_top`" bound DIVERGES, Codex counterexample.)
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory Set
open scoped ENNReal BigOperators

variable {L : ℕ}

/-- **The pure loss integral** `∫_x ofReal((E_top(x)+E_tr(x))^{−q})` at cut `u`, reduced params/corank
`p = (z, A_cor)`. The `x`-integral of the front loss `(E_top+E_tr)^{−q}` (`q = c'−(M₀−u)(M₁−u)/2`), with
the `x`-independent charge `det(Q_bQ_bᵀ)^{−a/2}·Cresid` STRIPPED — the `p`-dependent factor that (per-`p`
finite, NOT uniformly bounded) is integrated against the charge in the coupled interior estimate.
`E_top = frobSq(P·Q̃ₚ)`,
`E_tr = frobSq(C·Q̃ₚ·(1−proj))`, `Q̃ₚ = Q_inl + P⁻¹B₁₂Q_inr`. -/
noncomputable def frontLossIntegral (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (c' : ℝ)
    (p : Params (redChain u M) × (Fin (M 1 - u) → Fin (M 2) → ℝ)) : ℝ≥0∞ :=
  ∫⁻ x in outerDom u (M 0 - u) (M 1 - u) 1,
    ENNReal.ofReal
      ((frobSq (Matrix.of x.1.1
            * ((hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inl id
              + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2
                  * (hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inr id))
          + frobSq ((Matrix.of x.2
              * ((hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inl id
                + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2
                    * (hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inr id))
            * (1 - ((hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inr id)ᵀ
                * ((hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inr id
                    * ((hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inr id)ᵀ)⁻¹
                * (hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inr id)))
          ^ (-(c' - ((M 0 - u : ℕ) : ℝ) * ((M 1 - u : ℕ) : ℝ) / 2)))

/-- **The charge Gram det is nonnegative** `0 ≤ det(Q_bQ_bᵀ)` — the `b×b` Gram of `Q_b` is PosSemidef, so
its determinant is nonneg (`PosSemidef.det_nonneg`); over ℝ `Q_bᵀ = Q_bᴴ`. Unconditional (no `hG`). -/
theorem chargeGram_det_nonneg (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (p : Params (redChain u M) × (Fin (M 1 - u) → Fin (M 2) → ℝ)) :
    0 ≤ ((hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inr id
        * ((hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inr id)ᵀ).det := by
  have hps : ((hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inr id
      * ((hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inr id)ᵀ).PosSemidef := by
    have h := Matrix.posSemidef_self_mul_conjTranspose
      ((hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inr id)
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using h
  exact hps.det_nonneg

/-- **Charge/loss factoring of `frontChargeIntegrand`.** The `x`-independent charge
`det(Q_bQ_bᵀ)^{−a/2}·Cresid` (`a = M₀−u`) pulls straight out of the `x`-integral: `frontChargeIntegrand`
equals `ofReal(charge)` times the pure `frontLossIntegral`. SOUND + self-contained (`Cresid ≥ 0`, the Gram
det `≥ 0`); banks the charge/loss separation. Feeds the coupled interior estimate `∫_box frontCharge =
∫_{z,A_cor} ofReal(charge)·frontLossIntegral(p) < ⊤` (frontLossIntegral is per-`p` finite but not uniformly
bounded, so this is a genuine coupled integral, not a factored product — the boundary-RLCT crux). -/
theorem frontChargeIntegrand_eq_charge_mul_loss (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (c' : ℝ)
    (p : Params (redChain u M) × (Fin (M 1 - u) → Fin (M 2) → ℝ)) :
    frontChargeIntegrand M u c' p
      = ENNReal.ofReal
          (((hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inr id
              * ((hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inr id)ᵀ).det
                ^ (-((M 0 - u : ℕ) : ℝ) / 2)
            * Cresid ((M 0 - u) * (M 1 - u)) c')
        * frontLossIntegral M u c' p := by
  have hK : 0 ≤ ((hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inr id
        * ((hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inr id)ᵀ).det
          ^ (-((M 0 - u : ℕ) : ℝ) / 2)
      * Cresid ((M 0 - u) * (M 1 - u)) c' :=
    mul_nonneg (Real.rpow_nonneg (chargeGram_det_nonneg M u p) _) (Cresid_nonneg _ _)
  rw [frontChargeIntegrand, frontLossIntegral,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr (fun x => ?_)
  rw [← ENNReal.ofReal_mul hK]

end DLNFibre.DLN.RLCT
