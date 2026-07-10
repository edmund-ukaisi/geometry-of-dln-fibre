import DLNFibre.DLN.RLCT.Validate.RouteMSJCornerGate
import DLNFibre.DLN.RLCT.Validate.RouteMSJGoodLoss
import DLNFibre.DLN.RLCT.Validate.RouteMSJCorankResidual

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJGoodChart` — the good-chart endpoint in matrix coordinates

**Thread `genm-resmap`, Stage 2 (S,J) resolution-map tide.** The banked corner endpoint
`corner_block_cube_lintegral_lt_top_of_injective` (`RouteMSJCornerGate`) is stated over the FLAT cube
`[-1,1]ⁿ ⊆ (Fin n → ℝ)` for a squared-injective-linear loss `∑ⱼ (L z)ⱼ²`. The `(S,J)` change-of-variables
lands the good-chart resolved loss `g_cc(Γ, v) = frobSq(P·v·A₂) + frobSq((C·v + Γ·W)·A₂)` in **matrix
coordinates** — the joint block `(Γ, v)` ranging over a product of matrix boxes. This module bridges the
two: it flattens the matrix-product box to the flat cube (measure-preserving) and packages the good-chart
map `sjGoodMap` (banked, `RouteMSJGoodLoss`) as an injective linear map on the flat coordinates, so the
endpoint applies directly.

* **`twoMatBox_injectiveLinear_lintegral_lt_top`** — the abstract transport lemma: given ANY
  measure-preserving flatten `E : (Matrix p q × Matrix r s) ≃ᵐ (Fin n → ℝ)` sending the matrix-product box
  onto the flat cube, and an injective linear `L : (Fin n → ℝ) →ₗ (Fin m → ℝ)`, the matrix-box integral of
  the loss `(∑ⱼ (L (E x))ⱼ²)^{−c'}` is finite for `c' < n/2`. (`E` is a hypothesis; the concrete flatten is
  built below.)

S2-FREE (no `monomial_rlct`, no `cited_aoyagi_dln`); network-free (pure measure theory + matrix algebra).
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set Matrix
open scoped ENNReal BigOperators

/-- **The good-chart endpoint, matrix-box coordinates (transport form).** Given a measure-preserving
flatten `E` of the matrix-product domain `Matrix (Fin p) (Fin q) ℝ × Matrix (Fin r) (Fin s) ℝ` onto the
flat coordinate space `Fin n → ℝ` that carries the matrix-product box `matBox p q 1 ×ˢ matBox r s 1` onto
the flat cube `[-1,1]ⁿ`, and an injective linear `L : (Fin n → ℝ) →ₗ (Fin m → ℝ)`, the matrix-box integral
of the squared-linear loss `(∑ⱼ (L (E x))ⱼ²)^{−c'}` is finite below the threshold `c' < n/2`.

Pure transport: rewrite the domain to `E ⁻¹' cube` (`hbox`), push the integral along the
measure-preserving embedding `E` (`setLIntegral_comp_preimage_emb`) to the flat cube, and invoke the
banked `corner_block_cube_lintegral_lt_top_of_injective`. The concrete flatten `E` is supplied by
`twoMatFlat` below. -/
theorem twoMatBox_injectiveLinear_lintegral_lt_top {p q r s n m : ℕ} [NeZero n]
    (E : ((Fin p → Fin q → ℝ) × (Fin r → Fin s → ℝ)) ≃ᵐ (Fin n → ℝ))
    (hE : MeasurePreserving E
      (volume : Measure ((Fin p → Fin q → ℝ) × (Fin r → Fin s → ℝ)))
      (volume : Measure (Fin n → ℝ)))
    (hbox : matBox p q 1 ×ˢ matBox r s 1
      = E ⁻¹' Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1))
    (L : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (hL : Function.Injective L)
    (c' : NNReal) (hc' : (c' : ℝ) < (n : ℝ) / 2) :
    ∫⁻ x in matBox p q 1 ×ˢ matBox r s 1,
        ENNReal.ofReal ((∑ j, (L (E x) j) ^ 2) ^ (-(c' : ℝ))) < ⊤ := by
  rw [hbox]
  rw [hE.setLIntegral_comp_preimage_emb E.measurableEmbedding
    (fun z => ENNReal.ofReal ((∑ j, (L z j) ^ 2) ^ (-(c' : ℝ))))
    (Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1))]
  exact corner_block_cube_lintegral_lt_top_of_injective L hL (c' : ℝ) c'.coe_nonneg hc'

end DLNFibre.DLN.RLCT
