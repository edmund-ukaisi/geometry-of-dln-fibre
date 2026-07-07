import DLNFibre.DLN.RLCT.Validate.RouteMSJCorankResidual
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJGammaAtom` — the anisotropic-shifted corank Γ-atom

The **anisotropic** generalisation of `matBox_corank_residual_fullSpace_eq`: the full-space integral of
`(w + ‖Γ·R + S‖²)^{−c'}` over the corank block `Γ : Fin p → Fin q → ℝ`, where the block couples to the
tail bottom-rows through a general `R : Fin q → Fin n → ℝ` and shift `S : Fin p → Fin n → ℝ`. This is
Aoyagi's per-boundary exponent-shift step (design cert `genm-sjjoint-design`, step 2): the corank block
peels at threshold `pq/2`, contributing the coupling Jacobian `det(R Rᵀ)^{−p/2}` and leaving the core
at the shifted exponent `c' ↦ c' − pq/2`.

## The build (bottom-up)

1. **The right-multiplication operator's determinant (the cov Jacobian crux).** `Γ ↦ Γ · M` on
   `Fin p → Fin q → ℝ` is the `p`-fold diagonal of the single-row map `v ↦ v ᵥ* M = Mᵀ.mulVecLin v`;
   `LinearMap.det_pi` + `Matrix.det_toLin'` give `det = (det M)^p`. (This file, `det_rightMulₚ`.)
2. **The measure change of variables.** `map_linearMap_addHaar_eq_smul_addHaar` on the finite-dim
   `Fin p → Fin q → ℝ` turns the operator into a `|det M|^{−p}` scaling of `volume`, hence a `lintegral`
   change of variables. (This file.)
3. **The Gram reduction + isotropic endpoint** (the remaining anisotropic content): `RRᵀ` posdef →
   invertible sqrt, the cov `Γ ↦ Γ·G^{-1/2}`, the projection `I − P_R`, and the banked isotropic
   endpoint `matBox_corank_residual_fullSpace_eq`. (In progress — see the module header notes.)
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped BigOperators ENNReal

/-! ## Step 1 — the right-multiplication operator and its determinant (the cov Jacobian crux) -/

/-- **Right multiplication `Γ ↦ Γ · M` as a linear endomorphism of `Fin p → Fin q → ℝ`.** Realised as
the `p`-fold diagonal `LinearMap.pi (fun i ↦ (Mᵀ.mulVecLin) ∘ proj i)` — each row `Γ i` maps by
`v ↦ v ᵥ* M = Mᵀ.mulVecLin v`. -/
noncomputable def rightMulₚ (p : ℕ) {q : ℕ} (M : Matrix (Fin q) (Fin q) ℝ) :
    (Fin p → Fin q → ℝ) →ₗ[ℝ] (Fin p → Fin q → ℝ) :=
  LinearMap.pi (fun i : Fin p =>
    (Mᵀ.mulVecLin).comp (LinearMap.proj (R := ℝ) (φ := fun _ : Fin p => Fin q → ℝ) i))

/-- `rightMulₚ` acts as right multiplication by `M` on each row: `(rightMulₚ M Γ) i = Γ i ᵥ* M`. -/
theorem rightMulₚ_apply (p : ℕ) {q : ℕ} (M : Matrix (Fin q) (Fin q) ℝ)
    (Γ : Fin p → Fin q → ℝ) (i : Fin p) : rightMulₚ p M Γ i = Γ i ᵥ* M := by
  simp only [rightMulₚ, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Matrix.mulVecLin_apply]
  exact Matrix.mulVec_transpose M (Γ i)

/-- **The cov Jacobian crux — `det (Γ ↦ Γ·M) = (det M)^p`.** The `p`-fold diagonal determinant
(`LinearMap.det_pi`) of the single-row map `v ↦ v ᵥ* M = Mᵀ.mulVecLin v = Matrix.toLin' Mᵀ`
(`det_toLin'`, then `det_transpose`), giving `∏_{i : Fin p} det Mᵀ = (det M)^p`. -/
theorem det_rightMulₚ (p : ℕ) {q : ℕ} (M : Matrix (Fin q) (Fin q) ℝ) :
    LinearMap.det (rightMulₚ p M) = (Matrix.det M) ^ p := by
  rw [rightMulₚ, LinearMap.det_pi]
  have hrow : ∀ _ : Fin p, LinearMap.det (Mᵀ.mulVecLin) = Matrix.det M := by
    intro _
    rw [show Mᵀ.mulVecLin = Matrix.toLin' Mᵀ from (Matrix.toLin'_apply' Mᵀ).symm,
      LinearMap.det_toLin', Matrix.det_transpose]
  rw [Finset.prod_congr rfl (fun i _ => hrow i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-! ## Step 2 — the `lintegral` change of variables under `Γ ↦ Γ · M` -/

/-- **The `lintegral` change of variables `Γ ↦ Γ · M` (invertible `M`).** For a measurable
`ℝ≥0∞`-integrand `g` on `Fin p → Fin q → ℝ` and `det M ≠ 0`, precomposing with right-multiplication
by `M` scales the full-space integral by the reciprocal Jacobian `|det M|^{−p}`:

    ∫⁻ Γ, g (fun i ↦ Γ i ᵥ* M)  =  ofReal (|det M|^p)⁻¹ · ∫⁻ Γ, g Γ.

`map_linearMap_addHaar_eq_smul_addHaar` (the Haar scaling of the finite-dim linear cov, Jacobian
`det (rightMulₚ M) = (det M)^p` by `det_rightMulₚ`) + `lintegral_map` + `lintegral_smul_measure`. -/
theorem lintegral_comp_rightMulₚ (p : ℕ) {q : ℕ} (M : Matrix (Fin q) (Fin q) ℝ) (hM : M.det ≠ 0)
    (g : (Fin p → Fin q → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ Γ : Fin p → Fin q → ℝ, g (fun i => Γ i ᵥ* M)
      = ENNReal.ofReal (|M.det| ^ p)⁻¹ * ∫⁻ Γ : Fin p → Fin q → ℝ, g Γ := by
  have hdet : LinearMap.det (rightMulₚ p M) ≠ 0 := by
    rw [det_rightMulₚ]; exact pow_ne_zero _ hM
  have hfmeas : Measurable (rightMulₚ p M) :=
    (rightMulₚ p M).continuous_of_finiteDimensional.measurable
  -- rewrite the precomposed integrand through `rightMulₚ`
  have hcomp : (fun Γ : Fin p → Fin q → ℝ => g (fun i => Γ i ᵥ* M))
      = fun Γ => g (rightMulₚ p M Γ) := by
    funext Γ; congr 1; funext i; rw [rightMulₚ_apply]
  rw [hcomp]
  -- `lintegral_map` : ∫ y, g y ∂(map f vol) = ∫ Γ, g (f Γ) ∂vol
  rw [← lintegral_map hg hfmeas,
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet,
    lintegral_smul_measure, det_rightMulₚ,
    show |((M.det) ^ p)⁻¹| = (|M.det| ^ p)⁻¹ from by rw [abs_inv, abs_pow], smul_eq_mul]

end DLNFibre.DLN.RLCT
