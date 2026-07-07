import DLNFibre.DLN.RLCT.Validate.RouteMSJCorankResidual
import DLNFibre.DLN.RLCT.Validate.RouteMSJGramSqrt
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Group.LIntegral

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

/-! ## Step 3a — the Frobenius/trace bridge and the orthonormal-shear decomposition (piece (b)) -/

/-- **The Frobenius–trace bridge** `frobSq X = (X · Xᵀ).trace`. The squared Frobenius norm is the
trace of `X Xᵀ` (`∑ᵢ (X Xᵀ)ᵢᵢ = ∑ᵢ ∑ⱼ Xᵢⱼ²`). Reusable. -/
theorem frobSq_eq_trace {p q : ℕ} (X : Matrix (Fin p) (Fin q) ℝ) :
    frobSq X = (X * Xᵀ).trace := by
  unfold frobSq Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, pow_two]

/-- **The anisotropic orthonormal-shear decomposition (piece (b)).** For `U` with orthonormal rows
(`U Uᵀ = 1`) and a residual block `B` orthogonal to the row space (`B Uᵀ = 0`),
`frobSq (A·U + B) = frobSq A + frobSq B`. Trace algebra: expand `(A U + B)(A U + B)ᵀ`; the diagonal
term is `A (U Uᵀ) Aᵀ = A Aᵀ` and both cross terms vanish (`U Bᵀ = (B Uᵀ)ᵀ = 0`, `B Uᵀ = 0`). -/
theorem frobSq_mul_orthonormal_add {p q n : ℕ} (U : Matrix (Fin q) (Fin n) ℝ)
    (hU : U * Uᵀ = 1) (A : Matrix (Fin p) (Fin q) ℝ) (B : Matrix (Fin p) (Fin n) ℝ)
    (hB : B * Uᵀ = 0) : frobSq (A * U + B) = frobSq A + frobSq B := by
  have hUB : U * Bᵀ = 0 := by
    have h := congrArg Matrix.transpose hB
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] at h
  have hAU : A * U * (Uᵀ * Aᵀ) = A * Aᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc U Uᵀ Aᵀ, hU, Matrix.one_mul]
  have hterm2 : A * U * Bᵀ = 0 := by rw [Matrix.mul_assoc, hUB, Matrix.mul_zero]
  have hterm3 : B * (Uᵀ * Aᵀ) = 0 := by rw [← Matrix.mul_assoc, hB, Matrix.zero_mul]
  rw [frobSq_eq_trace, frobSq_eq_trace A, frobSq_eq_trace B, Matrix.transpose_add,
    Matrix.transpose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.trace_add,
    Matrix.trace_add, Matrix.trace_add, hAU, hterm2, hterm3]
  simp only [Matrix.trace_zero, add_zero, zero_add]

/-! ## Step 3b — the assembled anisotropic-shifted Γ-atom (piece (c)) -/

/-- **The anisotropic-shifted corank Γ-atom (EXACT), clean full-rank slice.** For `R` of full row
rank (`G := R Rᵀ` positive definite), a shift `S`, `c'` above the block threshold `pq/2`, and a
strictly-positive core `w > 0`,

    ∫_{Γ ∈ ℝ^{p×q}} (w + ‖Γ·R + S‖²)^{−c'} dΓ
      = det(R Rᵀ)^{−p/2} · Cresid(pq) c' · (w + ‖S·(I − P_R)‖²)^{−(c' − pq/2)},

where `P_R = Rᵀ (R Rᵀ)⁻¹ R` is the orthogonal projection onto the row space of `R` and `‖·‖²` is
`frobSq`. The Gram change of variables `Γ ↦ Γ·G^{−1/2}` (banked cov `lintegral_comp_rightMulₚ`,
Jacobian `|det G^{−1/2}|^p = det(R Rᵀ)^{−p/2}`) reduces the anisotropic form to `frobSq (Γ·U + S)`
with `U = G^{−1/2} R` orthonormal-rowed (`U Uᵀ = 1`, `exists_gram_normalizer`); the shear
decomposition (`frobSq_mul_orthonormal_add`) splits off the constant residual `‖S·(I − Uᵀ U)‖²` and
translation-invariance (`lintegral_add_right_eq_self`) + the banked isotropic endpoint
(`matBox_corank_residual_fullSpace_eq`) close the isotropic core. The projection identity
`Uᵀ U = Rᵀ (R Rᵀ)⁻¹ R` (from `M M = (R Rᵀ)⁻¹`) puts the residual in `R`-terms.

This is the exponent shift `c' ↦ c' − pq/2` at block dimension `a = pq`. Scoped to the full-rank
slice: `R Rᵀ` posdef is the a.e. generic-top-layer condition; degenerate rank-drop strata route
through the `(S,J)` R-blowup, not this atom. -/
theorem gammaAtom_aniso_shifted_eq {p q n : ℕ} (R : Matrix (Fin q) (Fin n) ℝ)
    (S : Matrix (Fin p) (Fin n) ℝ) (hG : (R * Rᵀ).PosDef) (c' : ℝ)
    (hc' : (p * q : ℝ) / 2 < c') (w : ℝ) (hw : 0 < w) :
    ∫⁻ Γ : Fin p → Fin q → ℝ,
        ENNReal.ofReal ((w + frobSq ((Matrix.of Γ) * R + S)) ^ (-c'))
      = ENNReal.ofReal ((R * Rᵀ).det ^ (-(p : ℝ) / 2) * Cresid (p * q) c'
          * (w + frobSq (S * (1 - Rᵀ * (R * Rᵀ)⁻¹ * R))) ^ (-(c' - (p * q : ℝ) / 2))) := by
  classical
  obtain ⟨M, hMsymm, hMGM, hMdet, hMabs⟩ := exists_gram_normalizer (R * Rᵀ) hG
  have hMunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hMdet
  have hd : 0 < (R * Rᵀ).det :=
    lt_of_le_of_ne hG.posSemidef.det_nonneg
      (Ne.symm ((Matrix.isUnit_iff_isUnit_det (R * Rᵀ)).mp hG.isUnit).ne_zero)
  -- U = M R has orthonormal rows
  set U : Matrix (Fin q) (Fin n) ℝ := M * R with hUdef
  have hUUt : U * Uᵀ = 1 := by
    rw [hUdef, Matrix.transpose_mul, Matrix.mul_assoc M R (Rᵀ * Mᵀ), ← Matrix.mul_assoc R Rᵀ Mᵀ,
      ← Matrix.mul_assoc M (R * Rᵀ) Mᵀ]
    exact hMGM
  have hBUt : S * (1 - Uᵀ * U) * Uᵀ = 0 := by
    rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc Uᵀ U Uᵀ, hUUt,
      Matrix.mul_one, sub_self, Matrix.mul_zero]
  have hAUB : ∀ Γ : Matrix (Fin p) (Fin q) ℝ,
      (Γ + S * Uᵀ) * U + S * (1 - Uᵀ * U) = Γ * U + S := by
    intro Γ
    rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc S Uᵀ U]
    abel
  -- projection identity Uᵀ U = Rᵀ (R Rᵀ)⁻¹ R  (via M M = (R Rᵀ)⁻¹)
  have hMGM2 : M * (R * Rᵀ) * M = 1 := by have h := hMGM; rwa [hMsymm] at h
  have hMG : M * (R * Rᵀ) = M⁻¹ := by
    have h2 : M * (R * Rᵀ) * M * M⁻¹ = 1 * M⁻¹ := by rw [hMGM2]
    rwa [Matrix.mul_assoc (M * (R * Rᵀ)) M M⁻¹, Matrix.mul_nonsing_inv M hMunit, Matrix.mul_one,
      Matrix.one_mul] at h2
  have hMMG : M * M * (R * Rᵀ) = 1 := by
    rw [Matrix.mul_assoc, hMG, Matrix.mul_nonsing_inv M hMunit]
  have hMM : M * M = (R * Rᵀ)⁻¹ := (Matrix.inv_eq_left_inv hMMG).symm
  have hUtU : Uᵀ * U = Rᵀ * (R * Rᵀ)⁻¹ * R := by
    rw [hUdef, Matrix.transpose_mul, hMsymm, Matrix.mul_assoc Rᵀ M (M * R),
      ← Matrix.mul_assoc M M R, hMM, ← Matrix.mul_assoc]
  -- the shifted core value w'' = w + ‖S (I − Uᵀ U)‖²
  set w'' : ℝ := w + frobSq (S * (1 - Uᵀ * U)) with hw''def
  have hw'' : 0 < w'' := by rw [hw''def]; exact add_pos_of_pos_of_nonneg hw (frobSq_nonneg _)
  have hdecomp : ∀ Γ : Matrix (Fin p) (Fin q) ℝ,
      frobSq (Γ * U + S) = frobSq (Γ + S * Uᵀ) + frobSq (S * (1 - Uᵀ * U)) := by
    intro Γ
    rw [← hAUB Γ]
    exact frobSq_mul_orthonormal_add U hUUt (Γ + S * Uᵀ) (S * (1 - Uᵀ * U)) hBUt
  -- value of the U-integral: decomposition + translation + banked endpoint
  have hIU : (∫⁻ Γ : Fin p → Fin q → ℝ,
        ENNReal.ofReal ((w + frobSq ((Matrix.of Γ) * U + S)) ^ (-c')))
      = ENNReal.ofReal (Cresid (p * q) c' * w'' ^ (-(c' - (p * q : ℝ) / 2))) := by
    have hstep1 : (∫⁻ Γ : Fin p → Fin q → ℝ,
          ENNReal.ofReal ((w + frobSq ((Matrix.of Γ) * U + S)) ^ (-c')))
        = ∫⁻ Γ : Fin p → Fin q → ℝ,
          ENNReal.ofReal ((w'' + frobSq ((Matrix.of Γ) + S * Uᵀ)) ^ (-c')) := by
      refine lintegral_congr (fun Γ => ?_)
      have hreal : w + frobSq ((Matrix.of Γ) * U + S)
          = w'' + frobSq ((Matrix.of Γ) + S * Uᵀ) := by
        rw [hdecomp (Matrix.of Γ), hw''def]; ring
      rw [hreal]
    have hstep2 : (∫⁻ Γ : Fin p → Fin q → ℝ,
          ENNReal.ofReal ((w'' + frobSq ((Matrix.of Γ) + S * Uᵀ)) ^ (-c')))
        = ∫⁻ Γ : Fin p → Fin q → ℝ,
          ENNReal.ofReal ((w'' + frobSq Γ) ^ (-c')) :=
      lintegral_add_right_eq_self
        (fun Γ : Fin p → Fin q → ℝ =>
          ENNReal.ofReal ((w'' + frobSq Γ) ^ (-c'))) (S * Uᵀ)
    have hstep3 : (∫⁻ Γ : Fin p → Fin q → ℝ,
          ENNReal.ofReal ((w'' + frobSq Γ) ^ (-c')))
        = ENNReal.ofReal (Cresid (p * q) c' * w'' ^ (-(c' - (p * q : ℝ) / 2))) := by
      rw [← matBox_corank_residual_fullSpace_eq p q c' hc' w'' hw'']
      refine lintegral_congr (fun Γ => ?_)
      rw [add_comm (frobSq Γ) w'']
    rw [hstep1, hstep2, hstep3]
  -- the change of variables Γ ↦ Γ M (Jacobian |det M|^p = det(R Rᵀ)^{−p/2})
  have hrow : ∀ Γ : Fin p → Fin q → ℝ,
      Matrix.of (fun i => Γ i ᵥ* M) = (Matrix.of Γ) * M := by
    intro Γ; funext i; exact (Matrix.mul_apply_eq_vecMul (Matrix.of Γ) M i).symm
  have hargR : ∀ Γ : Fin p → Fin q → ℝ,
      (Matrix.of (fun i => Γ i ᵥ* M)) * R
        = (Matrix.of Γ) * U := by
    intro Γ; rw [hrow Γ, Matrix.mul_assoc, ← hUdef]
  have hgmeas : Measurable (fun Θ : Fin p → Fin q → ℝ =>
      ENNReal.ofReal ((w + frobSq ((Matrix.of Θ) * R + S)) ^ (-c'))) := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
    unfold frobSq
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  have hpos : (0 : ℝ) < |M.det| ^ p := pow_pos (abs_pos.mpr hMdet) p
  have hdetbridge : |M.det| ^ p = (R * Rᵀ).det ^ (-(p : ℝ) / 2) := by
    rw [hMabs, Real.sqrt_eq_rpow, ← Real.rpow_neg hd.le, ← Real.rpow_natCast _ p,
      ← Real.rpow_mul hd.le]
    congr 1; ring
  have hcov_eq : (∫⁻ Γ : Fin p → Fin q → ℝ,
        ENNReal.ofReal ((w + frobSq ((Matrix.of Γ) * R + S)) ^ (-c')))
      = ENNReal.ofReal (|M.det| ^ p) * ∫⁻ Γ : Fin p → Fin q → ℝ,
        ENNReal.ofReal ((w + frobSq ((Matrix.of Γ) * U + S)) ^ (-c')) := by
    set g : (Fin p → Fin q → ℝ) → ℝ≥0∞ :=
      fun Θ => ENNReal.ofReal ((w + frobSq ((Matrix.of Θ) * R + S)) ^ (-c')) with hgdef
    have hcov := lintegral_comp_rightMulₚ p M hMdet g hgmeas
    have he1 : (∫⁻ Γ : Fin p → Fin q → ℝ, g (fun i => Γ i ᵥ* M))
        = ∫⁻ Γ : Fin p → Fin q → ℝ,
          ENNReal.ofReal ((w + frobSq ((Matrix.of Γ) * U + S)) ^ (-c')) := by
      refine lintegral_congr (fun Γ => ?_)
      rw [hgdef]
      change ENNReal.ofReal ((w + frobSq ((Matrix.of (fun i => Γ i ᵥ* M)) * R + S)) ^ (-c'))
        = ENNReal.ofReal ((w + frobSq ((Matrix.of Γ) * U + S)) ^ (-c'))
      rw [hargR Γ]
    have hstep : (∫⁻ Γ : Fin p → Fin q → ℝ, g Γ)
        = ENNReal.ofReal (|M.det| ^ p) * ∫⁻ Γ : Fin p → Fin q → ℝ, g (fun i => Γ i ᵥ* M) := by
      rw [hcov, ← mul_assoc, ← ENNReal.ofReal_mul hpos.le, mul_inv_cancel₀ (ne_of_gt hpos),
        ENNReal.ofReal_one, one_mul]
    change (∫⁻ Γ : Fin p → Fin q → ℝ, g Γ)
        = ENNReal.ofReal (|M.det| ^ p) * ∫⁻ Γ : Fin p → Fin q → ℝ,
          ENNReal.ofReal ((w + frobSq ((Matrix.of Γ) * U + S)) ^ (-c'))
    rw [hstep, he1]
  calc (∫⁻ Γ : Fin p → Fin q → ℝ,
          ENNReal.ofReal ((w + frobSq ((Matrix.of Γ) * R + S)) ^ (-c')))
      = ENNReal.ofReal (|M.det| ^ p)
          * ENNReal.ofReal (Cresid (p * q) c' * w'' ^ (-(c' - (p * q : ℝ) / 2))) := by
        rw [hcov_eq, hIU]
    _ = ENNReal.ofReal (|M.det| ^ p * (Cresid (p * q) c' * w'' ^ (-(c' - (p * q : ℝ) / 2)))) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal ((R * Rᵀ).det ^ (-(p : ℝ) / 2) * Cresid (p * q) c'
          * (w + frobSq (S * (1 - Rᵀ * (R * Rᵀ)⁻¹ * R))) ^ (-(c' - (p * q : ℝ) / 2))) := by
        rw [hdetbridge, hw''def, hUtU]; congr 1; ring

end DLNFibre.DLN.RLCT
