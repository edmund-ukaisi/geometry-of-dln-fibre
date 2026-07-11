import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJDetMono` — PSD determinant monotonicity (GAP-B piece 1)

**Thread `genm-sj5-schur`, B5-desc GAP-B (majorant fill).** The rebuilt Loewner-cone determinant
monotonicity `A ≼ B (PSD) ⟹ det A ≤ det B` for real symmetric matrices — the tool the m-column
Cauchy–Binet majorant needs (task #112's `det_le_det_of_posSemidef_le` was built on a lost worktree
branch, never integrated; this is the clean rebuild). Network-free, Mathlib-worthy, independently
reusable.

## What lands here (sorry-free)

* **`one_le_det_one_add_psd`** — `1 ≤ det (1 + C)` for `C` positive semidefinite. Via the spectral
  theorem: `C = U · diag(eigenvalues) · Uᴴ`, so `1 + C = U · diag(1 + eigenvalues) · Uᴴ`, whose
  determinant is `∏ (1 + eigenvalues i) ≥ 1` (the unitary conjugation is determinant-preserving,
  eigenvalues `≥ 0`).
* **`det_le_det_of_posSemidef_sub`** — `A.PosSemidef → (B - A).PosSemidef → A.det ≤ B.det`. The
  CFC square-root route: if `A` is positive definite, `S := CFC.sqrt A` is an invertible root,
  `B = S · (1 + S⁻¹(B-A)S⁻¹) · S`, and `det B = (det S)² · det(1 + C) = det A · det(1+C) ≥ det A` by
  `one_le_det_one_add_psd` (the congruence `C := S⁻¹(B-A)S⁻¹` is PSD). If `A` is singular,
  `det A = 0 ≤ det B` (both PSD).
-/

namespace DLNFibre.DLN.RLCT

open Matrix Unitary
open scoped BigOperators MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **`1 ≤ det (1 + C)` for `C` positive semidefinite** (real). Diagonalise `C = U·D·Uᴴ` (spectral
theorem, `D = diagonal (eigenvalues)`); then `1 + C = U·(1 + D)·Uᴴ`, and the unitary conjugation is
determinant-preserving, so `det (1 + C) = det (1 + D) = ∏ (1 + eigenvalues i) ≥ 1` (eigenvalues of a
PSD matrix are `≥ 0`). -/
theorem one_le_det_one_add_psd {C : Matrix n n ℝ} (hC : C.PosSemidef) :
    1 ≤ (1 + C).det := by
  have hH := hC.isHermitian
  set U := hH.eigenvectorUnitary with hU
  set d : n → ℝ := hH.eigenvalues with hd
  -- `1 + C = conjStarAlgAut U (1 + diagonal (ofReal ∘ d))`
  have hsum : (1 : Matrix n n ℝ) + C
      = conjStarAlgAut ℝ _ U ((1 : Matrix n n ℝ) + diagonal (RCLike.ofReal ∘ d)) := by
    rw [map_add, map_one, ← hH.spectral_theorem]
  rw [hsum, conjStarAlgAut_apply, det_mul, det_mul]
  -- the `1 + diagonal` part is `diagonal (fun i => 1 + d i)`, det `= ∏ (1 + d i)`
  have hdiag : (1 : Matrix n n ℝ) + diagonal (RCLike.ofReal ∘ d)
      = diagonal (fun i => 1 + d i) := by
    rw [← diagonal_one, ← diagonal_add]
    congr 1
  rw [hdiag, det_diagonal]
  -- the unitary conjugation factors cancel: `det U * det (star U) = 1`
  have hunit : (U : Matrix n n ℝ).det * (star U : Matrix n n ℝ).det = 1 := by
    rw [← det_mul, ← Unitary.coe_star, Unitary.coe_mul_star_self, det_one]
  have hprod : (1 : ℝ) ≤ ∏ i, (1 + d i) := by
    have h := Finset.prod_le_prod (s := (Finset.univ : Finset n))
      (f := fun _ => (1 : ℝ)) (g := fun i => 1 + d i)
      (fun i _ => zero_le_one) (fun i _ => by have := hC.eigenvalues_nonneg i; linarith)
    simpa using h
  calc (1 : ℝ)
      ≤ ∏ i, (1 + d i) := hprod
    _ = (∏ i, (1 + d i)) * ((U : Matrix n n ℝ).det * (star U : Matrix n n ℝ).det) := by
        rw [hunit, mul_one]
    _ = (U : Matrix n n ℝ).det * (∏ i, (1 + d i)) * (star U : Matrix n n ℝ).det := by ring

/-- **PSD determinant monotonicity (Loewner-cone).** For real symmetric matrices, if `A` is
positive semidefinite and `B - A` is positive semidefinite (i.e. `A ≼ B`), then `det A ≤ det B`. The
rebuild of task #112's `det_le_det_of_posSemidef_le` (lost worktree). CFC square-root route on the
positive-definite stratum; `det A = 0` on the singular stratum. -/
theorem det_le_det_of_posSemidef_sub {A B : Matrix n n ℝ}
    (hA : A.PosSemidef) (hsub : (B - A).PosSemidef) :
    A.det ≤ B.det := by
  have hB : B.PosSemidef := by
    have h := hsub.add hA
    rwa [show B - A + A = B from by abel] at h
  rcases hA.det_nonneg.lt_or_eq with hpos | hzero
  · -- `A` positive definite (`det A > 0`).
    have hApd : A.PosDef := by
      rw [hA.posDef_iff_isUnit, Matrix.isUnit_iff_isUnit_det]
      exact isUnit_iff_ne_zero.mpr (ne_of_gt hpos)
    set S := CFC.sqrt A with hS
    have hSpsd : S.PosSemidef := (CFC.sqrt_nonneg A).posSemidef
    have hSunit : IsUnit S := (CFC.isUnit_sqrt_iff A hA.nonneg).mpr hApd.isUnit
    letI := hSunit.invertible
    have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
    have hSinv : S * S⁻¹ = 1 := mul_inv_of_invertible S
    have hinvS : S⁻¹ * S = 1 := inv_mul_of_invertible S
    -- the congruence `C := S⁻¹ (B - A) S⁻¹` is PSD
    have hCpsd : (S⁻¹ * (B - A) * S⁻¹).PosSemidef := by
      have := hsub.mul_mul_conjTranspose_same S⁻¹
      rwa [hSpsd.isHermitian.inv.eq] at this
    -- `1 + C = S⁻¹ B S⁻¹` (since `S⁻¹ A S⁻¹ = 1`)
    have hAinv : S⁻¹ * A * S⁻¹ = 1 := by
      rw [← hSS]
      simp only [← Matrix.mul_assoc]
      rw [hinvS, Matrix.one_mul, hSinv]
    have hC_eq : (1 : Matrix n n ℝ) + S⁻¹ * (B - A) * S⁻¹ = S⁻¹ * B * S⁻¹ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, ← hAinv]; abel
    -- determinant factorisation: `det B = det A · det (1 + C)`
    have h1 : S.det * S⁻¹.det = 1 := by rw [← det_mul, hSinv, det_one]
    have hdA : A.det = S.det * S.det := by rw [← hSS, det_mul]
    have hdetB : B.det = A.det * ((1 : Matrix n n ℝ) + S⁻¹ * (B - A) * S⁻¹).det := by
      rw [hC_eq, det_mul, det_mul, hdA]
      calc B.det = (S.det * S⁻¹.det) * (S.det * S⁻¹.det) * B.det := by rw [h1]; ring
        _ = S.det * S.det * (S⁻¹.det * B.det * S⁻¹.det) := by ring
    rw [hdetB]
    nlinarith [one_le_det_one_add_psd hCpsd, hpos]
  · -- `A` singular: `det A = 0 ≤ det B`.
    rw [← hzero]
    exact hB.det_nonneg

end DLNFibre.DLN.RLCT
