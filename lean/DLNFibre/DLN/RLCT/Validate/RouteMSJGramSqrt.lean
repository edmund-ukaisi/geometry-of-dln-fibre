import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJGramSqrt` — the Gram normaliser (piece (a) of the Γ-atom)

The inverse Gram square-root `M = G^{−1/2}` for a positive-definite `G` (in the Γ-atom, `G = R Rᵀ`
with `R` full row rank), built from the CFC matrix square root (`CFC.sqrt`, `Analysis/Matrix/Order`).
`M` is the change-of-variables matrix that normalises the anisotropic corank form to isotropic:
`M G Mᵀ = 1` (so `M·R` has orthonormal rows), with Jacobian `|det M| = (det G)^{−1/2}`.

This isolates the heavy `Analysis/Matrix/Order` (CStarAlgebra CFC) import from the rest of the peel
stack. It is piece (a) of the anisotropic-shifted Γ-atom (`RouteMSJGammaAtom`).
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped BigOperators MatrixOrder

/-- **The Gram normaliser (piece (a)).** For a positive-definite `G : Matrix (Fin q) (Fin q) ℝ`,
there is a symmetric `M` (`= G^{−1/2}`) with `M G Mᵀ = 1` (so any `R` with `R Rᵀ = G` has `(M R)` of
orthonormal rows), `det M ≠ 0`, and `|det M| = (Real.sqrt (det G))⁻¹ = (det G)^{−1/2}`. Built from the
CFC square root `CFC.sqrt G`: `sqrt·sqrt = G` (`CFC.sq_sqrt`), symmetric + invertible (posdef, det
`= √(det G) > 0` via `Matrix.PosSemidef.det_sqrt`), inverse via `nonsing_inv`. -/
theorem exists_gram_normalizer {q : ℕ} (G : Matrix (Fin q) (Fin q) ℝ) (hG : G.PosDef) :
    ∃ M : Matrix (Fin q) (Fin q) ℝ,
      Mᵀ = M ∧ M * G * Mᵀ = 1 ∧ M.det ≠ 0 ∧ |M.det| = (Real.sqrt G.det)⁻¹ := by
  classical
  have hGps : G.PosSemidef := hG.posSemidef
  -- det G > 0
  have hGdet_pos : 0 < G.det :=
    lt_of_le_of_ne hGps.det_nonneg
      (Ne.symm ((Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit).ne_zero)
  -- the CFC square root `S = G^{1/2}` and its facts
  have hSps : (CFC.sqrt G).PosSemidef := (CFC.sqrt_nonneg G).posSemidef
  have hST : (CFC.sqrt G)ᵀ = CFC.sqrt G := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hSps.isHermitian.eq
  have hSsq : CFC.sqrt G * CFC.sqrt G = G := CFC.sqrt_mul_sqrt_self G
  have hSdet : (CFC.sqrt G).det = Real.sqrt G.det := by
    rw [hGps.det_sqrt, RCLike.sqrt_real]
  have hSdet_pos : 0 < (CFC.sqrt G).det := by rw [hSdet]; exact Real.sqrt_pos.mpr hGdet_pos
  have hSunit : IsUnit (CFC.sqrt G).det := (isUnit_iff_ne_zero).mpr (ne_of_gt hSdet_pos)
  -- M = S⁻¹ = G^{-1/2}
  refine ⟨(CFC.sqrt G)⁻¹, ?_, ?_, ?_, ?_⟩
  · -- (S⁻¹)ᵀ = S⁻¹
    rw [Matrix.transpose_nonsing_inv, hST]
  · -- S⁻¹ * G * (S⁻¹)ᵀ = 1
    rw [Matrix.transpose_nonsing_inv, hST]
    calc (CFC.sqrt G)⁻¹ * G * (CFC.sqrt G)⁻¹
        = (CFC.sqrt G)⁻¹ * (CFC.sqrt G * CFC.sqrt G) * (CFC.sqrt G)⁻¹ := by rw [hSsq]
      _ = 1 := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul (CFC.sqrt G) hSunit, Matrix.one_mul,
            Matrix.mul_nonsing_inv (CFC.sqrt G) hSunit]
  · -- (S⁻¹).det ≠ 0
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, hSdet]
    exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr hGdet_pos))
  · -- |(S⁻¹).det| = (√ det G)⁻¹
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, hSdet, abs_inv,
      abs_of_nonneg (Real.sqrt_nonneg _)]

end DLNFibre.DLN.RLCT
