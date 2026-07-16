import DLNFibre.DLN.RLCT.Validate.RouteMSJGramResidual

set_option linter.style.longLine false

/-!
# `RouteMSchurWishartWeight` — the b-general charge-weight (Wishart) finiteness

The shallow-cell charge-weight bound for the CHARGED corank recursion (couplerad §w3-atlas): for a `b×m`
matrix `B` (`b ≤ m`), the matrix-variate integral `∫_{B∈matBox b m T} det(B·Bᵀ)^{−a/2}` is finite when
`a < m − b + 1` (corneradj's confirmed threshold, at the rank-`m` floor). The `b=1` case is the banked
`corankWeight_lt_top`; general `b` peels one row via the banked Gram-det row-residual recursion
`RouteMSJGramResidual.det_gram_cons` (`det(gram(cons w u)) = det(gram u)·‖P_{V⊥}w‖²`), reducing to the
lower-`b` weight times a projection-radial integral `∫_w ‖P_{V⊥}w‖^{−a}` (finite for `a < dim V⊥`,
`dim V⊥ ≥ m−(b−1)`). Non-spectral.

## Status: building bottom-up. Landed: `det_mulTranspose_eq_det_gram` (the Gram bridge — the entry point).
-/

open Matrix
open scoped Matrix InnerProductSpace BigOperators

namespace DLNFibre.DLN.RLCT

/-- **Gram bridge.** `det(B·Bᵀ)` equals the determinant of the Gram matrix of `B`'s rows viewed as
Euclidean vectors — the entry point to the banked `det_gram_cons` row-residual recursion. -/
theorem det_mulTranspose_eq_det_gram {b m : ℕ} (B : Fin b → Fin m → ℝ) :
    ((Matrix.of B) * (Matrix.of B)ᵀ).det
      = (Matrix.gram ℝ (fun i => (WithLp.equiv 2 (Fin m → ℝ)).symm (B i))).det := by
  congr 1
  ext i j
  rw [Matrix.gram_apply,
    show ⟪(WithLp.equiv 2 (Fin m → ℝ)).symm (B i), (WithLp.equiv 2 (Fin m → ℝ)).symm (B j)⟫_ℝ
        = (B j) ⬝ᵥ star (B i) from rfl,
    Matrix.mul_apply]
  simp only [dotProduct, star_trivial, Matrix.transpose_apply, Matrix.of_apply]
  exact Finset.sum_congr rfl (fun k _ => by ring)

end DLNFibre.DLN.RLCT
