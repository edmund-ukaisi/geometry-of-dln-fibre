import DLNFibre.DLN.RLCT.Validate.RouteMSchurFrameDet

/-!
# `RouteMStaircaseDet` — the staircase (block-lower-bidiagonal) determinant, iterated `lowerTri`

The linear-map-level spine of the direction-2 staircase factorization (the validated per-piece
factorization, `perpiece-factorization-answer.md`): the global interior-chart Jacobian `D(T_M)` is
**block lower-bidiagonal**, diagonal block at layer `s` = `[[DC_s, −N_{s-1}],[0,I]]`, det `det(DC_s)`. So
`det D(T_M) = ∏_s det(DC_s)`, the `−N_{s-1}` shears (det-irrelevant) landing strictly off-diagonal.

This module banks the determinant spine as ITERATED `RouteMSchurFrameDet.lowerTri` (the
`LinearMap.det_eq_det_mul_det`-on-an-invariant-subspace gluing, `prodEquivOfIsCompl`-style — the
controller's named escape from the single-grading `Matrix.BlockTriangular` partition wall,
`RouteMGradingObstruction`). Each `lowerTri` peel takes the det at the LINEAR-MAP level on a product with
possibly-distinct in/out bases, so no square-matrix single-grading is forced.

* `lowerTri3_det` — the 3-block staircase `det = f₀.det · f₁.det · f₂.det` (the couplings `h₀₁`, `h₀₂`,
  `h₁₂` det-irrelevant), via two `lowerTri_det` peels. The reusable iteration template: the opaque-M
  assembly applies `lowerTri_det` per layer with `fₛ = DC_s` (the Schur⊗LDU differential), the couplings
  the `−N`-shears.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (determinant; no analysis).
-/

open scoped BigOperators

noncomputable section

namespace DLNFibre.DLN.RLCT

variable {V₀ V₁ V₂ : Type*}
  [AddCommGroup V₀] [Module ℝ V₀] [FiniteDimensional ℝ V₀]
  [AddCommGroup V₁] [Module ℝ V₁] [FiniteDimensional ℝ V₁]
  [AddCommGroup V₂] [Module ℝ V₂] [FiniteDimensional ℝ V₂]

/-- **The 3-block staircase determinant.** A block-lower-triangular endomorphism of `V₀ × (V₁ × V₂)`
whose diagonal blocks are `f₀, f₁, f₂` and whose strictly-lower couplings are `h₀₁ : V₀ → V₁`,
`h₀₂ : V₀ → V₂` (from layer 0 into 1, 2) and `h₁₂ : V₁ → V₂` (from layer 1 into 2) has determinant
`f₀.det · f₁.det · f₂.det` — the couplings are det-irrelevant. Two `lowerTri_det` peels: the outer peels
`f₀` off `(V₁ × V₂)` (coupling `(h₀₁, h₀₂)`), the inner peels `f₁` off `V₂` (coupling `h₁₂`). The
iteration template for the opaque-`M` staircase. -/
theorem lowerTri3_det (f₀ : V₀ →ₗ[ℝ] V₀) (f₁ : V₁ →ₗ[ℝ] V₁) (f₂ : V₂ →ₗ[ℝ] V₂)
    (h₀₁ : V₀ →ₗ[ℝ] V₁) (h₀₂ : V₀ →ₗ[ℝ] V₂) (h₁₂ : V₁ →ₗ[ℝ] V₂) :
    LinearMap.det
        (lowerTri f₀ (lowerTri f₁ f₂ h₁₂)
          ((LinearMap.inl ℝ V₁ V₂ ∘ₗ h₀₁) + (LinearMap.inr ℝ V₁ V₂ ∘ₗ h₀₂)))
      = f₀.det * f₁.det * f₂.det := by
  rw [lowerTri_det, lowerTri_det, mul_assoc]

/-! ## Non-vacuity: the 3-block staircase fires on a genuine coupling -/

/-- **Non-vacuity.** On `ℝ × (ℝ × ℝ)` with diagonal blocks the scalars `a, b, c` (as `mulRight`) and
genuine nonzero couplings, the 3-block staircase det is `a·b·c` — the couplings drop out. -/
example (a b c k₀₁ k₀₂ k₁₂ : ℝ) :
    LinearMap.det
        (lowerTri (LinearMap.mulRight ℝ a)
          (lowerTri (LinearMap.mulRight ℝ b) (LinearMap.mulRight ℝ c) (LinearMap.mulRight ℝ k₁₂))
          ((LinearMap.inl ℝ ℝ ℝ ∘ₗ LinearMap.mulRight ℝ k₀₁)
            + (LinearMap.inr ℝ ℝ ℝ ∘ₗ LinearMap.mulRight ℝ k₀₂)))
      = a * b * c := by
  rw [lowerTri3_det]
  simp [LinearMap.det_ring]

end DLNFibre.DLN.RLCT
