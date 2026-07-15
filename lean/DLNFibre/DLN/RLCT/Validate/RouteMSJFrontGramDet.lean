import DLNFibre.DLN.RLCT.Validate.RouteMSJFrontGram

set_option linter.style.longLine false

/-!
# `RouteMSJFrontGramDet` — the front-Gram determinant `det Σ = ∏(pᵢ²+σⱼ²)` (module (ii)(b))

**Thread `genm-sj5-stepbuild` (aoyagi-full Stage 2), step-3 module (ii)(b)** — the determinant of the
D–H covariance `Σ = frontGram P D = I_b⊗(PPᵀ) + (DᵀD)⊗I_u` (design §2.2). The honest joint weight of the
pushforward density is `(det Σ)^{−1/2} = ∏(pᵢ²+σⱼ²)^{−1/2}` (`pᵢ, σⱼ` the singular values of `P, D`).

Because the two Kronecker factors COMMUTE (`frontGram_factors_commute`, module (ii)(a)), `Σ` is
simultaneously diagonalised by `U = W ⊗ V` (`V, W` diagonalising `PPᵀ, DᵀD`), and

    det Σ = ∏_{j,i} (αᵢ + βⱼ),   αᵢ = eigenvalues(PPᵀ) = pᵢ²,  βⱼ = eigenvalues(DᵀD) = σⱼ².

`kroneckerSum_det_eq_prod` is the reusable heart (abstract `V, W, α, β` — no spectral terms, whnf-safe);
`frontGram_det_eq_prod` specialises it to `frontGram P D` given ANY orthogonal diagonalisation of
`PPᵀ, DᵀD` (the consumer supplies the spectral theorem, whose eigenvalues are the singular-value squares).
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped Kronecker BigOperators

/-- **Determinant of a Kronecker sum of two abstractly-diagonalised factors** —
`det(I_b⊗(V·diagα·Vᵀ) + (W·diagβ·Wᵀ)⊗I_u) = ∏_{j,i}(αᵢ+βⱼ)` for orthogonal `V` (`VVᵀ=VᵀV=1`), `W`.
The joint conjugator `U = W⊗V` is orthogonal and simultaneously diagonalises both Kronecker terms
(mixed product `mul_kronecker_mul` + `VᵀV=1`, `WᵀW=1`), landing the conjugated sum at
`diagonal((j,i) ↦ αᵢ+βⱼ)`; `det` is conjugation-invariant. The whnf-safe heart of the front-Gram
determinant (no spectral terms). -/
theorem kroneckerSum_det_eq_prod {u b : ℕ}
    (V : Matrix (Fin u) (Fin u) ℝ) (W : Matrix (Fin b) (Fin b) ℝ)
    (α : Fin u → ℝ) (β : Fin b → ℝ)
    (hVo' : Vᵀ * V = 1) (hWo' : Wᵀ * W = 1) :
    (((1 : Matrix (Fin b) (Fin b) ℝ) ⊗ₖ (V * Matrix.diagonal α * Vᵀ))
        + ((W * Matrix.diagonal β * Wᵀ) ⊗ₖ (1 : Matrix (Fin u) (Fin u) ℝ))).det
      = ∏ j : Fin b, ∏ i : Fin u, (α i + β j) := by
  -- the conjugated pivot blocks reduce to the diagonals
  have hA : Vᵀ * (V * Matrix.diagonal α * Vᵀ) * V = Matrix.diagonal α := by
    rw [← Matrix.mul_assoc Vᵀ (V * Matrix.diagonal α) Vᵀ,
      ← Matrix.mul_assoc Vᵀ V (Matrix.diagonal α), hVo', Matrix.one_mul,
      Matrix.mul_assoc (Matrix.diagonal α) Vᵀ V, hVo', Matrix.mul_one]
  have hB : Wᵀ * (W * Matrix.diagonal β * Wᵀ) * W = Matrix.diagonal β := by
    rw [← Matrix.mul_assoc Wᵀ (W * Matrix.diagonal β) Wᵀ,
      ← Matrix.mul_assoc Wᵀ W (Matrix.diagonal β), hWo', Matrix.one_mul,
      Matrix.mul_assoc (Matrix.diagonal β) Wᵀ W, hWo', Matrix.mul_one]
  -- conjugate each Kronecker term by `U = W ⊗ V`
  have hterm1 : (W ⊗ₖ V)ᵀ
        * ((1 : Matrix (Fin b) (Fin b) ℝ) ⊗ₖ (V * Matrix.diagonal α * Vᵀ)) * (W ⊗ₖ V)
      = (1 : Matrix (Fin b) (Fin b) ℝ) ⊗ₖ Matrix.diagonal α := by
    rw [transpose_kronecker', ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, hWo', hA]
  have hterm2 : (W ⊗ₖ V)ᵀ
        * ((W * Matrix.diagonal β * Wᵀ) ⊗ₖ (1 : Matrix (Fin u) (Fin u) ℝ)) * (W ⊗ₖ V)
      = Matrix.diagonal β ⊗ₖ (1 : Matrix (Fin u) (Fin u) ℝ) := by
    rw [transpose_kronecker', ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, hVo', hB]
  -- the two diagonal-Kronecker collapses
  have hd1 : (1 : Matrix (Fin b) (Fin b) ℝ) ⊗ₖ Matrix.diagonal α
      = Matrix.diagonal (fun ji : Fin b × Fin u => α ji.2) := by
    rw [← Matrix.diagonal_one, diagonal_kronecker_diagonal]
    congr 1; funext ji; simp
  have hd2 : (Matrix.diagonal β) ⊗ₖ (1 : Matrix (Fin u) (Fin u) ℝ)
      = Matrix.diagonal (fun ji : Fin b × Fin u => β ji.1) := by
    rw [← Matrix.diagonal_one, diagonal_kronecker_diagonal]
    congr 1; funext ji; simp
  -- the conjugated sum is diagonal
  have hconj : (W ⊗ₖ V)ᵀ
        * (((1 : Matrix (Fin b) (Fin b) ℝ) ⊗ₖ (V * Matrix.diagonal α * Vᵀ))
            + ((W * Matrix.diagonal β * Wᵀ) ⊗ₖ (1 : Matrix (Fin u) (Fin u) ℝ)))
        * (W ⊗ₖ V)
      = Matrix.diagonal (fun ji : Fin b × Fin u => α ji.2 + β ji.1) := by
    rw [Matrix.mul_add, Matrix.add_mul, hterm1, hterm2, hd1, hd2, Matrix.diagonal_add]
  -- `U` is orthogonal, so det is conjugation-invariant
  have hUtU : (W ⊗ₖ V)ᵀ * (W ⊗ₖ V) = 1 := by
    rw [transpose_kronecker', ← mul_kronecker_mul, hWo', hVo', one_kronecker_one]
  have hUdet : (W ⊗ₖ V)ᵀ.det * (W ⊗ₖ V).det = 1 := by
    rw [← Matrix.det_mul, hUtU, Matrix.det_one]
  set M := ((1 : Matrix (Fin b) (Fin b) ℝ) ⊗ₖ (V * Matrix.diagonal α * Vᵀ))
      + ((W * Matrix.diagonal β * Wᵀ) ⊗ₖ (1 : Matrix (Fin u) (Fin u) ℝ)) with hM
  calc M.det
      = M.det * ((W ⊗ₖ V)ᵀ.det * (W ⊗ₖ V).det) := by rw [hUdet, mul_one]
    _ = (W ⊗ₖ V)ᵀ.det * M.det * (W ⊗ₖ V).det := by ring
    _ = ((W ⊗ₖ V)ᵀ * M * (W ⊗ₖ V)).det := by rw [Matrix.det_mul, Matrix.det_mul]
    _ = (Matrix.diagonal (fun ji : Fin b × Fin u => α ji.2 + β ji.1)).det := by rw [hconj]
    _ = ∏ ji : Fin b × Fin u, (α ji.2 + β ji.1) := Matrix.det_diagonal
    _ = ∏ j : Fin b, ∏ i : Fin u, (α i + β j) := Fintype.prod_prod_type _

/-- **The front-Gram determinant `det Σ = ∏_{j,i}(αᵢ+βⱼ)`** — given ANY orthogonal diagonalisation
`P Pᵀ = V·diagα·Vᵀ`, `Dᵀ D = W·diagβ·Wᵀ` (the spectral theorem, supplied by the consumer, gives
`αᵢ = eigenvalues(PPᵀ) = pᵢ²`, `βⱼ = eigenvalues(DᵀD) = σⱼ²`), the covariance determinant is the joint
eigenvalue-sum product `∏(pᵢ²+σⱼ²)`. Its `−1/2` power is the honest pushforward density weight
(module (ii)(b), design §2.2). Specialises `kroneckerSum_det_eq_prod` at the frontGram Kronecker sum. -/
theorem frontGram_det_eq_prod {u b : ℕ}
    (P : Matrix (Fin u) (Fin u) ℝ) (D : Matrix (Fin b) (Fin b) ℝ)
    (V : Matrix (Fin u) (Fin u) ℝ) (W : Matrix (Fin b) (Fin b) ℝ) (α : Fin u → ℝ) (β : Fin b → ℝ)
    (hP : P * Pᵀ = V * Matrix.diagonal α * Vᵀ) (hD : Dᵀ * D = W * Matrix.diagonal β * Wᵀ)
    (hVo' : Vᵀ * V = 1) (hWo' : Wᵀ * W = 1) :
    (frontGram P D).det = ∏ j : Fin b, ∏ i : Fin u, (α i + β j) := by
  rw [frontGram, hP, hD]
  exact kroneckerSum_det_eq_prod V W α β hVo' hWo'

end DLNFibre.DLN.RLCT
