import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered

/-!
# `RouteMSJBorderedGram` — the bordered-Gram / Schur-complement determinant recursion

**Thread `genm-sj5-domination`, T-Obl3b mountain (bordered-Gram route).** The one genuinely-new
determinant primitive the corner-shrink change-of-variables needs: peeling the last vector off a
Gram matrix multiplies the determinant by the Schur complement of the leading block. This is
strictly smaller than full Cauchy–Binet — no sum over `b×b` minors — and rests directly on
Mathlib's `Matrix.det_fromBlocks₁₁` (Schur-complement determinant) + `Matrix.gram`.

The re-formulation cert (`tobl3b-reformulation-cert.md`) adjudicated the iterated-single-direction
spectral route dead for a corank block of width `b > 1` (trace ≠ det: `frobSq^{−c'}` cannot
dominate `det^{−a/2}`), and pinned this bordered-Gram recursion as the correct native primitive.

## What lands here (sorry-free)

* **`borderedGramSchur`** — the `(1×1)` Schur-complement scalar `⟪x,x⟫ − w ⬝ᵥ (G⁻¹ *ᵥ w)`, where
  `x = v (last)`, `w j = ⟪v (castSucc j), x⟫`, and `G = gram ℝ (v ∘ castSucc)` is the leading Gram
  of the first `n` vectors.
* **`borderedGram_det`** — the recursion: for `v : Fin (n+1) → E` whose first `n` vectors
  `v ∘ castSucc` are linearly independent,
  `(gram ℝ v).det = (gram ℝ (v ∘ castSucc)).det * borderedGramSchur v`. Via `det_fromBlocks₁₁` on
  the bordered Gram `[[G, w], [wᵀ, ⟪x,x⟫]]` (leading block invertible from linear independence).
* **`borderedGramSchur_nonneg`** — the Schur complement is `≥ 0`: the full Gram is positive
  semidefinite, so its Schur complement w.r.t. the positive-definite leading block is positive
  semidefinite, hence the scalar is nonnegative. This is the load-bearing sign fact for the
  corner-shrink domination (drop the nonneg residual).

Network-free, reusable, Mathlib-worthy.
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- The cross inner-product vector: `w j = ⟪v (castSucc j), v (last n)⟫` — the inner products of the
first `n` vectors with the last one. -/
noncomputable def borderedCross (v : Fin (n + 1) → E) : Fin n → ℝ :=
  fun j => (⟪v j.castSucc, v (Fin.last n)⟫_ℝ)

/-- The `(1×1)` Schur-complement scalar of the bordered Gram matrix: `⟪x,x⟫ − w ⬝ᵥ (G⁻¹ *ᵥ w)`
where `x = v (last n)`, `w = borderedCross v`, `G = gram ℝ (v ∘ castSucc)`. -/
noncomputable def borderedGramSchur (v : Fin (n + 1) → E) : ℝ :=
  (⟪v (Fin.last n), v (Fin.last n)⟫_ℝ)
    - borderedCross v ⬝ᵥ ((gram ℝ (v ∘ Fin.castSucc))⁻¹ *ᵥ borderedCross v)

/-- `finSumFinEquiv` sends the left summand to `castSucc`. -/
private lemma finSum_inl (i : Fin n) :
    (finSumFinEquiv (Sum.inl i) : Fin (n + 1)) = i.castSucc := by
  simp [finSumFinEquiv_apply_left]
  rfl

/-- `finSumFinEquiv` sends the (unique) right summand to `last`. -/
private lemma finSum_inr (i : Fin 1) :
    (finSumFinEquiv (Sum.inr i) : Fin (n + 1)) = Fin.last n := by
  fin_cases i
  simp [finSumFinEquiv_apply_right]
  rfl

/-- The bordered-block decomposition of the Gram matrix: reindexing `gram ℝ v` by
`finSumFinEquiv` produces the block matrix `[[G, w], [wᵀ, ⟪x,x⟫]]`. -/
private lemma gram_submatrix_eq_fromBlocks (v : Fin (n + 1) → E) :
    (gram ℝ v).submatrix finSumFinEquiv finSumFinEquiv
      = fromBlocks (gram ℝ (v ∘ Fin.castSucc))
          (Matrix.of fun (i : Fin n) (_ : Fin 1) => borderedCross v i)
          (Matrix.of fun (_ : Fin 1) (j : Fin n) => borderedCross v j)
          (Matrix.of fun (_ _ : Fin 1) => (⟪v (Fin.last n), v (Fin.last n)⟫_ℝ)) := by
  ext a b
  rcases a with i | i <;> rcases b with j | j <;>
    simp only [Matrix.submatrix_apply, finSum_inl, finSum_inr, fromBlocks_apply₁₁,
      fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, gram_apply,
      Function.comp_apply, Matrix.of_apply, borderedCross]
  · exact real_inner_comm _ _

/-- **The bordered-Gram / Schur-complement determinant recursion.** For `v : Fin (n+1) → E` whose
first `n` vectors `v ∘ castSucc` are linearly independent, peeling the last vector multiplies the
Gram determinant by the Schur complement:
`(gram ℝ v).det = (gram ℝ (v ∘ castSucc)).det * borderedGramSchur v`.
Via `Matrix.det_fromBlocks₁₁` on the bordered Gram `[[G, w], [wᵀ, ⟪x,x⟫]]` (leading block
invertible from linear independence). -/
theorem borderedGram_det (v : Fin (n + 1) → E)
    (hli : LinearIndependent ℝ (v ∘ Fin.castSucc)) :
    (gram ℝ v).det = (gram ℝ (v ∘ Fin.castSucc)).det * borderedGramSchur v := by
  set G := gram ℝ (v ∘ Fin.castSucc) with hG
  set w := borderedCross v with hw
  set x := v (Fin.last n) with hx
  letI : Invertible G := (posDef_gram_of_linearIndependent hli).isUnit.invertible
  -- reindex to the block form and expand the block determinant
  have hdet : (gram ℝ v).det
      = det (fromBlocks G
          (Matrix.of fun (i : Fin n) (_ : Fin 1) => w i)
          (Matrix.of fun (_ : Fin 1) (j : Fin n) => w j)
          (Matrix.of fun (_ _ : Fin 1) => (⟪x, x⟫_ℝ))) := by
    rw [← det_submatrix_equiv_self finSumFinEquiv (gram ℝ v),
      gram_submatrix_eq_fromBlocks v]
  rw [hdet, det_fromBlocks₁₁, det_fin_one]
  congr 1
  -- identify the (0,0) Schur entry with `borderedGramSchur`
  rw [borderedGramSchur, ← hG, ← hw, ← hx]
  simp only [Matrix.sub_apply, Matrix.of_apply, invOf_eq_nonsing_inv]
  congr 1
  -- `(C * G⁻¹ * B) 0 0 = w ⬝ᵥ (G⁻¹ *ᵥ w)`
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct]

/-- **The Schur complement is nonnegative.** The full Gram is positive semidefinite
(`posSemidef_gram`); its Schur complement w.r.t. the positive-definite leading block
(`posDef_gram_of_linearIndependent`) is positive semidefinite, so the scalar `borderedGramSchur`
— its unique diagonal entry — is `≥ 0`. The sign fact the corner-shrink domination consumes. -/
theorem borderedGramSchur_nonneg (v : Fin (n + 1) → E)
    (hli : LinearIndependent ℝ (v ∘ Fin.castSucc)) :
    0 ≤ borderedGramSchur v := by
  set G := gram ℝ (v ∘ Fin.castSucc) with hG
  set w := borderedCross v with hw
  set x := v (Fin.last n) with hx
  have hApd : G.PosDef := posDef_gram_of_linearIndependent hli
  letI : Invertible G := hApd.isUnit.invertible
  set B : Matrix (Fin n) (Fin 1) ℝ := Matrix.of fun i _ => w i with hB
  set D : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of fun _ _ => (⟪x, x⟫_ℝ) with hD
  -- the row block is `Bᴴ`
  have hCB : (Matrix.of fun (_ : Fin 1) (j : Fin n) => w j) = Bᴴ := by
    ext a c; simp [hB, Matrix.conjTranspose_apply]
  -- the full bordered block is positive semidefinite
  have hblkPSD : (fromBlocks G B Bᴴ D).PosSemidef := by
    have hgpsd : (gram ℝ v).PosSemidef := posSemidef_gram ℝ v
    have := (posSemidef_submatrix_equiv (M := gram ℝ v) finSumFinEquiv).mpr hgpsd
    rw [gram_submatrix_eq_fromBlocks v, hCB] at this
    exact this
  -- Schur complement is PSD
  have hschurPSD : (D - Bᴴ * G⁻¹ * B).PosSemidef :=
    (Matrix.PosDef.fromBlocks₁₁ B D hApd).mp hblkPSD
  -- its unique diagonal entry is `borderedGramSchur v`
  have hentry : (D - Bᴴ * G⁻¹ * B) 0 0 = borderedGramSchur v := by
    rw [borderedGramSchur, ← hG, ← hw, ← hx]
    simp only [Matrix.sub_apply, hD, hB, Matrix.of_apply]
    congr 1
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.mulVec, dotProduct, star_trivial]
  have := hschurPSD.diag_nonneg (i := 0)
  rwa [hentry] at this

end DLNFibre.DLN.RLCT
