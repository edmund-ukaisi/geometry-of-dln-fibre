import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Matrix.Order

/-!
# `Core.Matrix.OrthoRowComplement` — an orthonormal complement of the row space

A network-free engine brick. A full-row-rank real matrix `F : Matrix (Fin m) (Fin n) ℝ` (encoded by
`det (F * Fᵀ) ≠ 0`, the nonvanishing of the Gram determinant of its rows) admits an orthonormal
complement `S : Matrix (Fin (n - m)) (Fin n) ℝ` of its row space, stacked as rows: `S * Fᵀ = 0`
(each row of `S` is orthogonal to every row of `F`) and `S * Sᵀ = 1` (the rows of `S` are
orthonormal).
-/

open Matrix
open scoped Matrix InnerProductSpace

namespace DLNFibre

/-- A full-row-rank real matrix admits an orthonormal complement of its row space, stacked as rows:
`S * Fᵀ = 0` and `S * Sᵀ = 1`. -/
theorem exists_ortho_complement_rows {m n : ℕ} (hmn : m ≤ n)
    (F : Matrix (Fin m) (Fin n) ℝ) (hFdet : (F * Fᵀ).det ≠ 0) :
    ∃ S : Matrix (Fin (n - m)) (Fin n) ℝ, S * Fᵀ = 0 ∧ S * Sᵀ = 1 := by
  classical
  -- The rows of `F`, viewed as Euclidean vectors.
  set rowF : Fin m → EuclideanSpace ℝ (Fin n) := fun i => WithLp.toLp 2 (F i) with hrowF
  -- The Gram matrix of the rows equals `F * Fᵀ`.
  have hgram : Matrix.gram ℝ rowF = F * Fᵀ := by
    ext i j
    simp only [hrowF, Matrix.gram_apply, PiLp.inner_apply, Matrix.mul_apply,
      Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  -- `det ≠ 0` on the Gram, so the Gram is positive definite, so the rows are linearly independent.
  have hpsd : (Matrix.gram ℝ rowF).PosSemidef := Matrix.posSemidef_gram ℝ rowF
  have hdet_gram : (Matrix.gram ℝ rowF).det ≠ 0 := by rw [hgram]; exact hFdet
  have hpd : (Matrix.gram ℝ rowF).PosDef :=
    hpsd.posDef_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hdet_gram.isUnit)
  have hli : LinearIndependent ℝ rowF := Matrix.posDef_gram_iff_linearIndependent.mp hpd
  -- The span `V` of the rows has dimension `m`; its orthogonal complement has dimension `n - m`.
  set V : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := Submodule.span ℝ (Set.range rowF) with hV
  have hfinrankV : Module.finrank ℝ V = m := by
    rw [hV, finrank_span_eq_card hli, Fintype.card_fin]
  have hfinrankPerp : Module.finrank ℝ Vᗮ = n - m := by
    apply Submodule.finrank_add_finrank_orthogonal' (K := V)
    rw [hfinrankV, finrank_euclideanSpace_fin]
    omega
  -- An orthonormal basis of `Vᗮ`, reindexed to `Fin (n - m)`.
  let b := (stdOrthonormalBasis ℝ (Vᗮ)).reindex (finCongr hfinrankPerp)
  -- `S`: row `i` is the `i`-th basis vector read out in ambient coordinates.
  refine ⟨Matrix.of (fun i j => (b i : EuclideanSpace ℝ (Fin n)) j), ?_, ?_⟩
  · -- `S * Fᵀ = 0`: each row of `S` lies in `Vᗮ`, each row of `F` lies in `V`.
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.zero_apply]
    have horth : (⟪rowF j, (b i : EuclideanSpace ℝ (Fin n))⟫_ℝ) = 0 :=
      Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self j)) (b i).2
    simp only [hrowF, PiLp.inner_apply] at horth
    exact horth
  · -- `S * Sᵀ = 1`: orthonormality of the basis.
    ext i i'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply]
    have hb := (orthonormal_iff_ite (𝕜 := ℝ)).mp b.orthonormal i i'
    simp only [Submodule.coe_inner, PiLp.inner_apply] at hb
    rw [← hb]
    exact Finset.sum_congr rfl fun x _ => mul_comm _ _

end DLNFibre
