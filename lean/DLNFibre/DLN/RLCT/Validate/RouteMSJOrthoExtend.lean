import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# `RouteMSJOrthoExtend` — orthogonal extension of a matrix with orthonormal columns

**Thread `genm-sj5-domination`, T-Obl3b mountain, OWED-2 support.** A matrix `U_s : M₂×m` with
`U_sᵀ U_s = 1` (orthonormal columns) extends to a square **orthogonal** matrix whose first `m`
columns are `U_s`. This is the crux of the corrected corner-shrink's reduced-weight finiteness
(OWED-2 `strongBlock_lintegral_lt_top`): after extending to `U ∈ O(M₂)`, right-multiplication
`A ↦ A U` is a measure-preserving change of variables and `A U_s = (A U)|_{first m cols}`.

Network-free (pure Mathlib inner-product-space + matrix), reusable.
-/

namespace DLNFibre.DLN.RLCT

open Matrix Finset
open scoped InnerProductSpace

/-- **Orthogonal extension.** A real matrix `U_s : M₂×m` with orthonormal columns (`U_sᵀ U_s = 1`)
extends to a square orthogonal matrix `U : M₂×M₂` (`Uᵀ U = 1`) whose first `m` columns are `U_s`
(`U.submatrix id (Fin.castLE hmM) = U_s`). Via `exists_orthonormalBasis_extension_of_card_eq` on
the columns of `U_s` viewed as an orthonormal family in `EuclideanSpace ℝ (Fin M₂)`. -/
theorem exists_ortho_ext {M₂ m : ℕ} (hmM : m ≤ M₂) (U_s : Matrix (Fin M₂) (Fin m) ℝ)
    (hUs : U_sᵀ * U_s = 1) :
    ∃ U : Matrix (Fin M₂) (Fin M₂) ℝ, Uᵀ * U = 1 ∧ U.submatrix id (Fin.castLE hmM) = U_s := by
  classical
  set v : Fin m → EuclideanSpace ℝ (Fin M₂) := fun k => WithLp.toLp 2 (fun i => U_s i k) with hv
  have hinner : ∀ k l, (inner ℝ (v k) (v l) : ℝ) = (U_sᵀ * U_s) l k := by
    intro k l
    have h : (inner ℝ (v k) (v l) : ℝ) = (fun i => U_s i l) ⬝ᵥ star (fun i => U_s i k) :=
      EuclideanSpace.inner_toLp_toLp (fun i => U_s i k) (fun i => U_s i l)
    rw [h]
    simp only [dotProduct, Pi.star_apply, star_trivial, Matrix.mul_apply, Matrix.transpose_apply]
  have hon : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]; intro k l; rw [hinner, hUs]; simp [Matrix.one_apply, eq_comm]
  set castm : Fin m ↪ Fin M₂ := Fin.castLEEmb hmM with hcastm
  have hcard : Module.finrank ℝ (EuclideanSpace ℝ (Fin M₂)) = Fintype.card (Fin M₂) := by
    rw [finrank_euclideanSpace_fin, Fintype.card_fin]
  set v' : Fin M₂ → EuclideanSpace ℝ (Fin M₂) :=
    fun i => if h : ∃ k, castm k = i then v h.choose else 0 with hv'
  have hv'castm : ∀ k, v' (castm k) = v k := by
    intro k
    have hex : ∃ k', castm k' = castm k := ⟨k, rfl⟩
    simp only [hv', dif_pos hex]; congr 1; exact castm.injective hex.choose_spec
  have hres : Orthonormal ℝ ((Set.range castm).restrict v') := by
    rw [orthonormal_iff_ite]
    rintro ⟨_, k, rfl⟩ ⟨_, l, rfl⟩
    simp only [Set.restrict_apply, hv'castm]
    rw [orthonormal_iff_ite.mp hon k l]
    simp [Subtype.ext_iff, castm.injective.eq_iff]
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard hres
  refine ⟨Matrix.of fun i j => (b j) i, ?_, ?_⟩
  · ext j l
    have hbon := b.orthonormal
    rw [orthonormal_iff_ite] at hbon
    have hbb : (inner ℝ (b j) (b l) : ℝ) = (fun i => (b l) i) ⬝ᵥ star (fun i => (b j) i) :=
      EuclideanSpace.inner_toLp_toLp ((b j)) ((b l))
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply]
    rw [← hbon j l, hbb]
    simp only [dotProduct, Pi.star_apply, star_trivial]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · ext i k
    simp only [Matrix.submatrix_apply, Matrix.of_apply, id_eq]
    have hbk : b (castm k) = v k := by rw [hb (castm k) ⟨k, rfl⟩, hv'castm]
    show (b (Fin.castLE hmM k)) i = U_s i k
    rw [show (Fin.castLE hmM k) = castm k from rfl, hbk]

end DLNFibre.DLN.RLCT
