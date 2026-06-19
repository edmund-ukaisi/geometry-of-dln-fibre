import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod

/-!
# Aoyagi block-elimination identities

This file formalises the algebraic block identities and rank consequence in
Aoyagi's Lemma 2.
-/

noncomputable section

open Matrix

namespace DLNFibre
namespace DLN
namespace Aoyagi

section Identities

variable {K : Type*} [CommRing K]

/-- Left block elimination exposes the Schur complement in the lower-right block. -/
theorem schurComplement_leftBlockElim_fromBlocks {r p q : ℕ}
    (A1 : Matrix (Fin r) (Fin r) K) (A2 : Matrix (Fin r) (Fin q) K)
    (A3 : Matrix (Fin p) (Fin r) K) (A4 : Matrix (Fin p) (Fin q) K)
    (hA1 : IsUnit A1.det) :
    fromBlocks (1 : Matrix (Fin r) (Fin r) K) 0 (-(A3 * A1⁻¹)) 1
        * fromBlocks A1 A2 A3 A4 =
      fromBlocks A1 A2 0 (A4 - A3 * A1⁻¹ * A2) := by
  rw [fromBlocks_multiply]
  simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA1, sub_eq_add_neg, add_comm]

/-- Two-sided block elimination produces a block diagonal matrix with Schur complement. -/
theorem schurComplement_blockElim_fromBlocks {r p q : ℕ}
    (A1 : Matrix (Fin r) (Fin r) K) (A2 : Matrix (Fin r) (Fin q) K)
    (A3 : Matrix (Fin p) (Fin r) K) (A4 : Matrix (Fin p) (Fin q) K)
    (hA1 : IsUnit A1.det) :
    fromBlocks (1 : Matrix (Fin r) (Fin r) K) 0 (-(A3 * A1⁻¹)) 1
        * fromBlocks A1 A2 A3 A4
        * fromBlocks (1 : Matrix (Fin r) (Fin r) K) (-(A1⁻¹ * A2)) 0 1 =
      fromBlocks A1 0 0 (A4 - A3 * A1⁻¹ * A2) := by
  rw [schurComplement_leftBlockElim_fromBlocks A1 A2 A3 A4 hA1]
  rw [fromBlocks_multiply]
  simp [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left A1 A2 hA1, sub_eq_add_neg]

/-- Indexed left block elimination exposes the Schur complement in the lower-right block. -/
theorem schurComplement_leftBlockElim_fromBlocks_indexed
    {ρ μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype μ] [DecidableEq μ]
    (A1 : Matrix ρ ρ K) (A2 : Matrix ρ ν K)
    (A3 : Matrix μ ρ K) (A4 : Matrix μ ν K)
    (hA1 : IsUnit A1.det) :
    fromBlocks (1 : Matrix ρ ρ K) 0 (-(A3 * A1⁻¹)) 1
        * fromBlocks A1 A2 A3 A4 =
      fromBlocks A1 A2 0 (A4 - A3 * A1⁻¹ * A2) := by
  rw [fromBlocks_multiply]
  simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA1, sub_eq_add_neg, add_comm]

/-- Indexed two-sided block elimination produces a block diagonal matrix. -/
theorem schurComplement_blockElim_fromBlocks_indexed
    {ρ μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype μ] [DecidableEq μ]
    [Fintype ν] [DecidableEq ν]
    (A1 : Matrix ρ ρ K) (A2 : Matrix ρ ν K)
    (A3 : Matrix μ ρ K) (A4 : Matrix μ ν K)
    (hA1 : IsUnit A1.det) :
    fromBlocks (1 : Matrix ρ ρ K) 0 (-(A3 * A1⁻¹)) 1
        * fromBlocks A1 A2 A3 A4
        * fromBlocks (1 : Matrix ρ ρ K) (-(A1⁻¹ * A2)) 0 1 =
      fromBlocks A1 0 0 (A4 - A3 * A1⁻¹ * A2) := by
  rw [schurComplement_leftBlockElim_fromBlocks_indexed A1 A2 A3 A4 hA1]
  rw [fromBlocks_multiply]
  simp [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left A1 A2 hA1, sub_eq_add_neg]

end Identities

section Rank

variable {K : Type*} [Field K]

/-- The product submodule is linearly equivalent to the product of the two submodules. -/
private def submoduleProdLinearEquiv {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module K M] [Module K N] (p : Submodule K M) (q : Submodule K N) :
    p.prod q ≃ₗ[K] p × q where
  toFun x :=
    ⟨⟨x.1.1, (Submodule.mem_prod.mp x.2).1⟩,
      ⟨x.1.2, (Submodule.mem_prod.mp x.2).2⟩⟩
  invFun x := ⟨(x.1.1, x.2.1), Submodule.mem_prod.mpr ⟨x.1.2, x.2.2⟩⟩
  left_inv x := by ext <;> rfl
  right_inv x := by ext <;> rfl
  map_add' x y := by ext <;> rfl
  map_smul' c x := by ext <;> rfl

/-- The `finrank` of a product submodule is the sum of the two `finrank`s. -/
private theorem finrank_submodule_prod {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module K M] [Module K N] (p : Submodule K M) (q : Submodule K N)
    [Module.Finite K p] [Module.Finite K q] :
    Module.finrank K (p.prod q) = Module.finrank K p + Module.finrank K q := by
  rw [(submoduleProdLinearEquiv p q).finrank_eq, Module.finrank_prod]

/-- The rank of a block diagonal matrix is the sum of the ranks of its diagonal blocks. -/
theorem rank_fromBlocks_zero_zero {m n p q : Type*} [Fintype n] [Fintype q]
    (A : Matrix m n K) (B : Matrix p q K) :
    (fromBlocks A 0 0 B).rank = A.rank + B.rank := by
  let Ec := LinearEquiv.sumArrowLequivProdArrow n q K K
  let Er := LinearEquiv.sumArrowLequivProdArrow m p K K
  let f := (fromBlocks A 0 0 B).mulVecLin
  let g := A.mulVecLin.prodMap B.mulVecLin
  have hfg : Er.toLinearMap.comp f = g.comp Ec.toLinearMap := by
    ext x i <;> simp [Ec, Er, f, g, fromBlocks_mulVec, Matrix.mulVec, dotProduct,
      Function.comp_def]
  rw [Matrix.rank, Matrix.rank, Matrix.rank]
  calc
    Module.finrank K (LinearMap.range f)
        = Module.finrank K (Submodule.map Er.toLinearMap (LinearMap.range f)) :=
          (LinearEquiv.finrank_map_eq Er _).symm
    _ = Module.finrank K (LinearMap.range (Er.toLinearMap.comp f)) := by
      rw [LinearMap.range_comp]
    _ = Module.finrank K (LinearMap.range (g.comp Ec.toLinearMap)) := by
      rw [hfg]
    _ = Module.finrank K (LinearMap.range g) := by
      rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
    _ = Module.finrank K (LinearMap.range A.mulVecLin)
          + Module.finrank K (LinearMap.range B.mulVecLin) := by
      change Module.finrank K (LinearMap.range (A.mulVecLin.prodMap B.mulVecLin)) = _
      rw [LinearMap.range_prodMap, finrank_submodule_prod]

/-- On Aoyagi's invertible chart, matrix rank is the corner size plus Schur-complement rank. -/
theorem rank_fromBlocks_eq_card_add_rank_schurComplement_of_isUnit_det {r p q : ℕ}
    (A1 : Matrix (Fin r) (Fin r) K) (A2 : Matrix (Fin r) (Fin q) K)
    (A3 : Matrix (Fin p) (Fin r) K) (A4 : Matrix (Fin p) (Fin q) K)
    (hA1 : IsUnit A1.det) :
    (fromBlocks A1 A2 A3 A4).rank = r + (A4 - A3 * A1⁻¹ * A2).rank := by
  let Q1 : Matrix (Fin r ⊕ Fin p) (Fin r ⊕ Fin p) K :=
    fromBlocks (1 : Matrix (Fin r) (Fin r) K) 0 (-(A3 * A1⁻¹)) 1
  let Q2 : Matrix (Fin r ⊕ Fin q) (Fin r ⊕ Fin q) K :=
    fromBlocks (1 : Matrix (Fin r) (Fin r) K) (-(A1⁻¹ * A2)) 0 1
  let M : Matrix (Fin r ⊕ Fin p) (Fin r ⊕ Fin q) K := fromBlocks A1 A2 A3 A4
  let C : Matrix (Fin p) (Fin q) K := A4 - A3 * A1⁻¹ * A2
  have hQ1det : IsUnit Q1.det := by
    exact (Matrix.isUnit_iff_isUnit_det (A := Q1)).mp
      ((Matrix.isUnit_fromBlocks_zero₁₂).2 ⟨isUnit_one, isUnit_one⟩)
  have hQ2det : IsUnit Q2.det := by
    exact (Matrix.isUnit_iff_isUnit_det (A := Q2)).mp
      ((Matrix.isUnit_fromBlocks_zero₂₁).2 ⟨isUnit_one, isUnit_one⟩)
  have hMrank : (Q1 * M * Q2).rank = M.rank := by
    rw [Matrix.rank_mul_eq_left_of_isUnit_det Q2 (Q1 * M) hQ2det,
      Matrix.rank_mul_eq_right_of_isUnit_det Q1 M hQ1det]
  have hblock : Q1 * M * Q2 = fromBlocks A1 0 0 C := by
    simpa [Q1, Q2, M, C] using schurComplement_blockElim_fromBlocks A1 A2 A3 A4 hA1
  calc
    (fromBlocks A1 A2 A3 A4).rank = (Q1 * M * Q2).rank := by
      rw [hMrank]
    _ = (fromBlocks A1 0 0 C).rank := by rw [hblock]
    _ = A1.rank + C.rank := rank_fromBlocks_zero_zero A1 C
    _ = r + C.rank := by
      rw [Matrix.rank_of_isUnit A1 ((Matrix.isUnit_iff_isUnit_det (A := A1)).mpr hA1),
        Fintype.card_fin]

end Rank

end Aoyagi
end DLN
end DLNFibre
