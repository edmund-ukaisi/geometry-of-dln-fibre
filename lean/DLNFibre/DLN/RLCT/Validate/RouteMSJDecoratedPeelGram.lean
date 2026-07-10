import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedPeelGram` — full row rank ⟹ Gram PosDef

**Thread `genm-decbuild`, piece-8 minimal prerequisite (Cauchy-Binet-FREE).** The good stratum
corner cover is `{rank Q_b = b}` (full row rank), on which the Γ-peel (Regime A) needs
`(Q_b Q_bᵀ).PosDef`. This supplies that from the rank alone: the quadratic form is `x ↦ ‖Q_bᵀ x‖²`,
strictly positive off `ker Q_bᵀ = ⊥` (full row rank ⟹ `Q_bᵀ` injective, by rank-nullity). The
Gram weight `det(Q_bQ_bᵀ)^{−a/2}` is then handled by the banked CFC Gram normaliser, not by a
`det = Σ minors²` decomposition — `PosDef` needs only strict positivity.

S2-FREE: pure linear algebra over the banked Mathlib PosDef/Rank API. Axiom-clean
`[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped BigOperators

/-- **Full row rank ⟹ Gram PosDef.** For `Q_b : b × q` over `ℝ` with `rank Q_b = b`,
`Q_b Q_bᵀ` is positive-definite: the quadratic form `x ⬝ᵥ (Q_bQ_bᵀ *ᵥ x) = ‖Q_bᵀ x‖²` is `> 0` for
`x ≠ 0` because `Q_bᵀ` is injective (full column rank `b`, by rank-nullity). No Cauchy-Binet. -/
theorem posDef_gram_of_rank_full {b q : ℕ} (Qb : Matrix (Fin b) (Fin q) ℝ) (hrank : Qb.rank = b) :
    (Qb * Qbᵀ).PosDef := by
  -- Hermitian (real symmetric): `(Qb Qbᵀ)ᴴ = Qb Qbᵀ` entrywise.
  have hHerm : (Qb * Qbᵀ).IsHermitian := by
    show (Qb * Qbᵀ)ᴴ = Qb * Qbᵀ
    ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
  -- `Qbᵀ.mulVecLin` is injective: full column rank `b` = domain dimension, so `ker = ⊥`.
  have hrankT : Qbᵀ.rank = b := by rw [Matrix.rank_transpose]; exact hrank
  have hker : LinearMap.ker (Matrix.mulVecLin Qbᵀ) = ⊥ := by
    have hrange : Module.finrank ℝ (LinearMap.range (Matrix.mulVecLin Qbᵀ)) = b := hrankT
    have hsum := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin Qbᵀ)
    have hdom : Module.finrank ℝ (Fin b → ℝ) = b := by simp
    have hkerdim : Module.finrank ℝ (LinearMap.ker (Matrix.mulVecLin Qbᵀ)) = 0 := by
      rw [hrange, hdom] at hsum; omega
    exact Submodule.finrank_eq_zero.mp hkerdim
  refine (Matrix.posDef_iff_dotProduct_mulVec).mpr ⟨hHerm, ?_⟩
  intro x hx
  have hstar : star x = x := by ext i; exact star_trivial _
  have hy : Qbᵀ *ᵥ x ≠ 0 := by
    intro h0
    apply hx
    have hmem : x ∈ LinearMap.ker (Matrix.mulVecLin Qbᵀ) := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact h0
    rw [hker] at hmem
    exact (Submodule.mem_bot ℝ).mp hmem
  have hquad : x ⬝ᵥ ((Qb * Qbᵀ) *ᵥ x) = (Qbᵀ *ᵥ x) ⬝ᵥ (Qbᵀ *ᵥ x) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  have hnn : 0 ≤ (Qbᵀ *ᵥ x) ⬝ᵥ (Qbᵀ *ᵥ x) :=
    Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hne : (Qbᵀ *ᵥ x) ⬝ᵥ (Qbᵀ *ᵥ x) ≠ 0 :=
    fun h => hy (dotProduct_self_eq_zero.mp h)
  rw [hstar, hquad]
  exact lt_of_le_of_ne hnn (Ne.symm hne)

end DLNFibre.DLN.RLCT
