import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Mathlib.Data.Real.StarOrdered

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJUnitsBridge` — the units-on-chart interface

**Thread `genm-sj5-desc3`, Piece 1 (encoding-independent).** The route-A leaf finiteness
`RouteMSJLeafFinite.corankLeaf_rpow_lt_top` consumes the *units interface* `Z·Zᵀ ≽ c·I` (`c > 0`).
This module supplies it from full ROW rank, `Aoyagi`/AG-free:

    Z : Matrix (Fin n) (Fin D) ℝ,  Z.rank = n  ⟹  ∃ c > 0, (Z·Zᵀ − c·1) ≽ 0.

Two elementary sub-facts (both network-free):

* **`posDef_gram_of_rank_eq`** — full ROW rank ⟹ `(Z·Zᵀ).PosDef`. Full row rank makes the rows
  linearly independent (`vecMul_injective_iff`), so `Z.vecMul` is injective, and Mathlib's
  `PosDef.mul_conjTranspose_self` gives `(Z·Zᴴ).PosDef` (over ℝ, `Zᴴ = Zᵀ`).
* **`exists_pos_smul_one_le_of_posDef`** — a positive definite matrix Loewner-dominates a positive
  multiple of `1`: `A.PosDef ⟹ ∃ c > 0, (A − c·1) ≽ 0`. Proof by minimising the Rayleigh quotient
  `x ↦ xᵀAx` over the Euclidean unit sphere `{x | x ⬝ᵥ x = 1}` (compact in `Fin n → ℝ`, a proper
  space), and extending the min by homogeneity of degree 2. **AVOIDS eigenvalues** (the
  spectral-isDefEq-timeout hazard, `lean/CLAUDE.md`) — pure compactness / homogeneity.

* **`exists_gram_sub_smul_one_posSemidef_of_rank_eq`** — the units bridge, composing the two:
  the exact `hZ` shape that `corankLeaf_rpow_lt_top` consumes.

Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped BigOperators Matrix

/-- **Full ROW rank ⟹ the rows are linearly independent.** `rank Z = n` (with `n` rows) forces the
`n` rows to span an `n`-dimensional space, hence to be independent (`Set.finrank` of the row-span
`= rank`, matched against the row count). -/
theorem linearIndependent_row_of_rank_eq {n D : ℕ} (Z : Matrix (Fin n) (Fin D) ℝ)
    (hrank : Z.rank = n) : LinearIndependent ℝ Z.row := by
  rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin, Set.finrank,
    ← Matrix.rank_eq_finrank_span_row]
  exact hrank.symm

/-- **Sub-fact (1): full ROW rank ⟹ the Gram matrix `Z·Zᵀ` is positive definite.** The rows are
independent (`linearIndependent_row_of_rank_eq`), so `Z.vecMul` is injective, and
`PosDef.mul_conjTranspose_self` gives `(Z·Zᴴ).PosDef`; over ℝ, `Zᴴ = Zᵀ`. -/
theorem posDef_gram_of_rank_eq {n D : ℕ} (Z : Matrix (Fin n) (Fin D) ℝ)
    (hrank : Z.rank = n) : (Z * Zᵀ).PosDef := by
  have hinj : Function.Injective Z.vecMul :=
    Matrix.vecMul_injective_iff.mpr (linearIndependent_row_of_rank_eq Z hrank)
  have h := Matrix.PosDef.mul_conjTranspose_self Z hinj
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- **Sub-fact (2): a positive definite matrix Loewner-dominates a positive multiple of `1`.**
`A.PosDef ⟹ ∃ c > 0, (A − c·1) ≽ 0`. The Rayleigh quotient `q x = x ⬝ᵥ (A *ᵥ x)` attains a positive
minimum `m` over the compact Euclidean unit sphere `{x | x ⬝ᵥ x = 1}`; homogeneity of degree 2 gives
`m·(x ⬝ᵥ x) ≤ q x` for all `x`, i.e. `(A − m·1) ≽ 0`. Eigenvalue-free. -/
theorem exists_pos_smul_one_le_of_posDef {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) :
    ∃ c : ℝ, 0 < c ∧ (A - c • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
  classical
  have hstar : ∀ v : Fin n → ℝ, star v = v := fun v => star_trivial v
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · -- `n = 0`: every matrix is positive semidefinite (empty index).
    subst hn0
    refine ⟨1, one_pos, ?_⟩
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun x => ?_⟩
    · funext i; exact Fin.elim0 i
    · simp [dotProduct]
  -- `n > 0`: the compact-sphere minimisation.
  set S : Set (Fin n → ℝ) := {x | x ⬝ᵥ x = 1} with hS
  -- Continuity of the Rayleigh quotient.
  have hqcont : Continuous (fun x : Fin n → ℝ => x ⬝ᵥ (A *ᵥ x)) := by
    have hmv : Continuous (fun x : Fin n → ℝ => A *ᵥ x) := by
      have := (Matrix.mulVecLin A).continuous_of_finiteDimensional
      simpa only [Matrix.mulVecLin_apply] using this
    simp only [dotProduct]
    exact continuous_finset_sum _ fun i _ =>
      (continuous_apply i).mul ((continuous_apply i).comp hmv)
  have hEcont : Continuous (fun x : Fin n → ℝ => x ⬝ᵥ x) := by
    simp only [dotProduct]
    exact continuous_finset_sum _ fun i _ => (continuous_apply i).mul (continuous_apply i)
  -- The sphere is compact (closed + bounded in a proper space).
  have hScl : IsClosed S := isClosed_eq hEcont continuous_const
  have hSbd : Bornology.IsBounded S := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := 1)).subset ?_
    intro x hx
    have hx1 : x ⬝ᵥ x = 1 := hx
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have hxi : (x i) ^ 2 ≤ 1 := by
      rw [sq, ← hx1, dotProduct]
      exact Finset.single_le_sum (f := fun j => x j * x j)
        (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i)
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    calc Real.sqrt ((x i) ^ 2) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hxi
      _ = 1 := Real.sqrt_one
  have hScompact : IsCompact S := Metric.isCompact_of_isClosed_isBounded hScl hSbd
  -- The sphere is nonempty (`n > 0`).
  have hSne : S.Nonempty := by
    refine ⟨Pi.single (⟨0, hn⟩ : Fin n) 1, ?_⟩
    simp only [hS, Set.mem_setOf_eq, dotProduct]
    rw [Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
    · rw [Pi.single_eq_same]; ring
    · intro b _ hb; rw [Pi.single_eq_of_ne hb]; ring
    · intro h; exact absurd (Finset.mem_univ _) h
  -- Minimise the Rayleigh quotient over the sphere.
  obtain ⟨x₀, hx₀S, hx₀min⟩ := hScompact.exists_isMinOn hSne hqcont.continuousOn
  have hx₀1 : x₀ ⬝ᵥ x₀ = 1 := hx₀S
  have hx₀ne : x₀ ≠ 0 := by
    intro h; rw [h, zero_dotProduct] at hx₀1; exact one_ne_zero hx₀1.symm
  set m : ℝ := x₀ ⬝ᵥ (A *ᵥ x₀) with hm_def
  have hm : 0 < m := by
    have := hA.dotProduct_mulVec_pos hx₀ne
    rwa [hstar x₀] at this
  -- The homogeneity-extended Loewner bound.
  have hbound : ∀ x : Fin n → ℝ, m * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
    intro x
    by_cases hx : x = 0
    · subst hx; simp [mulVec_zero]
    · have hEnn : (0 : ℝ) ≤ x ⬝ᵥ x := by
        rw [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
      have hEx : 0 < x ⬝ᵥ x :=
        lt_of_le_of_ne hEnn (fun h => hx (dotProduct_self_eq_zero.mp h.symm))
      set c : ℝ := (Real.sqrt (x ⬝ᵥ x))⁻¹ with hc
      have hc2E : c ^ 2 * (x ⬝ᵥ x) = 1 := by
        rw [hc, inv_pow, Real.sq_sqrt hEx.le, inv_mul_cancel₀ (ne_of_gt hEx)]
      have hyy : (c • x) ⬝ᵥ (c • x) = c ^ 2 * (x ⬝ᵥ x) := by
        rw [smul_dotProduct, dotProduct_smul]; simp only [smul_eq_mul]; ring
      have hqy : (c • x) ⬝ᵥ (A *ᵥ (c • x)) = c ^ 2 * (x ⬝ᵥ (A *ᵥ x)) := by
        rw [mulVec_smul, smul_dotProduct, dotProduct_smul]; simp only [smul_eq_mul]; ring
      have hmem : (c • x) ∈ S := by
        simp only [hS, Set.mem_setOf_eq]; rw [hyy, hc2E]
      have hle : m ≤ (c • x) ⬝ᵥ (A *ᵥ (c • x)) := (isMinOn_iff.mp hx₀min) (c • x) hmem
      rw [hqy] at hle
      calc m * (x ⬝ᵥ x) ≤ (c ^ 2 * (x ⬝ᵥ (A *ᵥ x))) * (x ⬝ᵥ x) :=
            mul_le_mul_of_nonneg_right hle hEx.le
        _ = (c ^ 2 * (x ⬝ᵥ x)) * (x ⬝ᵥ (A *ᵥ x)) := by ring
        _ = x ⬝ᵥ (A *ᵥ x) := by rw [hc2E, one_mul]
  refine ⟨m, hm, ?_⟩
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨hA.1.sub (Matrix.isHermitian_one.smul (IsSelfAdjoint.all m)), fun x => ?_⟩
  rw [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul,
    smul_eq_mul, hstar x]
  exact sub_nonneg.mpr (hbound x)

/-- **The units-on-chart interface (the `hZ` shape `corankLeaf_rpow_lt_top` consumes).** For a
full-ROW-rank real matrix `Z`, its Gram `Z·Zᵀ` dominates a positive multiple of `1`:
`Z.rank = n ⟹ ∃ c > 0, (Z·Zᵀ − c·1) ≽ 0`. Composes `posDef_gram_of_rank_eq` (Gram PosDef) with
`exists_pos_smul_one_le_of_posDef` (Loewner lower bound). -/
theorem exists_gram_sub_smul_one_posSemidef_of_rank_eq {n D : ℕ} (Z : Matrix (Fin n) (Fin D) ℝ)
    (hrank : Z.rank = n) :
    ∃ c : ℝ, 0 < c ∧ (Z * Zᵀ - c • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef :=
  exists_pos_smul_one_le_of_posDef (Z * Zᵀ) (posDef_gram_of_rank_eq Z hrank)

end DLNFibre.DLN.RLCT
