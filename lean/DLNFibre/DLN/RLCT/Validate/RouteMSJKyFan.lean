import DLNFibre.DLN.RLCT.Validate.RouteMSJShellCover
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option linter.style.longLine false

/-!
# `RouteMSJKyFan` — the shell⊆G containment via a dimension-counting eigenspace argument (Brick D-C)

**Thread `genm-sj5` (aoyagi-full Stage 2), Brick D-C.** The reusable spectral core the head-split
domination consumes for the containment: on the shell `{A'₀·Z_deep ∈ singularShell ε r j}`, the deep factor
`Z_deep` has `weakEigCount ε' Z_deep ≤ M₂ − m`. Mathlib v4.29 has NO min-max / Courant–Fischer / Weyl
monotonicity / threshold eigenvalue-count↔subspace-dim, so this is built from scratch as a **dimension-
counting eigenspace** argument (avoiding the abstract Ky-Fan σ_m inequality), connected directly to
`weakEigCount`'s sorted Gram eigenvalues:

* **`rayleigh_expansion`** — `⟪x, H x⟫ = ∑ᵢ λᵢ·⟪bᵢ,x⟫²` in the orthonormal eigenbasis (the linchpin).
* **`sum_sq_inner_eigenvectorBasis`** — Parseval `‖x‖² = ∑ᵢ ⟪bᵢ,x⟫²`.
* **`finrank_add_weakCount_le`** — the counting core: a subspace `U` with Rayleigh `≥ c` meets the weak
  eigenspace `{eigenvectors : λ < c}` trivially, so `finrank U + #{λ<c} ≤ k`
  (`Submodule.finrank_sup_add_finrank_inf_eq`).

Network-free spectral linear algebra. Axiom target `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped BigOperators

variable {k : ℕ}

/-- The matrix operator on `EuclideanSpace` sends the `i`-th eigenvector to `λᵢ` times itself. -/
theorem toEuclideanLin_eigenvectorBasis (H : Matrix (Fin k) (Fin k) ℝ) (hH : H.IsHermitian)
    (i : Fin k) :
    Matrix.toEuclideanLin H (hH.eigenvectorBasis i) = hH.eigenvalues i • hH.eigenvectorBasis i := by
  apply (WithLp.addEquiv 2 (Fin k → ℝ)).injective
  rw [WithLp.coe_addEquiv, Matrix.ofLp_toEuclideanLin_apply, WithLp.ofLp_smul]
  exact hH.mulVec_eigenvectorBasis i

/-- **The Rayleigh expansion in the orthonormal eigenbasis.** `⟪x, H x⟫ = ∑ᵢ λᵢ · ⟪bᵢ, x⟫²`. -/
theorem rayleigh_expansion (H : Matrix (Fin k) (Fin k) ℝ) (hH : H.IsHermitian)
    (x : EuclideanSpace ℝ (Fin k)) :
    (inner ℝ x (Matrix.toEuclideanLin H x))
      = ∑ i, hH.eigenvalues i * (inner ℝ (hH.eigenvectorBasis i) x) ^ 2 := by
  -- keep the operator applied; introduce the eigenvalue only inside `⟪x, ·⟫` (a scalar pull-out),
  -- so the heavy spectral vector `λ • b` never appears as a bare `•` (which chokes the closing defeq).
  have hTx : Matrix.toEuclideanLin H x
      = ∑ i, (inner ℝ (hH.eigenvectorBasis i) x) • Matrix.toEuclideanLin H (hH.eigenvectorBasis i) := by
    conv_lhs => rw [← hH.eigenvectorBasis.sum_repr' x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  rw [hTx, inner_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [real_inner_smul_right, toEuclideanLin_eigenvectorBasis H hH i, real_inner_smul_right,
    real_inner_comm x (hH.eigenvectorBasis i)]
  ring

/-- **Parseval**: `‖x‖² = ∑ᵢ ⟪bᵢ, x⟫²` in the orthonormal eigenbasis. -/
theorem sum_sq_inner_eigenvectorBasis (H : Matrix (Fin k) (Fin k) ℝ) (hH : H.IsHermitian)
    (x : EuclideanSpace ℝ (Fin k)) :
    ∑ i, (inner ℝ (hH.eigenvectorBasis i) x) ^ 2 = ‖x‖ ^ 2 := by
  calc ∑ i, (inner ℝ (hH.eigenvectorBasis i) x) ^ 2
      = ∑ i, inner ℝ x (hH.eigenvectorBasis i) * inner ℝ (hH.eigenvectorBasis i) x :=
        Finset.sum_congr rfl (fun i _ => by
          rw [real_inner_comm x (hH.eigenvectorBasis i)]; ring)
    _ = inner ℝ x x := hH.eigenvectorBasis.sum_inner_mul_inner x x
    _ = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x

/-- **The dimension-counting core (network-free).** If the Rayleigh quotient of a Hermitian `H` is `≥ c`
on a subspace `U`, then `finrank U + #{eigenvalue < c} ≤ k`: `U` meets the weak eigenspace `{eigenvectors :
λ < c}` trivially (Rayleigh both `≥ c` and `< c` forces `0`), so `finrank U + #{λ<c} ≤ k` via
`Submodule.finrank_sup_add_finrank_inf_eq`. -/
theorem finrank_add_weakCount_le (H : Matrix (Fin k) (Fin k) ℝ) (hH : H.IsHermitian) (c : ℝ)
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin k)))
    (hU : ∀ u ∈ U, c * ‖u‖ ^ 2 ≤ inner ℝ u (Matrix.toEuclideanLin H u)) :
    Module.finrank ℝ U + (Finset.univ.filter (fun i => hH.eigenvalues i < c)).card ≤ k := by
  set S : Finset (Fin k) := Finset.univ.filter (fun i => hH.eigenvalues i < c) with hS
  set v : {i // i ∈ S} → EuclideanSpace ℝ (Fin k) := fun i => hH.eigenvectorBasis (i : Fin k) with hv
  have hvli : LinearIndependent ℝ v :=
    (hH.eigenvectorBasis.orthonormal.linearIndependent).comp _ Subtype.val_injective
  set W : Submodule ℝ (EuclideanSpace ℝ (Fin k)) := Submodule.span ℝ (Set.range v) with hW
  have hWdim : Module.finrank ℝ W = S.card := by
    rw [hW, finrank_span_eq_card hvli, Fintype.card_coe]
  -- `⟪b j, u⟫ = 0` for `j ∉ S` and `u ∈ W`
  have hortho : ∀ j : Fin k, j ∉ S → ∀ u ∈ W, inner ℝ (hH.eigenvectorBasis j) u = 0 := by
    intro j hj u hu
    refine Submodule.span_induction (p := fun u _ => inner ℝ (hH.eigenvectorBasis j) u = 0)
      ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨i, rfl⟩
      have hne : j ≠ (i : Fin k) := fun h => hj (h ▸ i.2)
      have hpair := orthonormal_iff_ite.1 hH.eigenvectorBasis.orthonormal j (i : Fin k)
      rw [if_neg hne] at hpair
      exact hpair
    · simp
    · intro x y _ _ hx hy; rw [inner_add_right, hx, hy, add_zero]
    · intro a x _ hx; rw [inner_smul_right, hx, mul_zero]
  -- Rayleigh `< c ‖u‖²` on `W \ {0}`
  have hrayW : ∀ u ∈ W, u ≠ 0 → inner ℝ u (Matrix.toEuclideanLin H u) < c * ‖u‖ ^ 2 := by
    intro u huW hune
    rw [rayleigh_expansion H hH u]
    set t : Fin k → ℝ := fun i => (inner ℝ (hH.eigenvectorBasis i) u) ^ 2 with ht
    have htnonneg : ∀ i, 0 ≤ t i := fun i => sq_nonneg _
    have htzero : ∀ i ∉ S, t i = 0 := by
      intro i hi; simp only [ht, hortho i hi u huW]; ring
    have hzero : ∀ i ∉ S, hH.eigenvalues i * t i = 0 := by
      intro i hi; rw [htzero i hi]; ring
    have hnormsq : ∑ i, t i = ‖u‖ ^ 2 := sum_sq_inner_eigenvectorBasis H hH u
    have hsumS : ∑ i ∈ S, t i = ‖u‖ ^ 2 := by
      rw [← hnormsq]
      exact Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => htzero i hi)
    have hSsumpos : 0 < ∑ i ∈ S, t i := by rw [hsumS]; positivity
    obtain ⟨i0, hi0S, hi0pos⟩ : ∃ i ∈ S, 0 < t i := by
      by_contra hcon
      push_neg at hcon
      have : ∑ i ∈ S, t i = 0 :=
        Finset.sum_eq_zero (fun i hi => le_antisymm (hcon i hi) (htnonneg i))
      rw [this] at hSsumpos; exact lt_irrefl 0 hSsumpos
    calc ∑ i, hH.eigenvalues i * t i
        = ∑ i ∈ S, hH.eigenvalues i * t i :=
          (Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => hzero i hi)).symm
      _ < ∑ i ∈ S, c * t i := by
          refine Finset.sum_lt_sum (fun i hi => ?_) ⟨i0, hi0S, ?_⟩
          · exact mul_le_mul_of_nonneg_right (Finset.mem_filter.1 hi).2.le (htnonneg i)
          · exact mul_lt_mul_of_pos_right (Finset.mem_filter.1 hi0S).2 hi0pos
      _ = c * ‖u‖ ^ 2 := by rw [← Finset.mul_sum, hsumS]
  -- `U ⊓ W = ⊥`
  have hInter : U ⊓ W = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro u hu
    obtain ⟨huU, huW⟩ := Submodule.mem_inf.1 hu
    by_contra hune
    exact absurd (hU u huU) (not_le.mpr (hrayW u huW hune))
  -- assemble
  have hfe := Submodule.finrank_sup_add_finrank_inf_eq U W
  rw [hInter, finrank_bot, add_zero] at hfe
  haveI hfin : Module.Finite ℝ (EuclideanSpace ℝ (Fin k)) :=
    Module.Finite.equiv (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm
  have h1 := Submodule.finrank_le (U ⊔ W)
  rw [(WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).finrank_eq, Module.finrank_fin_fun] at h1
  rw [← hWdim]; omega

end DLNFibre.DLN.RLCT
