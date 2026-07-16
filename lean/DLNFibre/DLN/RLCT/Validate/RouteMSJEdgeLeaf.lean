import DLNFibre.DLN.RLCT.Validate.MatMulFibre
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option linter.style.longLine false

/-!
# `RouteMSJEdgeLeaf` — the b=1 corank-one edge leaf reduction (R1)

Thread `genm-tideD` (edge dispatch arm). The **R1 corank-collapse a-fortiori** of the b=1 edge leaf:
the corank Frobenius loss `frobSq(C·Q̃ₚ + γ⊗q_b)` is bounded BELOW by the single-fragile-direction
residual `‖C·v + σγ‖²` (`v = Q̃ₚ·ω`, `ω = q_b/‖q_b‖` the unit fragile row, `σ = ‖q_b‖`), so — since
`(·)^{−c'}` is decreasing — the edge loss power is bounded ABOVE by `(W + ‖C·v+σγ‖²)^{−c'}`, the form the
C-shift atoms (`RouteMSJEdgeCShift`) consume. Network-free.

Route (edgeasm's recipe, Cauchy-Schwarz variant): `frobSq M ≥ ‖M·ω₀‖²` for a unit vector `ω₀` (per-row
Cauchy-Schwarz, `frobSq M = ∑ᵢ‖rowᵢ‖² ≥ ∑ᵢ⟨rowᵢ,ω₀⟩² = ‖M·ω₀‖²`); instantiated at `M = C·Q̃ₚ + γ⊗q_b`,
`ω₀ = q_b/‖q_b‖`, using `(C·Q̃ₚ + γ⊗q_b)·ω₀ = C·(Q̃ₚ·ω₀) + σγ = C·v + σγ`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped BigOperators

/-- **The Frobenius–mulVec Cauchy-Schwarz bound (R1 core).** For `M : Fin a → Fin n → ℝ` and a
sub-unit vector `ω` (`∑ⱼωⱼ² ≤ 1`), the squared Euclidean norm of `M·ω` is bounded by the squared
Frobenius norm: `∑ᵢ ((of M).mulVec ω i)² ≤ frobSq M`. Per-row discrete Cauchy-Schwarz
(`Finset.sum_mul_sq_le_sq_mul_sq`) + the sub-unit factor. This is the a-fortiori that drops the
transverse corank directions, keeping only the fragile direction `ω`. -/
theorem frobSq_ge_sumSq_mulVec {a n : ℕ} (M : Fin a → Fin n → ℝ) (ω : Fin n → ℝ)
    (hω : ∑ j, (ω j) ^ 2 ≤ 1) :
    (∑ i, ((Matrix.of M).mulVec ω i) ^ 2) ≤ frobSq M := by
  have hrow : ∀ i, ((Matrix.of M).mulVec ω i) ^ 2 ≤ ∑ j, (M i j) ^ 2 := by
    intro i
    have hcs : (∑ j, M i j * ω j) ^ 2 ≤ (∑ j, (M i j) ^ 2) * (∑ j, (ω j) ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => M i j) ω
    have hmv : (Matrix.of M).mulVec ω i = ∑ j, M i j * ω j := by
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    rw [hmv]
    refine le_trans hcs ?_
    calc (∑ j, (M i j) ^ 2) * (∑ j, (ω j) ^ 2)
        ≤ (∑ j, (M i j) ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left hω (Finset.sum_nonneg (fun j _ => sq_nonneg _))
      _ = ∑ j, (M i j) ^ 2 := mul_one _
  refine le_trans (Finset.sum_le_sum (fun i _ => hrow i)) ?_
  unfold frobSq
  exact le_refl _

end DLNFibre.DLN.RLCT
