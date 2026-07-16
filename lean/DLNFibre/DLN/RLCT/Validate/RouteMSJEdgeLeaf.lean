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

/-- **The b=1 corank-collapse a-fortiori (R1).** For the corank block `Matrix.of C * Q̃ₚ + γ⊗q_b` with a
single fragile row `q_b = σ•ω` (`ω` unit, `∑ⱼωⱼ²=1`, `σ = ‖q_b‖`), the squared Frobenius loss is bounded
BELOW by the single-fragile-direction residual `‖C·v + σγ‖²` (`v = Q̃ₚ·ω`). Instantiates the R1 core
`frobSq_ge_sumSq_mulVec` at the unit direction `ω`, using `(of M).mulVec ω = (of C)·(Q̃ₚ·ω) + σγ` (the
outer product contributes `σγᵢ·∑ⱼωⱼ² = σγᵢ`). Dropping the ≥0 transverse residual, this is the a-fortiori
that turns the corank Frobenius loss into the C-shift atom form: `(W + frobSq(...))^{−c'} ≤ (W + ‖C·v+σγ‖²)^{−c'}`
(rpow-antitone), the input to `edge_C_shift_bound`/`edge_leaf_gamma_bound`. -/
theorem corank_afortiori {a u n : ℕ} (C : Fin a → Fin u → ℝ) (Qp : Matrix (Fin u) (Fin n) ℝ)
    (γ : Fin a → ℝ) (ω : Fin n → ℝ) (σ : ℝ) (hω : ∑ j, (ω j) ^ 2 = 1) :
    (∑ i, ((Matrix.of C).mulVec (Qp.mulVec ω) i + σ * γ i) ^ 2)
      ≤ frobSq (Matrix.of C * Qp + Matrix.of (fun i j => σ * γ i * ω j)) := by
  set M : Matrix (Fin a) (Fin n) ℝ := Matrix.of C * Qp + Matrix.of (fun i j => σ * γ i * ω j) with hM
  have hmv : ∀ i, (Matrix.of M).mulVec ω i = (Matrix.of C).mulVec (Qp.mulVec ω) i + σ * γ i := by
    intro i
    have hMof : (Matrix.of M) = M := rfl
    rw [hMof, hM, Matrix.add_mulVec, Pi.add_apply, ← Matrix.mulVec_mulVec]
    congr 1
    -- outer product term: (of (σγᵢωⱼ)).mulVec ω i = σ γᵢ (∑ⱼ ωⱼ²) = σ γᵢ
    have houter : (Matrix.of (fun i j => σ * γ i * ω j)).mulVec ω i = σ * γ i * ∑ j, (ω j) ^ 2 := by
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [houter, hω, mul_one]
  refine le_trans (le_of_eq ?_) (frobSq_ge_sumSq_mulVec M ω (le_of_eq hω))
  exact Finset.sum_congr rfl (fun i _ => by rw [hmv i])

/-- **The R1 integrand a-fortiori (b=1).** The corank loss power is bounded ABOVE by the
single-fragile-direction power: `(W + frobSq(C·Q̃ₚ + γ⊗q_b))^{−c'} ≤ (W + ‖C·v+σγ‖²)^{−c'}` (`ofReal`,
`W>0`, `c'≥0`, `q_b = σ•ω`, `ω` unit). Composes `corank_afortiori` (`‖C·v+σγ‖² ≤ frobSq(...)`) with
rpow base-antitonicity for the negative exponent (`Real.rpow_le_rpow_of_nonpos`). This is the exact
pointwise bound the edge assembly applies before Fubini: it turns `(freedSchurLoss)^{−c'}` (with the
pivot core `W = frobSq(P·Q̃ₚ)` split off) into the C-shift atom integrand. -/
theorem corank_integrand_le {a u n : ℕ} (C : Fin a → Fin u → ℝ) (Qp : Matrix (Fin u) (Fin n) ℝ)
    (γ : Fin a → ℝ) (ω : Fin n → ℝ) (σ : ℝ) (hω : ∑ j, (ω j) ^ 2 = 1) {W c' : ℝ}
    (hW : 0 < W) (hc' : 0 ≤ c') :
    ENNReal.ofReal ((W + frobSq (Matrix.of C * Qp + Matrix.of (fun i j => σ * γ i * ω j))) ^ (-c'))
      ≤ ENNReal.ofReal ((W + ∑ i, ((Matrix.of C).mulVec (Qp.mulVec ω) i + σ * γ i) ^ 2) ^ (-c')) := by
  apply ENNReal.ofReal_le_ofReal
  apply Real.rpow_le_rpow_of_nonpos
  · exact add_pos_of_pos_of_nonneg hW (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  · linarith [corank_afortiori C Qp γ ω σ hω]
  · linarith

end DLNFibre.DLN.RLCT
