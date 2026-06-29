import DLNFibre.DLN.RLCT.Validate.RouteMBoundaryClass
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# `RouteMSmearedGenRate` — the generic scalar-Gram shear cancellation (the ∀M-smeared rate's core)

The load-bearing algebraic fact for the family-parametric ∀M boundary-SMEARED rate, in the
`(r,c) = (1,·)` (SCALAR-Gram) regime: when the front product `P` has RANK-ONE columns (every column
is a scalar multiple of column `0` — the front-bottleneck `r = 1` structural fact), the scalar-Gram
routing `Λ₀ = (P₁ᵀP₁)⁻¹P₁ᵀP₂` satisfies `P₁·Λ₀ = P₂` exactly off the pole `{‖col 0‖² = 0}`. This is
the generic version of the `(1,2,1)`/`(1,3,2)` validate-smalls' per-`M` scalar cancellation
(`a00·(a01/a00) = a01`), proven once for ALL rank-one-column front products — the piece Codex
(`genM11-arch`) flagged as the biggest risk for the flat-coordinate ∀M lift.

This file is the architecture-proving FIRST sub-target (Codex `genM11-arch` §First sub-target). It is
network-free pure linear algebra (no `routeMCore`/chart yet) — the generic cancellation that the
flat-coordinate ∀M smeared chart's rate will consume, specialized to `P = frontProd M` via the
front-bottleneck rank-one fact (a SEPARATE, still-to-build bridge).

**Caveat (carried next to the claim):** the rank-one-columns hypothesis AND `‖col 0‖² ≠ 0` are BOTH
load-bearing — scalar Gram alone does NOT give `P₁Λ₀ = P₂` (the columns must actually lie in
`span(col 0)`, and `col 0 ≠ 0` for the Gram to be invertible). The front-bottleneck `r = 1` supplies
the rank-one fact; the off-pole condition supplies `‖col 0‖² ≠ 0`.
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

variable {rows : Type*} [Fintype rows] [DecidableEq rows]
variable {s : Type*} [Fintype s] [DecidableEq s]

/-- **The scalar-Gram cancellation (rank-one columns).** Let `c₀ : rows → ℝ` be the pivot column with
`‖c₀‖² = ∑ᵢ (c₀ i)² ≠ 0`, and let `P₂ : Matrix rows s ℝ` have every column a scalar multiple of `c₀`:
`P₂ · eⱼ = μ j • c₀` (`P₂ i j = μ j * c₀ i`). Writing `P₁ : Matrix rows (Fin 1) ℝ` for the single
pivot column, the scalar-Gram routing `Λ₀ = (P₁ᵀP₁)⁻¹ P₁ᵀ P₂` satisfies `P₁ · Λ₀ = P₂`. The proof:
`P₁ᵀP₁ = ‖c₀‖²` (a `1×1` matrix), invertible; `Λ₀ 0 j = (‖c₀‖²)⁻¹ · (c₀ ⬝ (μ j • c₀)) = μ j`; so
`(P₁·Λ₀) i j = c₀ i · μ j = P₂ i j`. -/
theorem scalarGram_cancel_of_rankOneColumns
    (c₀ : rows → ℝ) (μ : s → ℝ) (hc : (∑ i, (c₀ i) ^ 2) ≠ 0)
    (P₁ : Matrix rows (Fin 1) ℝ) (P₂ : Matrix rows s ℝ)
    (hP₁ : ∀ i, P₁ i 0 = c₀ i) (hP₂ : ∀ i j, P₂ i j = μ j * c₀ i) :
    P₁ * ((P₁.transpose * P₁)⁻¹ * P₁.transpose * P₂) = P₂ := by
  -- `P₁ᵀP₁` is the `1×1` matrix `‖c₀‖²`
  have hgram : (P₁.transpose * P₁) = (fun _ _ => ∑ i, (c₀ i) ^ 2 : Matrix (Fin 1) (Fin 1) ℝ) := by
    funext a b
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha; subst hb
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply, hP₁]
    exact Finset.sum_congr rfl (fun i _ => by rw [sq])
  -- the `1×1` inverse: `((‖c₀‖²))⁻¹`
  have hinv : ((P₁.transpose * P₁)⁻¹ : Matrix (Fin 1) (Fin 1) ℝ)
      = (fun _ _ => (∑ i, (c₀ i) ^ 2)⁻¹) := by
    rw [hgram]
    funext a b
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha; subst hb
    rw [Matrix.inv_def, Matrix.det_fin_one, Matrix.adjugate_fin_one]
    simp only [Matrix.of_apply, Matrix.one_apply_eq, Ring.inverse_eq_inv', Matrix.smul_apply,
      smul_eq_mul, mul_one]
  -- The routing scalar `Λ₀ 0 j = μ j` (proven first), then `(P₁·Λ₀) i j = c₀ i · μ j = P₂ i j`.
  have hrow : ∀ k, (∑ a, ((P₁.transpose * P₁)⁻¹) 0 a * P₁.transpose a k)
      = (∑ i, (c₀ i) ^ 2)⁻¹ * c₀ k := by
    intro k
    rw [Fin.sum_univ_one, hinv]
    simp only [Matrix.transpose_apply, hP₁]
  have hlam : ∀ j, ((P₁.transpose * P₁)⁻¹ * P₁.transpose * P₂) 0 j = μ j := by
    intro j
    rw [Matrix.mul_apply]
    rw [show (∑ x, ((P₁.transpose * P₁)⁻¹ * P₁.transpose) 0 x * P₂ x j)
        = ∑ x, ((∑ i, (c₀ i) ^ 2)⁻¹ * c₀ x) * (μ j * c₀ x) from
      Finset.sum_congr rfl (fun x _ => by rw [Matrix.mul_apply, hrow x, hP₂ x j])]
    rw [show (∑ x, ((∑ i, (c₀ i) ^ 2)⁻¹ * c₀ x) * (μ j * c₀ x))
        = (μ j * (∑ x, (c₀ x) ^ 2)) * (∑ i, (c₀ i) ^ 2)⁻¹ from by
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun x _ => by rw [sq]; ring)]
    rw [mul_assoc, mul_inv_cancel₀ hc, mul_one]
  funext i j
  have hlhs : (P₁ * ((P₁.transpose * P₁)⁻¹ * P₁.transpose * P₂)) i j = P₁ i 0 * μ j := by
    rw [Matrix.mul_apply]
    rw [Fin.sum_univ_one]
    rw [hlam j]
  rw [hlhs, hP₁ i, hP₂ i j, mul_comm]

end DLNFibre.DLN.RLCT
