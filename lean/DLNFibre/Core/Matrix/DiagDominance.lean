import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# `Core.Matrix.DiagDominance` — strict row diagonal dominance: `det ≠ 0` + the Varah inverse bound

A network-free engine brick. For a real square matrix `B` with a strict row-diagonal-dominance
MARGIN `γ > 0` (every row's diagonal absolute value exceeds the off-diagonal absolute-row-sum by at
least `γ`):

* `det B ≠ 0` (Levy–Desplanques) — wraps Mathlib's `det_ne_zero_of_sum_row_lt_diag`;
* **the Varah a-priori bound** `γ·|x i| ≤ ‖B·x‖_∞` for every index `i` — the elementary argmax
  argument: at the row `k` maximizing `|x k|`, `γ·|x_k| ≤ |(B·x)_k|` by isolating the diagonal term;
* its consequence for the inverse: every entry of `B⁻¹·C` is bounded by `(1/γ)·(a sup bound on C)`.

These are the two bricks the smeared L=2 stratum needs: `det ≠ 0` (the off-pole cancellation, on the
conditioned box — UNCONDITIONAL, not a.e.) and the `Λ₀ = B⁻¹·P₂` entry bound (field A). The bound is
δ-free given the conditioning `|B_ii| ≥ δ/2`, `|B_ij| ≤ δ/(4(r−1))` (so `γ = δ/4`); the per-`r` box
width is the load-bearing scope catch (a fixed `δ/8` is singular for `r ≥ 5`).
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.Core.Matrix

variable {n : ℕ}

/-- **Strict row diagonal dominance with margin `γ`.** Every row's diagonal absolute value beats the
off-diagonal absolute-row-sum by at least `γ`: `∑_{j≠k} |B k j| + γ ≤ |B k k|`, with `0 < γ`. -/
def StrictRowDominant (B : Matrix (Fin n) (Fin n) ℝ) (γ : ℝ) : Prop :=
  0 < γ ∧ ∀ k, (∑ j ∈ Finset.univ.erase k, |B k j|) + γ ≤ |B k k|

/-- A diagonally dominant matrix (margin `γ > 0`) has nonzero determinant (Levy–Desplanques). -/
theorem StrictRowDominant.det_ne_zero {B : Matrix (Fin n) (Fin n) ℝ} {γ : ℝ}
    (h : StrictRowDominant B γ) : B.det ≠ 0 := by
  refine det_ne_zero_of_sum_row_lt_diag (fun k => ?_)
  have := h.2 k
  simp only [Real.norm_eq_abs]
  have hγ := h.1
  linarith [this]

/-! ## The Varah a-priori bound -/

/-- **The argmax row.** For a nonempty index set there is a row `k` realizing the max of `|x ·|`.
The single diagonally-dominant row inequality at `k` then carries the global bound. -/
theorem StrictRowDominant.exists_argmax_bound [Nonempty (Fin n)]
    {B : Matrix (Fin n) (Fin n) ℝ} {γ : ℝ}
    (h : StrictRowDominant B γ) (x : Fin n → ℝ) :
    ∃ k, γ * |x k| ≤ |(B *ᵥ x) k| ∧ ∀ i, |x i| ≤ |x k| := by
  -- the index maximizing `|x ·|`
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin n))
    (fun i => |x i|)
  have hmax : ∀ i, |x i| ≤ |x k| := by
    intro i
    rw [← hk]
    exact Finset.le_sup' (fun i => |x i|) (Finset.mem_univ i)
  refine ⟨k, ?_, hmax⟩
  -- isolate the diagonal term:  (B·x) k = B k k · x k + ∑_{j≠k} B k j · x j
  have hsplit : (B *ᵥ x) k = B k k * x k + ∑ j ∈ Finset.univ.erase k, B k j * x j := by
    have : (B *ᵥ x) k = ∑ j, B k j * x j := rfl
    rw [this, Finset.sum_erase_eq_sub (Finset.mem_univ k)]
    ring
  -- so |B k k · x k| ≤ |(B·x) k| + ∑_{j≠k} |B k j| · |x j| ≤ |(B·x) k| + (∑_{j≠k}|B k j|) · |x k|
  have hdiag : |B k k * x k| ≤ |(B *ᵥ x) k| + (∑ j ∈ Finset.univ.erase k, |B k j|) * |x k| := by
    have htri : |B k k * x k| ≤ |(B *ᵥ x) k| + |∑ j ∈ Finset.univ.erase k, B k j * x j| := by
      rw [hsplit]
      calc |B k k * x k|
          = |(B k k * x k + ∑ j ∈ Finset.univ.erase k, B k j * x j)
              - ∑ j ∈ Finset.univ.erase k, B k j * x j| := by ring_nf
        _ ≤ |B k k * x k + ∑ j ∈ Finset.univ.erase k, B k j * x j|
              + |∑ j ∈ Finset.univ.erase k, B k j * x j| := abs_sub _ _
    have hoff : |∑ j ∈ Finset.univ.erase k, B k j * x j|
        ≤ (∑ j ∈ Finset.univ.erase k, |B k j|) * |x k| := by
      rw [Finset.sum_mul]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hmax j) (abs_nonneg _)
    linarith
  -- combine with the margin `∑_{j≠k}|B k j| + γ ≤ |B k k|`:  γ·|x k| ≤ |(B·x) k|
  have hmargin := h.2 k
  rw [abs_mul] at hdiag
  have hxk : (0 : ℝ) ≤ |x k| := abs_nonneg _
  nlinarith [hdiag, hmargin, hxk, h.1]

/-- **The Varah solution bound (pointwise).** If `B *ᵥ y = c` for a `γ`-dominant `B`, then every
coordinate `|y i| ≤ (1/γ)·M` for any uniform bound `M` on `|c k|` (`∀ k, |c k| ≤ M`). The argmax
inequality `γ·|y argmax| ≤ |c argmax| ≤ M`, then `|y i| ≤ |y argmax|`. -/
theorem StrictRowDominant.solution_bound [Nonempty (Fin n)]
    {B : Matrix (Fin n) (Fin n) ℝ} {γ : ℝ}
    (h : StrictRowDominant B γ) {y c : Fin n → ℝ} (hsol : B *ᵥ y = c)
    {Mbnd : ℝ} (hc : ∀ k, |c k| ≤ Mbnd) (i : Fin n) :
    |y i| ≤ (1 / γ) * Mbnd := by
  obtain ⟨k, hk, hmax⟩ := h.exists_argmax_bound y
  rw [hsol] at hk
  have hγ := h.1
  -- `γ·|y k| ≤ |c k| ≤ Mbnd`, and `|y i| ≤ |y k|`
  have hyk : γ * |y k| ≤ Mbnd := le_trans hk (hc k)
  have hik : |y i| ≤ |y k| := hmax i
  rw [one_div]
  -- `|y i| ≤ |y k| ≤ Mbnd/γ`
  have hkdiv : |y k| ≤ Mbnd / γ := by rw [le_div_iff₀ hγ]; linarith [mul_comm γ |y k|]
  calc |y i| ≤ |y k| := hik
    _ ≤ Mbnd / γ := hkdiv
    _ = γ⁻¹ * Mbnd := by rw [div_eq_inv_mul]

/-- **The Varah inverse-entry bound.** For a `γ`-dominant `B` (off the pole `det ≠ 0`) and any `C`,
the product `B⁻¹·C` has every entry `|(B⁻¹·C) a j| ≤ (1/γ)·Mj`, where `Mj` uniformly bounds the `j`-th
column of `C` (`∀ i, |C i j| ≤ Mj`). Column-by-column: `B·((B⁻¹·C)_{·,j}) = C_{·,j}`, then the
solution bound. -/
theorem StrictRowDominant.inv_mul_entry_bound [Nonempty (Fin n)] {p : ℕ}
    {B : Matrix (Fin n) (Fin n) ℝ} {γ : ℝ} (h : StrictRowDominant B γ)
    (C : Matrix (Fin n) (Fin p) ℝ) (j : Fin p) {Mj : ℝ} (hC : ∀ i, |C i j| ≤ Mj)
    (a : Fin n) :
    |(B⁻¹ * C) a j| ≤ (1 / γ) * Mj := by
  -- the `j`-th column of `B⁻¹·C` solves `B·(col) = C_{·,j}`
  set y : Fin n → ℝ := fun i => (B⁻¹ * C) i j with hy
  have hunit : IsUnit B.det := isUnit_iff_ne_zero.mpr h.det_ne_zero
  have hsol : B *ᵥ y = (fun i => C i j) := by
    funext i
    -- `(B *ᵥ y) i = ∑ t, B i t · (B⁻¹·C) t j = ((B·(B⁻¹·C)) i j) = ((B·B⁻¹·C) i j) = C i j`
    have hBy : (B *ᵥ y) i = (B * (B⁻¹ * C)) i j := by
      simp only [hy, Matrix.mul_apply]; rfl
    rw [hBy, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mul]
  exact h.solution_bound hsol (fun k => hC k) a

end DLNFibre.Core.Matrix
