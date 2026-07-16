import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement

set_option linter.style.longLine false

/-!
# `RouteMSchurPSDDetMono` — Loewner-order determinant monotonicity (non-spectral)

The reusable matrix-algebra lemma the CHARGED corank recursion needs (couplerad §w3-percorank): for real
positive-semidefinite matrices, `0 ⪯ Y ⪯ X ⟹ det Y ≤ det X` (Minkowski's determinant monotonicity), proved
WITHOUT eigenvalues (dodging the documented D-C `IsHermitian.eigenvalues` whnf/isDefEq trap). Route: the
Schur-complement recursion `det X = X₁₁ · det(X/X₁₁)` (`Matrix.det_fromBlocks₁₁`), with the Schur complement
Loewner-monotone via the variational identity `vᵀ(X/X₁₁)v = min_u [u;v]ᵀX[u;v]` (complete the square).

`Matrix.PosSemidef.det_nonneg` is the `Y = 0` instance (`det 0 = 0 ≤ det X`), so the induction proves both
at once — no `PosSemidef.sqrt` / continuous-functional-calculus import needed.

## Status: building bottom-up. Landed: `blockQuadForm_expand` (the `1⊕k` block QF expansion — the heart).
## Remaining (documented plan): complete-square form → Schur-complement PSD + Loewner-monotone (variational)
## → `det_fromBlocks₁₁` pivot step → induction on dimension. Non-spectral throughout.
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

/-! ## The block quadratic-form expansion (the heart) -/

/-- **Block quadratic-form expansion for a `1 ⊕ k` symmetric matrix.** For a symmetric block matrix `M`
over `Fin 1 ⊕ Fin k`, the quadratic form at `w = (u, v)` expands as the pivot term + the (symmetry-merged)
cross term + the lower block form: `w ⬝ᵥ M *ᵥ w = M₁₁·u² + 2u·(∑ⱼ M(inl 0)(inr j)·vⱼ) + ∑ⱼₗ vⱼ·M(inr j)(inr
l)·vₗ`. The starting point for completing the square (the `d·(u + d⁻¹ r·v)²` form and the Schur complement
follow by `ring` once `d := M₁₁ ≠ 0`). Uses symmetry only to merge the two cross terms. -/
theorem blockQuadForm_expand {k : ℕ} (M : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) ℝ)
    (hsymm : ∀ p q, M p q = M q p) (u : ℝ) (v : Fin k → ℝ) :
    (Sum.elim (fun _ : Fin 1 => u) v) ⬝ᵥ (M *ᵥ (Sum.elim (fun _ : Fin 1 => u) v))
      = M (Sum.inl 0) (Sum.inl 0) * u ^ 2
        + 2 * u * (∑ j, M (Sum.inl 0) (Sum.inr j) * v j)
        + ∑ j, ∑ l, v j * M (Sum.inr j) (Sum.inr l) * v l := by
  classical
  -- Expand the dot product / mulVec over the `Fin 1 ⊕ Fin k` index into the four blocks.
  simp only [dotProduct, mulVec, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Fin.sum_univ_one, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  -- rewrite the lower-cross term via symmetry `M (inr x) (inl 0) = M (inl 0) (inr x)`
  rw [show (∑ x : Fin k, v x * (M (Sum.inr x) (Sum.inl 0) * u))
        = ∑ x : Fin k, u * (M (Sum.inl 0) (Sum.inr x) * v x) from
      Finset.sum_congr rfl (fun x _ => by rw [hsymm (Sum.inr x) (Sum.inl 0)]; ring)]
  have h2 : (∑ i : Fin k, 2 * u * (M (Sum.inl 0) (Sum.inr i) * v i))
      = (∑ x : Fin k, u * (M (Sum.inl 0) (Sum.inr x) * v x))
        + (∑ x : Fin k, u * (M (Sum.inl 0) (Sum.inr x) * v x)) := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun x _ => by ring)
  have hdd : (∑ j : Fin k, ∑ l : Fin k, v j * M (Sum.inr j) (Sum.inr l) * v l)
      = ∑ x : Fin k, ∑ x_1 : Fin k, v x * (M (Sum.inr x) (Sum.inr x_1) * v x_1) :=
    Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun x_1 _ => by ring))
  rw [h2, hdd]; ring

/-! ## The Schur complement and its variational quadratic form -/

/-- **The `1⊕k` Schur complement** `Sc j l := M(inr j)(inr l) − M₁₁⁻¹·M(inr j)(inl 0)·M(inl 0)(inr l)`
(pivot `M₁₁ = M (inl 0)(inl 0)`; Lean's `0⁻¹ = 0` makes it the plain lower block when the pivot is `0`). -/
noncomputable def schurCompl {k : ℕ} (M : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun j l => M (Sum.inr j) (Sum.inr l)
    - (M (Sum.inl 0) (Sum.inl 0))⁻¹ * (M (Sum.inr j) (Sum.inl 0) * M (Sum.inl 0) (Sum.inr l))

/-- **The Schur-complement quadratic form, closed form.** `v ⬝ᵥ Sc *ᵥ v = ∑ⱼₗ vⱼ·M(inr j)(inr l)·vₗ −
M₁₁⁻¹·(∑ⱼ M(inl 0)(inr j)·vⱼ)²` (the second sum factors as a square via symmetry). -/
theorem schurCompl_quadForm_closed {k : ℕ} (M : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) ℝ)
    (hsymm : ∀ p q, M p q = M q p) (v : Fin k → ℝ) :
    v ⬝ᵥ (schurCompl M *ᵥ v)
      = (∑ j, ∑ l, v j * M (Sum.inr j) (Sum.inr l) * v l)
        - (M (Sum.inl 0) (Sum.inl 0))⁻¹ * (∑ j, M (Sum.inl 0) (Sum.inr j) * v j) ^ 2 := by
  classical
  set d := M (Sum.inl 0) (Sum.inl 0) with hd
  -- Step 1: expand `v ⬝ᵥ Sc v` as one double sum with the sub kept inside each summand.
  have hL : v ⬝ᵥ (schurCompl M *ᵥ v)
      = ∑ j, ∑ l, (v j * M (Sum.inr j) (Sum.inr l) * v l
          - d⁻¹ * ((v j * M (Sum.inr j) (Sum.inl 0)) * (M (Sum.inl 0) (Sum.inr l) * v l))) := by
    simp only [dotProduct, mulVec, schurCompl, Matrix.of_apply, Finset.mul_sum, hd]
    exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => by ring))
  rw [hL]
  simp only [Finset.sum_sub_distrib]
  congr 1
  -- Step 2: the pivot-correction double sum factors as `d⁻¹ · R²` (via symmetry + product-of-sums).
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [hsymm (Sum.inr j) (Sum.inl 0)]; ring

/-- **The variational identity: `v ⬝ᵥ Sc *ᵥ v` is the block QF at the minimiser `u* = −M₁₁⁻¹·(row·v)`.**
So for `M` PSD the Schur form is nonneg (`= w* ⬝ᵥ M *ᵥ w* ≥ 0`), and it is `≤` the block QF at every `u`. -/
theorem schurCompl_quadForm_eq_blockQuadForm_min {k : ℕ}
    (M : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) ℝ) (hsymm : ∀ p q, M p q = M q p) (v : Fin k → ℝ) :
    v ⬝ᵥ (schurCompl M *ᵥ v)
      = (Sum.elim (fun _ : Fin 1 =>
            -(M (Sum.inl 0) (Sum.inl 0))⁻¹ * (∑ j, M (Sum.inl 0) (Sum.inr j) * v j)) v)
          ⬝ᵥ (M *ᵥ (Sum.elim (fun _ : Fin 1 =>
            -(M (Sum.inl 0) (Sum.inl 0))⁻¹ * (∑ j, M (Sum.inl 0) (Sum.inr j) * v j)) v)) := by
  rw [schurCompl_quadForm_closed M hsymm v,
    blockQuadForm_expand M hsymm
      (-(M (Sum.inl 0) (Sum.inl 0))⁻¹ * (∑ j, M (Sum.inl 0) (Sum.inr j) * v j)) v]
  set d := M (Sum.inl 0) (Sum.inl 0) with hd
  set R := ∑ j, M (Sum.inl 0) (Sum.inr j) * v j with hR
  -- both sides equal `(∑∑ vMv) − d⁻¹·R²`; the pivot terms collapse via `d·d⁻² = d⁻¹` (holds even d=0).
  have hdd : d * (d⁻¹ * d⁻¹) = d⁻¹ := by
    rcases eq_or_ne d 0 with h | h
    · simp [h]
    · field_simp
  ring_nf
  rw [hR] at *
  nlinarith [hdd, sq_nonneg R]

end DLNFibre.DLN.RLCT
