import DLNFibre.DLN.RLCT.Validate.MatMulFibre
import DLNFibre.DLN.RLCT.Validate.RouteMSJPivotChart

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJChartAlgebra` — the exact post-shear Frobenius block identity

The **algebraic core** of Aoyagi's boundary-0 pivot peel (the residual of `sjBoundaryPeel`,
`RouteMSJResolution.lean`): the exact cross-coupled decomposition of the front-factor Frobenius loss
under the Schur block split. Network-free, S2-free (pure matrix algebra, no measure theory).

On a pivot chart the front factor `A₀ : Matrix (t ⊕ a) (t ⊕ b) ℝ` splits into blocks
`A₀ = fromBlocks A B C D` with `A` the invertible `t × t` pivot. The tail product `Q : Matrix (t ⊕ b) n`
splits by rows into the pivot-column rows `Q_p = Q.submatrix Sum.inl id` and the non-pivot-column rows
`Q_b = Q.submatrix Sum.inr id`. Then, EXACTLY (design cert ADDENDUM 4, verified to 1e-10):

    frobSq (A₀ · Q) = frobSq (A · Q̃_p) + frobSq (C · Q̃_p + Γ · Q_b),

    Q̃_p := Q_p + A⁻¹ · B · Q_b,      Γ := D − C · A⁻¹ · B   (the Schur complement `schurCompl`).

**The corank block `Γ` is CROSS-COUPLED with `C · Q̃_p`** — the bottom block is `C·Q̃_p + Γ·Q_b`, NOT the
clean `Γ·Q_b`. A prior design that dropped the `C·Q̃_p` term (`(‖A·Q̃_p‖² + ‖Γ·Q_b‖²)`) was WRONG; this
identity is the corrected exact form. It is the `frobSq` form of the banked `schur_cov`
(`RouteMSJPivotChart.lean`): whereas `schur_cov` records `Q₁·A₀·Q₂ = fromBlocks A 0 0 Γ` (an algebraic
block-diagonalisation of `A₀` alone), this records what happens to the loss `frobSq(A₀·Q)` of the
front factor times the tail — the object the peel actually integrates.

The identity is exact and route-independent: any formalisation of the peel (whichever domain / cover
convention the assembly uses) needs it. What it does NOT do (deferred to the assembly tides): the
measure-preserving reindex `Fin M₀ ≃ Fin t ⊕ Fin (M₀−t)` of the box to block coordinates, the
`measurePreserving_shearSub` substitution `D ↦ Γ`, and the finite pivot-chart cover — the plumbing that
turns this pointwise identity into a `lintegral` bound.
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped BigOperators

variable {t a b n : Type*} [Fintype t] [Fintype a] [Fintype b] [Fintype n] [DecidableEq t]

/-- **The Frobenius row-block split.** For a matrix with a sum-type row index `t ⊕ a`, the squared
Frobenius norm splits over the two row blocks: `frobSq M = frobSq (top rows) + frobSq (bottom rows)`,
the top/bottom rows being the `Sum.inl` / `Sum.inr` submatrices. Just `Fintype.sum_sum_type` on the
outer (row) sum of `frobSq`. -/
theorem frobSq_row_split (M : Matrix (t ⊕ a) n ℝ) :
    frobSq M = frobSq (M.submatrix Sum.inl id) + frobSq (M.submatrix Sum.inr id) := by
  unfold frobSq
  rw [Fintype.sum_sum_type]
  rfl

/-- **The top row-block of `A₀ · Q`.** With `A₀ = fromBlocks A B C D`, the pivot-row block of the
product is `A · Q_p + B · Q_b` (`Q_p, Q_b` the pivot / non-pivot column rows of `Q`). Entrywise:
`Matrix.mul_apply` splits the contraction sum over `t ⊕ b`, and `fromBlocks_apply₁₁ / ₁₂` read the
top-left / top-right blocks. -/
theorem fromBlocks_mul_topRows (A : Matrix t t ℝ) (B : Matrix t b ℝ) (C : Matrix a t ℝ)
    (D : Matrix a b ℝ) (Q : Matrix (t ⊕ b) n ℝ) :
    (fromBlocks A B C D * Q).submatrix Sum.inl id
      = A * Q.submatrix Sum.inl id + B * Q.submatrix Sum.inr id := by
  ext i k
  simp only [Matrix.submatrix_apply, id_eq, Matrix.mul_apply, Matrix.add_apply]
  rw [Fintype.sum_sum_type]
  simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂]

/-- **The bottom row-block of `A₀ · Q`.** With `A₀ = fromBlocks A B C D`, the non-pivot-row block of
the product is `C · Q_p + D · Q_b`. As `fromBlocks_mul_topRows`, with `fromBlocks_apply₂₁ / ₂₂`. -/
theorem fromBlocks_mul_botRows (A : Matrix t t ℝ) (B : Matrix t b ℝ) (C : Matrix a t ℝ)
    (D : Matrix a b ℝ) (Q : Matrix (t ⊕ b) n ℝ) :
    (fromBlocks A B C D * Q).submatrix Sum.inr id
      = C * Q.submatrix Sum.inl id + D * Q.submatrix Sum.inr id := by
  ext i k
  simp only [Matrix.submatrix_apply, id_eq, Matrix.mul_apply, Matrix.add_apply]
  rw [Fintype.sum_sum_type]
  simp only [fromBlocks_apply₂₁, fromBlocks_apply₂₂]

/-- **The pivot top-block collapses to `A · Q̃_p`.** `A · Q_p + B · Q_b = A · (Q_p + A⁻¹ B Q_b)`,
using `A · A⁻¹ = 1` (`mul_invOf_self`) — the shear coordinate `Q̃_p := Q_p + A⁻¹ B Q_b` appears here. -/
theorem topRows_eq_mul_QtildeP (A : Matrix t t ℝ) (B : Matrix t b ℝ) [Invertible A]
    (Qp : Matrix t n ℝ) (Qb : Matrix b n ℝ) :
    A * Qp + B * Qb = A * (Qp + ⅟A * B * Qb) := by
  rw [Matrix.mul_add]
  congr 1
  rw [Matrix.mul_assoc (⅟A) B Qb, ← Matrix.mul_assoc A (⅟A) (B * Qb), mul_invOf_self,
    Matrix.one_mul]

/-- **The corank bottom-block reveals the cross-coupling `C · Q̃_p + Γ · Q_b`.**
`C · Q_p + D · Q_b = C · (Q_p + A⁻¹ B Q_b) + (D − C A⁻¹ B) · Q_b` — the `C·Q̃_p` cross term is genuine,
`Γ = schurCompl A B C D`. Expand `C·Q̃_p` and cancel the `± C A⁻¹ B Q_b` pair. -/
theorem botRows_eq_cross (A : Matrix t t ℝ) (B : Matrix t b ℝ) (C : Matrix a t ℝ)
    (D : Matrix a b ℝ) [Invertible A] (Qp : Matrix t n ℝ) (Qb : Matrix b n ℝ) :
    C * Qp + D * Qb
      = C * (Qp + ⅟A * B * Qb) + schurCompl A B C D * Qb := by
  rw [schurCompl, Matrix.mul_add, Matrix.sub_mul,
    ← Matrix.mul_assoc C (⅟A * B) Qb, ← Matrix.mul_assoc C (⅟A) B]
  abel

/-- **The exact post-shear Frobenius block identity (design cert ADDENDUM 4).** With `A` the
invertible `t × t` pivot block of the front factor `A₀ = fromBlocks A B C D`, and the tail product `Q`
split by rows into `Q_p = Q.submatrix Sum.inl id` (pivot columns) and `Q_b = Q.submatrix Sum.inr id`:

    frobSq (A₀ · Q) = frobSq (A · Q̃_p) + frobSq (C · Q̃_p + Γ · Q_b),

`Q̃_p := Q_p + A⁻¹ B Q_b`, `Γ := schurCompl A B C D = D − C A⁻¹ B`. The bottom block carries the
CROSS-COUPLING `C · Q̃_p` alongside `Γ · Q_b` (the corank contribution). Exact matrix algebra: split
the loss over the two row blocks (`frobSq_row_split`), compute each block of `A₀·Q`
(`fromBlocks_mul_*`), and collapse to the sheared coordinates (`topRows_eq_mul_QtildeP`,
`botRows_eq_cross`). -/
theorem frobSq_schur_block_split (A : Matrix t t ℝ) (B : Matrix t b ℝ) (C : Matrix a t ℝ)
    (D : Matrix a b ℝ) [Invertible A] (Q : Matrix (t ⊕ b) n ℝ) :
    frobSq (fromBlocks A B C D * Q)
      = frobSq (A * (Q.submatrix Sum.inl id + ⅟A * B * Q.submatrix Sum.inr id))
        + frobSq (C * (Q.submatrix Sum.inl id + ⅟A * B * Q.submatrix Sum.inr id)
            + schurCompl A B C D * Q.submatrix Sum.inr id) := by
  rw [frobSq_row_split (fromBlocks A B C D * Q), fromBlocks_mul_topRows, fromBlocks_mul_botRows,
    topRows_eq_mul_QtildeP A B, botRows_eq_cross A B C D]

/-- **The block identity in `toBlocks` form** — the shape the pivot chart consumes. For a block-indexed
front factor `M'` with invertible top-left (pivot) block, `frobSq (M' · Q)` splits into the pivot-block
energy `frobSq (P · Q̃_p)` and the corank energy `frobSq (C · Q̃_p + Γ · Q_b)`, `P = M'.toBlocks₁₁`,
`Γ = schurCompl …`. The `M' = A₀.reindex e₀ e₁` form of `frobSq_schur_block_split` (via
`fromBlocks_toBlocks`), matching the banked `schur_cov_toBlocks` interface. -/
theorem frobSq_schur_toBlocks_split (M' : Matrix (t ⊕ a) (t ⊕ b) ℝ) [Invertible M'.toBlocks₁₁]
    (Q : Matrix (t ⊕ b) n ℝ) :
    frobSq (M' * Q)
      = frobSq (M'.toBlocks₁₁ *
          (Q.submatrix Sum.inl id + ⅟M'.toBlocks₁₁ * M'.toBlocks₁₂ * Q.submatrix Sum.inr id))
        + frobSq (M'.toBlocks₂₁ *
            (Q.submatrix Sum.inl id + ⅟M'.toBlocks₁₁ * M'.toBlocks₁₂ * Q.submatrix Sum.inr id)
          + schurCompl M'.toBlocks₁₁ M'.toBlocks₁₂ M'.toBlocks₂₁ M'.toBlocks₂₂
              * Q.submatrix Sum.inr id) := by
  have h := frobSq_schur_block_split M'.toBlocks₁₁ M'.toBlocks₁₂ M'.toBlocks₂₁ M'.toBlocks₂₂ Q
  rwa [fromBlocks_toBlocks] at h

end DLNFibre.DLN.RLCT
