import DLNFibre.Core.RankLocusClosed
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Mul

/-!
# `DLNFibre.Core.CommonPivotL2` — a common invertible pivot for a two-factor product

The pivot-existence brick for the L = 2 D1 explicit corner-elimination chart (`genm-phiexpl`): for a
two-factor product `A0 · A1` of rank `r`, there is a **single row set** `I`, an internal set `K`, and
a column set `J` (all injective, all of size `r`) such that BOTH

    (A0 · A1).submatrix I J   and   A0.submatrix I K

are invertible (nonzero determinant). This is what the Schur reparametrisation
`w = (p | A0red, A1red | X, Y, U)` needs: `X = A0.submatrix I K` invertible (for the reduced block
`A0red = W − Z X⁻¹ Y`) AND `M11 = (A0·A1).submatrix I J` invertible (for `A1red = V − U M11⁻¹ M12`
and the regular block `p`).

**No Cauchy–Binet needed** (Mathlib v4.29 lacks a rectangular Cauchy–Binet): the two pivots share the
row set `I` by a rank squeeze — pick `I, J` making the product minor invertible (rank `r`); then
`(A0·A1).submatrix I J = (A0.submatrix I id) · (A1.submatrix id J)`, so
`r = rank(prod) ≤ rank(A0.submatrix I id) ≤ r`, forcing `rank(A0.submatrix I id) = r`; a full-row-rank
`r × H1` matrix has an invertible `r`-column minor, and a row permutation (`det_permute`) transports
its determinant back to the SAME row set `I`. Network-free; over any field; reusable for the ∀-`L`
corner-elimination lift (iterate on the grouped `(first L−1)·last` product).
-/

open Matrix

namespace DLNFibre.Core

variable {k : Type*} [Field k]

/-- **Square-minor existence** handling the `r = 0` empty minor (`det = 1`). Wraps the banked
`exists_submatrix_det_ne_zero_of_le_rank` (which needs `r + 1 ≤ rank`). -/
theorem exists_square_minor {p q m : ℕ} (A : Matrix (Fin p) (Fin q) k) (hm : m ≤ A.rank) :
    ∃ (er : Fin m → Fin p) (ec : Fin m → Fin q),
      Function.Injective er ∧ Function.Injective ec ∧ (A.submatrix er ec).det ≠ 0 := by
  classical
  cases m with
  | zero =>
      refine ⟨Fin.elim0, Fin.elim0, fun a => a.elim0, fun a => a.elim0, ?_⟩
      rw [Matrix.det_eq_one_of_card_eq_zero (by simp)]; exact one_ne_zero
  | succ n => exact exists_submatrix_det_ne_zero_of_le_rank A hm

/-- A square matrix over a field with nonzero determinant has full rank. -/
theorem rank_eq_of_det_ne_zero {m : ℕ} (A : Matrix (Fin m) (Fin m) k) (h : A.det ≠ 0) :
    A.rank = m := by
  classical
  have hunit : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr h)
  rw [Matrix.rank_of_isUnit A hunit, Fintype.card_fin]

/-- **A common invertible pivot for a two-factor product.** For `A0 : (Fin H0)×(Fin H1)` and
`A1 : (Fin H1)×(Fin H2)` over a field with `(A0 · A1).rank = r`, there are injective index maps
`I : Fin r → Fin H0`, `K : Fin r → Fin H1`, `J : Fin r → Fin H2` such that `(A0 · A1).submatrix I J`
and `A0.submatrix I K` both have nonzero determinant — the shared-row-set pivot the L = 2 Schur chart
consumes. -/
theorem exists_common_pivot_two_factor {H0 H1 H2 r : ℕ}
    (A0 : Matrix (Fin H0) (Fin H1) k) (A1 : Matrix (Fin H1) (Fin H2) k)
    (hr : (A0 * A1).rank = r) :
    ∃ (I : Fin r → Fin H0) (K : Fin r → Fin H1) (J : Fin r → Fin H2),
      Function.Injective I ∧ Function.Injective K ∧ Function.Injective J ∧
      ((A0 * A1).submatrix I J).det ≠ 0 ∧ (A0.submatrix I K).det ≠ 0 := by
  classical
  -- (a) the product minor: `I, J` with `det((A0·A1).submatrix I J) ≠ 0`.
  obtain ⟨I, J, hI, hJ, hMdet⟩ := exists_square_minor (A0 * A1) (le_of_eq hr.symm)
  -- (b) the row block `A0.submatrix I id` has rank `r` (squeeze).
  have hsplit : (A0 * A1).submatrix I J = (A0.submatrix I id) * (A1.submatrix id J) :=
    Matrix.submatrix_mul A0 A1 I id J Function.bijective_id
  have hMrank : ((A0 * A1).submatrix I J).rank = r :=
    rank_eq_of_det_ne_zero _ hMdet
  have hle : r ≤ (A0.submatrix I (id : Fin H1 → Fin H1)).rank := by
    have h1 : ((A0.submatrix I (id : Fin H1 → Fin H1)) * (A1.submatrix id J)).rank
        ≤ (A0.submatrix I (id : Fin H1 → Fin H1)).rank := Matrix.rank_mul_le_left _ _
    rwa [← hsplit, hMrank] at h1
  -- (c) extract an invertible column minor `K` of `A0.submatrix I id` (arbitrary row perm `er'`).
  obtain ⟨er', K, her', hK, hXdet⟩ := exists_square_minor (A0.submatrix I (id : Fin H1 → Fin H1)) hle
  refine ⟨I, K, J, hI, hK, hJ, hMdet, ?_⟩
  -- (d) transport the det back to row set `I` via the row permutation `er'`.
  have hbij : Function.Bijective er' := (Finite.injective_iff_bijective).mp her'
  set σ : Equiv.Perm (Fin r) := Equiv.ofBijective er' hbij with hσ
  have hrw : (A0.submatrix I (id : Fin H1 → Fin H1)).submatrix er' K
      = (A0.submatrix I K).submatrix σ id := by
    ext i j
    simp only [Matrix.submatrix_apply, id_eq, hσ, Equiv.ofBijective_apply]
  have hne : ((A0.submatrix I K).submatrix σ id).det ≠ 0 := by rw [← hrw]; exact hXdet
  rw [Matrix.det_permute σ (A0.submatrix I K)] at hne
  exact right_ne_zero_of_mul hne

end DLNFibre.Core
