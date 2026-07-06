import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# `DLNFibre.Core.SchurRankZero` — a rank-`r` block matrix with invertible leading block has zero
Schur complement

The algebraic fact the L=2 D1 `≥`-leg explicit corner-elimination germ needs on the slice `p = 0`
(`threads/genm-splitwit`, PART 2): the target `B = mult(v)` has `rank B = r` and an invertible
`r × r` leading block, so its **Schur complement vanishes**:

    B22 = B21 · B11⁻¹ · B12.

Combined with the banked `Core.schur_product_factor` (`M22 − M21 M11⁻¹ M12 = A0red·A1red`), this
pins the slice residual `(mult − B)22` at `p = 0` to `A0red·A1red = prod (H−r) (A0red,A1red)` —
the reduced Aoyagi core `dlnLoss (H−r) 0`, with NO leftover `Schur(B)` term.

Proof (column-space): with `B11` invertible, the `r` left columns of `fromBlocks B11 B12 B21 B22`
already span the column space (their span has `finrank r`, and `rank B ≤ r`), so the right columns
factor through them: `[B12; B22] = [B11; B21] · Y`. Reading the top block, `Y = B11⁻¹ · B12`, whence
`B22 = B21 · B11⁻¹ · B12`. Network-free; over any field. Reusable for the ∀-`L` lift.
-/

open Matrix Module

namespace DLNFibre.Core

variable {r p q : ℕ} {𝕜 : Type*} [Field 𝕜]

/-- **A rank-`r` block matrix with invertible leading block has zero Schur complement.** For
`Bf = fromBlocks B11 B12 B21 B22` with `B11` an invertible `r × r` block and `rank Bf ≤ r`, the
bottom block is fixed by the top via the Schur relation `B22 = B21 · ⅟B11 · B12`. -/
theorem schur_complement_zero_of_rank_le
    (B11 : Matrix (Fin r) (Fin r) 𝕜) (B12 : Matrix (Fin r) (Fin q) 𝕜)
    (B21 : Matrix (Fin p) (Fin r) 𝕜) (B22 : Matrix (Fin p) (Fin q) 𝕜)
    [Invertible B11]
    (hrank : (fromBlocks B11 B12 B21 B22).rank ≤ r) :
    B22 = B21 * ⅟B11 * B12 := by
  classical
  set Bf : Matrix (Fin r ⊕ Fin p) (Fin r ⊕ Fin q) 𝕜 := fromBlocks B11 B12 B21 B22 with hBf
  -- the `r` left columns of `Bf`.
  set Lft : Matrix (Fin r ⊕ Fin p) (Fin r) 𝕜 := Bf.submatrix id Sum.inl with hLft
  -- block row/column read-offs of `fromBlocks` (through the `Lft` submatrix).
  have hLinl : ∀ (a : Fin r) (k : Fin r), Lft (Sum.inl a) k = B11 a k := by
    intro a k; simp [hLft, hBf, Matrix.submatrix_apply, Matrix.fromBlocks]
  have hLinr : ∀ (a : Fin p) (k : Fin r), Lft (Sum.inr a) k = B21 a k := by
    intro a k; simp [hLft, hBf, Matrix.submatrix_apply, Matrix.fromBlocks]
  have hBinl : ∀ (a : Fin r) (j : Fin q), Bf (Sum.inl a) (Sum.inr j) = B12 a j := by
    intro a j; simp [hBf, Matrix.fromBlocks]
  have hBinr : ∀ (a : Fin p) (j : Fin q), Bf (Sum.inr a) (Sum.inr j) = B22 a j := by
    intro a j; simp [hBf, Matrix.fromBlocks]
  -- `Lft *ᵥ x = Bf *ᵥ (Sum.elim x 0)`: left columns are the full columns, `inr`-input zeroed.
  have hLftmul : ∀ x : Fin r → 𝕜, Lft *ᵥ x = Bf *ᵥ (Sum.elim x 0) := by
    intro x; funext i
    simp only [hLft, Matrix.mulVec, Matrix.submatrix_apply, id, dotProduct,
      Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero, add_zero]
  -- range inclusion `range Lft ≤ range Bf` (from `hLftmul`).
  have hle : LinearMap.range Lft.mulVecLin ≤ LinearMap.range Bf.mulVecLin := by
    rintro _ ⟨x, rfl⟩
    exact ⟨Sum.elim x 0, by simp only [Matrix.mulVecLin_apply]; rw [← hLftmul]⟩
  -- `rank Lft = r`: `Lft.mulVecLin` is injective — its `Sum.inl` block is `B11 *ᵥ ·` (invertible),
  -- so `Lft *ᵥ c = 0 ⟹ B11 *ᵥ c = 0 ⟹ c = 0`; an injective map into a fin-dim space has full rank.
  have hLftrank : Lft.rank = r := by
    have hinj : Function.Injective Lft.mulVecLin := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro c hc
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hc
      have hB11c : B11 *ᵥ c = 0 := by
        funext a
        change B11 a ⬝ᵥ c = 0
        have hrow : B11 a = Lft (Sum.inl a) := by funext k; exact (hLinl a k).symm
        rw [hrow]; change (Lft *ᵥ c) (Sum.inl a) = 0; rw [hc]; rfl
      have hc0 : c = ⅟B11 *ᵥ (B11 *ᵥ c) := by
        rw [Matrix.mulVec_mulVec, invOf_mul_self, Matrix.one_mulVec]
      rw [hc0, hB11c, Matrix.mulVec_zero]
    have : Module.finrank 𝕜 (LinearMap.range Lft.mulVecLin) = Module.finrank 𝕜 (Fin r → 𝕜) :=
      (LinearEquiv.ofInjective Lft.mulVecLin hinj).finrank_eq.symm
    rw [Matrix.rank, this, Module.finrank_pi, Fintype.card_fin]
  -- finrank of `range Bf ≤ r = finrank range Lft`, so with `hle` the ranges coincide.
  have hfinLft : finrank 𝕜 (LinearMap.range Lft.mulVecLin) = r := hLftrank
  have hfinBf : finrank 𝕜 (LinearMap.range Bf.mulVecLin) ≤ r := hrank
  have hrangeEq : LinearMap.range Lft.mulVecLin = LinearMap.range Bf.mulVecLin :=
    Submodule.eq_of_le_of_finrank_le hle (by rw [hfinLft]; exact hfinBf)
  -- each right column of `Bf` lies in `range Lft.mulVecLin`; choose a witness column vector.
  have hcol : ∀ j : Fin q, ∃ x : Fin r → 𝕜, Lft *ᵥ x = fun i => Bf i (Sum.inr j) := by
    intro j
    have hmem : (fun i => Bf i (Sum.inr j)) ∈ LinearMap.range Bf.mulVecLin := by
      refine ⟨Pi.single (Sum.inr j) 1, ?_⟩
      funext i; simp [Matrix.col_apply]
    obtain ⟨x, hx⟩ := hrangeEq ▸ hmem
    exact ⟨x, by rw [Matrix.mulVecLin_apply] at hx; exact hx⟩
  choose X hX using hcol
  -- the chosen `X j` solves `B11 *ᵥ X j = B12·col j` and `B21 *ᵥ X j = B22·col j`
  -- (`Lft`'s `Sum.inl`/`Sum.inr` rows are the `B11`/`B21` rows; `⬝ᵥ` is `*ᵥ` entrywise).
  have hB11X : ∀ j, B11 *ᵥ X j = fun a => B12 a j := by
    intro j; funext a
    change B11 a ⬝ᵥ X j = B12 a j
    have hrow : B11 a = Lft (Sum.inl a) := by funext k; exact (hLinl a k).symm
    rw [hrow]
    change (Lft *ᵥ X j) (Sum.inl a) = B12 a j
    rw [hX j]; exact hBinl a j
  have hB21X : ∀ j, B21 *ᵥ X j = fun a => B22 a j := by
    intro j; funext a
    change B21 a ⬝ᵥ X j = B22 a j
    have hrow : B21 a = Lft (Sum.inr a) := by funext k; exact (hLinr a k).symm
    rw [hrow]
    change (Lft *ᵥ X j) (Sum.inr a) = B22 a j
    rw [hX j]; exact hBinr a j
  -- `X j = ⅟B11 *ᵥ (B12·col j)`, so `B22·col j = (B21 ⅟B11 B12)·col j`.
  funext a j
  have hXsolve : X j = ⅟B11 *ᵥ (fun a => B12 a j) := by
    rw [← hB11X j, Matrix.mulVec_mulVec, invOf_mul_self, Matrix.one_mulVec]
  have h := congrFun (hB21X j) a
  rw [← h, hXsolve, Matrix.mulVec_mulVec]
  change (B21 * ⅟B11) a ⬝ᵥ (fun k => B12 k j) = (B21 * ⅟B11 * B12) a j
  rw [Matrix.mul_apply]; rfl

end DLNFibre.Core
