import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJPivotChart` — the R1-UPPER `(S,J)` peel's inner c.o.v. base

The **change-of-variables base** for Aoyagi's boundary-0 pivot peel (the residual of `sjBoundaryPeel`,
`RouteMSJResolution.lean`). Self-contained, network-free block-matrix algebra: **Aoyagi Lemma 2** — the
unit-triangular change of variables. On a chart where the front factor's top-left `t × t` block `A` is
invertible, unit-triangular `Q₁` (lower) and `Q₂` (upper) — each of determinant `1` (the Jacobian-`1`
property) — conjugate the block matrix to block-diagonal form, exposing the **corank block** = the Schur
complement `Γ = D − C A⁻¹ B`:

    Q₁ · fromBlocks A B C D · Q₂ = fromBlocks A 0 0 Γ,   Γ = D − C · A⁻¹ · B.

`schur_cov` (the identity), `det_schurLeft`/`det_schurRight` (Jacobian `1`), and `det_fromBlocks_cov`
(`det = det A · det Γ`, the codimension-count bridge for a square front factor via `det_fromBlocks₁₁`).

## The math

Writing the front factor in blocks `A₀ = [[A, B], [C, D]]` with `A` the invertible `t × t` pivot, the
elementary (unit-triangular, hence Jacobian-`1`) row/column operations

    Q₁ = [[1, 0], [−C A⁻¹, 1]]   (clears the C block: row-reduce),
    Q₂ = [[1, −A⁻¹ B], [0, 1]]   (clears the B block: column-reduce)

give `Q₁ A₀ Q₂ = [[A, 0], [0, D − C A⁻¹ B]]`. The Schur complement `Γ = D − C A⁻¹ B` is the corank block:
its `(M₀ − t) × (M₁ − t)` shape is the codim-charge `(M₀ − t)(M₁ − t)` of the peel (`peelExp`). The
identity is `Matrix.fromBlocks_eq_of_invertible₁₁` (the LDU) read as `Q₁ = L⁻¹`, `Q₂ = U⁻¹`; here it is
re-proved directly by two `fromBlocks_multiply` and the pivot cancellations `⅟A · A = 1`, `A · ⅟A = 1`.

## Scope

This is the *reachable* c.o.v. base: the `Q₁, Q₂` unit-triangular reduction and its Jacobian-`1` /
Schur-complement facts. The reindex-to-top-left-block bridge (permute a chosen pivot minor to the corner
so `fromBlocks` applies) and the measure-theoretic assembly (radial blow-up + a.e. chart cover + `Beta`
fibre bound) are the `sjBoundaryPeel` residual, LATER tides.
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped Matrix

section AbstractCov

variable {t a b : Type*} [Fintype t] [Fintype a] [Fintype b]
  [DecidableEq t] [DecidableEq a] [DecidableEq b]

/-- **The unit lower-triangular left factor** `Q₁ = [[1, 0], [−C A⁻¹, 1]]` of the Schur c.o.v.
Clears the lower-left `C` block by a row operation. -/
noncomputable def schurLeft (A : Matrix t t ℝ) (C : Matrix a t ℝ) [Invertible A] :
    Matrix (t ⊕ a) (t ⊕ a) ℝ :=
  fromBlocks 1 0 (-(C * ⅟A)) 1

/-- **The unit upper-triangular right factor** `Q₂ = [[1, −A⁻¹ B], [0, 1]]` of the Schur c.o.v.
Clears the upper-right `B` block by a column operation. -/
noncomputable def schurRight (A : Matrix t t ℝ) (B : Matrix t b ℝ) [Invertible A] :
    Matrix (t ⊕ b) (t ⊕ b) ℝ :=
  fromBlocks 1 (-(⅟A * B)) 0 1

/-- **The Schur complement (corank block)** `Γ = D − C A⁻¹ B`. Its `a × b` shape is the corank
`(M₀ − t) × (M₁ − t)`; the codim-charge `(M₀ − t)(M₁ − t)` is its entry count. -/
noncomputable def schurCompl (A : Matrix t t ℝ) (B : Matrix t b ℝ) (C : Matrix a t ℝ)
    (D : Matrix a b ℝ) [Invertible A] : Matrix a b ℝ :=
  D - C * ⅟A * B

/-- **Aoyagi Lemma 2 — the unit-triangular change of variables.** With the pivot block `A`
invertible, `Q₁ · [[A, B], [C, D]] · Q₂ = [[A, 0], [0, Γ]]`, `Γ = D − C A⁻¹ B` the Schur complement.
Direct block-multiply: `Q₁` clears the `C` block (`⅟A · A = 1`), `Q₂` clears the `B` block
(`A · ⅟A = 1`). -/
theorem schur_cov (A : Matrix t t ℝ) (B : Matrix t b ℝ) (C : Matrix a t ℝ) (D : Matrix a b ℝ)
    [Invertible A] :
    schurLeft A C * fromBlocks A B C D * schurRight A B =
      fromBlocks A 0 0 (schurCompl A B C D) := by
  simp only [schurLeft, schurRight, schurCompl]
  rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]
  refine ⟨by simp, by simp, by simp [Matrix.mul_assoc], ?_⟩
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, zero_add,
    Matrix.neg_mul, Matrix.mul_assoc, invOf_mul_self, neg_add_cancel]
  rw [neg_add_eq_sub]

/-- **Jacobian `1` (left factor).** `det Q₁ = 1` — `Q₁` is unit lower-triangular
(`det = det 1 · det 1`). -/
theorem det_schurLeft (A : Matrix t t ℝ) (C : Matrix a t ℝ) [Invertible A] :
    (schurLeft A C).det = 1 := by
  unfold schurLeft
  rw [det_fromBlocks_zero₁₂, det_one, det_one, mul_one]

/-- **Jacobian `1` (right factor).** `det Q₂ = 1` — `Q₂` is unit upper-triangular
(`det = det 1 · det 1`). -/
theorem det_schurRight (A : Matrix t t ℝ) (B : Matrix t b ℝ) [Invertible A] :
    (schurRight A B).det = 1 := by
  unfold schurRight
  rw [det_fromBlocks_zero₂₁, det_one, det_one, mul_one]

/-- **The determinant factorises through the corank block** (square front factor) — `det [[A, B],
[C, D]] = det A · det Γ` (`Matrix.det_fromBlocks₁₁`, Schur), `Γ = D − C A⁻¹ B` the corank block. The
codimension-count bridge: with `A` (the pivot) invertible, the full square block matrix is nonsingular
iff the corank block `Γ` is — so the singular locus of the peeled factor is cut out by `Γ`. (The peel's
front factor is rectangular in general; there the corank charge is `Γ`'s entry count `(M₀−t)(M₁−t)`,
`schurCompl`'s `a × b` shape, not a determinant.) -/
theorem det_fromBlocks_cov (A : Matrix t t ℝ) (B : Matrix t a ℝ) (C : Matrix a t ℝ)
    (D : Matrix a a ℝ) [Invertible A] :
    (fromBlocks A B C D).det = A.det * (schurCompl A B C D).det := by
  rw [schurCompl, det_fromBlocks₁₁]

end AbstractCov

/-! ## The pivot chart — the c.o.v. on an actual front factor

A **pivot chart** for the front factor `A₀ : Matrix m n ℝ` is a choice of block-splitting equivs
`e₀ : m ≃ t ⊕ a`, `e₁ : n ≃ t ⊕ b` (equivalently: which `t` rows and `t` columns are the pivot) on
which the top-left `t × t` block of the reindexed matrix is invertible — equivalently the chosen
`(e₀, e₁)`-pivot minor `A₀.submatrix (e₀⁻¹∘inl) (e₁⁻¹∘inl)` has nonzero determinant
(`Matrix.invertibleOfIsUnitDet` turns that into the `Invertible` instance). There are finitely many
block-splittings for each `t ≤ min m n`, so these charts form a finite family.

On each chart the abstract `schur_cov` applies verbatim through `fromBlocks_toBlocks`: the front
factor's reindexing is `fromBlocks` of its own blocks, top-left the (invertible) pivot minor. What is
NOT proved here (the `sjBoundaryPeel` residual, LATER tides): the a.e. COVERING property — that every
front factor of rank `t` lies in some rank-`t` chart (`rank ⟹ nonzero minor of that size`) — and the
measure-theoretic finite-sum assembly (radial blow-up + `Beta` fibre bound). -/

section PivotChart

/-- **The pivot block is the chosen minor.** The top-left block of the block-split `A₀.reindex e₀ e₁`
is exactly the `(e₀, e₁)`-pivot minor `A₀.submatrix (e₀⁻¹∘inl) (e₁⁻¹∘inl)` — so the chart condition
"top-left block invertible" is literally "the chosen `t × t` pivot minor is nonsingular". -/
theorem pivotBlock_reindex_eq_submatrix {m n t a b : Type*}
    (A₀ : Matrix m n ℝ) (e₀ : m ≃ t ⊕ a) (e₁ : n ≃ t ⊕ b) :
    (A₀.reindex e₀ e₁).toBlocks₁₁
      = A₀.submatrix (fun i => e₀.symm (Sum.inl i)) (fun j => e₁.symm (Sum.inl j)) := by
  ext i j; rfl

variable {t a b : Type*} [Fintype t] [Fintype a] [Fintype b]
  [DecidableEq t] [DecidableEq a] [DecidableEq b]

/-- **The block-indexed change of variables.** For any block-indexed matrix `M'` with invertible
top-left block, `Q₁ · M' · Q₂ = fromBlocks (M'₁₁) 0 0 Γ`. `schur_cov` transported through
`fromBlocks_toBlocks` (`M'` is `fromBlocks` of its own blocks). This is the form the pivot chart uses:
apply it at `M' = A₀.reindex e₀ e₁`. -/
theorem schur_cov_toBlocks (M' : Matrix (t ⊕ a) (t ⊕ b) ℝ) [Invertible M'.toBlocks₁₁] :
    schurLeft M'.toBlocks₁₁ M'.toBlocks₂₁ * M' * schurRight M'.toBlocks₁₁ M'.toBlocks₁₂
      = fromBlocks M'.toBlocks₁₁ 0 0
          (schurCompl M'.toBlocks₁₁ M'.toBlocks₁₂ M'.toBlocks₂₁ M'.toBlocks₂₂) := by
  have h := schur_cov M'.toBlocks₁₁ M'.toBlocks₁₂ M'.toBlocks₂₁ M'.toBlocks₂₂
  rwa [fromBlocks_toBlocks] at h

/-- **The determinant factorises through the corank block (block-indexed, square).** For a square
block-indexed matrix with invertible pivot block, `det M' = det(pivot) · det Γ` — the singular locus of
the peeled factor is cut out by the Schur complement `Γ`. `det_fromBlocks_cov` through
`fromBlocks_toBlocks`. -/
theorem det_toBlocks_cov (M' : Matrix (t ⊕ a) (t ⊕ a) ℝ) [Invertible M'.toBlocks₁₁] :
    M'.det = M'.toBlocks₁₁.det
      * (schurCompl M'.toBlocks₁₁ M'.toBlocks₁₂ M'.toBlocks₂₁ M'.toBlocks₂₂).det := by
  have h := det_fromBlocks_cov M'.toBlocks₁₁ M'.toBlocks₁₂ M'.toBlocks₂₁ M'.toBlocks₂₂
  rwa [fromBlocks_toBlocks] at h

end PivotChart

end DLNFibre.DLN.RLCT
