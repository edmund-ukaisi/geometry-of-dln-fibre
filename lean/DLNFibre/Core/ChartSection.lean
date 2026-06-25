/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.SchurChartIff
import DLNFibre.Core.DeterminantalBaseElimination

/-!
# `DLNFibre.Core.ChartSection` — the `k`-valued normalizing gauge of a chart matrix (rung-2 brick 1)

The first concrete brick of the route-(c) rung-2 chart trivialization (thread 31): the **`k`-valued
normalizing gauge** of a target matrix `M : Mat_{p×q}(k)` whose top-left `r×r` pivot block `Δ` is
invertible. The gauge is the pair of end-vertex units `(L, H)` of the Schur-complement factorization
`M = L · E' · H` (`E' = diag(Δ, Schur)`), reindexed from the block split `Fin r ⊕ Fin (n−r)` to
`Fin n` by `finSplit`:

- `Lmatk M = [[I, 0], [B21·Δ⁻¹, I]]` (the `p×p` lower-unitriangular unit),
- `Hmatk M = [[Δ, B12], [0, I]]` (the `q×q` upper-triangular unit, `Δ` the invertible pivot).

When additionally `rank M ≤ r` (so the Schur relation `B22 = B21·Δ⁻¹·B12` holds, by the rung-1
`rank_le_iff_schur_eq`), the conjugation normalizes `M` to the rank-`r` normal form
`E = diag(I_r, 0)`:

> `(Lmatk M)⁻¹ · M · (Hmatk M)⁻¹ = E`   (`normalize_chart_matrix`).

This is the matrix heart of the chart retraction, **over `k`** (not the `SchurLoc` localization — the
gauge is read off the actual entries of `M`, valid pointwise on the chart `detΔ ≠ 0`). It feeds the
tuple-level retraction `φ(A) = gauge(mult A) • A ∈ fibre E` (next brick), via `mult_smul`.

## Main results
- `Lmatk`, `Hmatk` — the `k`-valued end-vertex gauge units of a chart matrix.
- `normalize_chart_matrix` — `L⁻¹ M H⁻¹ = E` when `rank M ≤ r` and `Δ` invertible.
-/

namespace DLNFibre.Core

open Matrix

universe u

variable {k : Type u} [Field k] {p q r : ℕ}

/-- The pivot block `Δ` (top-left `r×r`) of a chart matrix `M : Mat_{p×q}(k)`. -/
def chartΔ (M : Matrix (Fin p) (Fin q) k) (hp : r ≤ p) (hq : r ≤ q) :
    Matrix (Fin r) (Fin r) k :=
  M.submatrix (Fin.castLE hp) (Fin.castLE hq)

/-- `M` read in block form `[[Δ, B12], [B21, B22]]` over the pivot split `Fin r ⊕ Fin (·−r)`,
i.e. `(reindex (finSplit) (finSplit)) M`. -/
def chartBlocks (M : Matrix (Fin p) (Fin q) k) (hp : r ≤ p) (hq : r ≤ q) :
    Matrix (Fin r ⊕ Fin (p - r)) (Fin r ⊕ Fin (q - r)) k :=
  M.submatrix (finSplit hp).symm (finSplit hq).symm

/-- The lower-unitriangular gauge `L = [[I, 0], [B21·Δ⁻¹, I]]` as a `p×p` matrix over `k`,
reindexed from the block split. -/
noncomputable def Lmatk (M : Matrix (Fin p) (Fin q) k) (hp : r ≤ p) (hq : r ≤ q) :
    Matrix (Fin p) (Fin p) k :=
  (Matrix.fromBlocks 1 0
      ((chartBlocks M hp hq).toBlocks₂₁ * (chartΔ M hp hq)⁻¹) 1).submatrix
    (finSplit hp) (finSplit hp)

/-- The upper-triangular gauge `H = [[Δ, B12], [0, I]]` as a `q×q` matrix over `k`. -/
noncomputable def Hmatk (M : Matrix (Fin p) (Fin q) k) (hp : r ≤ p) (hq : r ≤ q) :
    Matrix (Fin q) (Fin q) k :=
  (Matrix.fromBlocks (chartΔ M hp hq) (chartBlocks M hp hq).toBlocks₁₂ 0 1).submatrix
    (finSplit hq) (finSplit hq)

/-! ## The gauge units are invertible -/

/-- `L` is a unit: lower-unitriangular (diagonal `I, I`), and reindexing by a permutation preserves
units (`det (submatrix e e) = det · sign`, but `IsUnit` is clean via `Matrix.submatrix_mul_equiv`). -/
theorem isUnit_Lmatk (M : Matrix (Fin p) (Fin q) k) (hp : r ≤ p) (hq : r ≤ q) :
    IsUnit (Lmatk M hp hq) := by
  rw [Lmatk, Matrix.isUnit_iff_isUnit_det, Matrix.det_submatrix_equiv_self,
    Matrix.det_fromBlocks_zero₁₂]
  simp

/-- `H` is a unit iff its pivot block `Δ` is: upper-triangular with diagonal `Δ, I`. -/
theorem isUnit_Hmatk (M : Matrix (Fin p) (Fin q) k) (hp : r ≤ p) (hq : r ≤ q)
    (hΔ : IsUnit (chartΔ M hp hq).det) :
    IsUnit (Hmatk M hp hq) := by
  rw [Hmatk, Matrix.isUnit_iff_isUnit_det, Matrix.det_submatrix_equiv_self,
    Matrix.det_fromBlocks_zero₂₁]
  simpa using hΔ

end DLNFibre.Core
