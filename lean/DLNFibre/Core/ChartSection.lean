/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.RingTheory.Determinantal.Schur
import DLNFibre.Core.SchurGauge
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

/-! ## The explicit block inverses of the gauge units -/

/-- The explicit inverse of the lower-unitriangular block `[[I,0],[X,I]]⁻¹ = [[I,0],[−X,I]]`
(over any commutative ring; `Invertible` of the unitriangular block via `Matrix.invertibleOfIsUnitDet`). -/
theorem inv_fromBlocks_lower {R : Type*} [CommRing R] {a b : ℕ}
    (X : Matrix (Fin b) (Fin a) R) :
    (Matrix.fromBlocks (1 : Matrix (Fin a) (Fin a) R) (0 : Matrix (Fin a) (Fin b) R) X 1)⁻¹
      = Matrix.fromBlocks (1 : Matrix (Fin a) (Fin a) R) (0 : Matrix (Fin a) (Fin b) R) (-X) 1 := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.fromBlocks_multiply]
  simp

/-- The explicit inverse of the upper-triangular block `[[Δ,Y],[0,I]]⁻¹ = [[Δ⁻¹,−Δ⁻¹Y],[0,I]]`
when `Δ` is invertible. -/
theorem inv_fromBlocks_upper {R : Type*} [CommRing R] {a c : ℕ}
    (Δ : Matrix (Fin a) (Fin a) R) (Y : Matrix (Fin a) (Fin c) R) (hΔ : IsUnit Δ.det) :
    (Matrix.fromBlocks Δ Y (0 : Matrix (Fin c) (Fin a) R) 1)⁻¹
      = Matrix.fromBlocks Δ⁻¹ (-(Δ⁻¹ * Y)) (0 : Matrix (Fin c) (Fin a) R) 1 := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.fromBlocks_multiply, Matrix.nonsing_inv_mul Δ hΔ]
  simp

/-! ## The normal form and the chart normalization -/

/-- The rank-`r` normal form `E = diag(I_r, 0) : Mat_{p×q}(k)`, in block form `[[I,0],[0,0]]`
reindexed by the pivot split. -/
noncomputable def normalForm (p q r : ℕ) (hp : r ≤ p) (hq : r ≤ q) : Matrix (Fin p) (Fin q) k :=
  (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) k) 0 0 0).submatrix (finSplit hp) (finSplit hq)

/-- **The chart normalization.** When `rank M ≤ r` (so the Schur block relation holds, rung-1) and
the pivot block `Δ` is invertible, the gauge conjugation `L⁻¹ · M · H⁻¹` carries `M` to the rank-`r`
normal form `E = diag(I_r, 0)`. The matrix heart of the chart retraction, over `k`. Proof: reindex
the whole identity to the pivot block split, where the explicit gauge inverses (`inv_fromBlocks_*`)
and the LANDED `schurComplement_normal_form` give it directly (the Schur relation `B22 = B21 Δ⁻¹ B12`
is `rank_le_iff_schur_eq`). -/
theorem normalize_chart_matrix (M : Matrix (Fin p) (Fin q) k) (hp : r ≤ p) (hq : r ≤ q)
    (hΔ : IsUnit (chartΔ M hp hq).det) (hrank : M.rank ≤ r) :
    (Lmatk M hp hq)⁻¹ * M * (Hmatk M hp hq)⁻¹ = normalForm p q r hp hq := by
  -- abbreviations for the four blocks of `M` (in the pivot split).
  set Δ := chartΔ M hp hq with hΔdef
  set B12 := (chartBlocks M hp hq).toBlocks₁₂ with hB12
  set B21 := (chartBlocks M hp hq).toBlocks₂₁ with hB21
  set B22 := (chartBlocks M hp hq).toBlocks₂₂ with hB22
  -- `chartBlocks M = fromBlocks Δ B12 B21 B22` (the block decomposition; the top-left block of the
  -- reindexed matrix is exactly the pivot minor `chartΔ`).
  have hΔeq : (chartBlocks M hp hq).toBlocks₁₁ = Δ := by
    ext i j
    simp only [hΔdef, chartΔ, chartBlocks, Matrix.toBlocks₁₁, Matrix.submatrix_apply,
      Matrix.of_apply, Fin.castLE]
    rfl
  have hMblocks : chartBlocks M hp hq = Matrix.fromBlocks Δ B12 B21 B22 := by
    rw [← hΔeq, hB12, hB21, hB22, Matrix.fromBlocks_toBlocks]
  -- the Schur relation `B22 = B21 Δ⁻¹ B12` (rung-1, since `rank (chartBlocks M) = rank M ≤ r`).
  have hrankBlocks : (chartBlocks M hp hq).rank = M.rank := by
    rw [chartBlocks]; exact Matrix.rank_submatrix M (finSplit hp).symm (finSplit hq).symm
  have hSchur : B22 = B21 * Δ⁻¹ * B12 := by
    rw [← (rank_le_iff_schur_eq Δ B12 B21 B22 hΔ)]
    rw [← hMblocks, hrankBlocks]; exact hrank
  -- the block matrix `Mb = chartBlocks M`, an opaque name so reindexing `M` does not loop.
  set Mb := chartBlocks M hp hq with hMb
  -- `M` as a reindexed block matrix (`Mb` is opaque, so this rewrite terminates).
  have hMre : M = Mb.submatrix (finSplit hp) (finSplit hq) := by
    rw [hMb, chartBlocks, Matrix.submatrix_submatrix]; simp
  -- The two gauge inverses, in block form (their `M`-content folded into `Δ`, `B12`, `B21`).
  have hLinv : (Lmatk M hp hq)⁻¹
      = (Matrix.fromBlocks 1 0 (-(B21 * Δ⁻¹)) 1).submatrix (finSplit hp) (finSplit hp) := by
    rw [Lmatk, inv_submatrix_equiv, inv_fromBlocks_lower]
  have hHinv : (Hmatk M hp hq)⁻¹
      = (Matrix.fromBlocks Δ⁻¹ (-(Δ⁻¹ * B12)) 0 1).submatrix (finSplit hq) (finSplit hq) := by
    rw [Hmatk, inv_submatrix_equiv, inv_fromBlocks_upper _ _ hΔ]
  -- reindex the whole conjugation to block coordinates, then `schurComplement_normal_form`.
  rw [hLinv, hHinv, hMre,
    Matrix.submatrix_mul_equiv _ _ (finSplit hp) (finSplit hp) (finSplit hq),
    Matrix.submatrix_mul_equiv _ _ (finSplit hp) (finSplit hq) (finSplit hq), normalForm]
  congr 1
  -- block-coordinate goal: `[[I,0],[−B21Δ⁻¹,I]] * (chartBlocks M) * [[Δ⁻¹,−Δ⁻¹B12],[0,I]]
  --   = fromBlocks 1 0 0 0`, with `chartBlocks M = fromBlocks Δ B12 B21 (B21Δ⁻¹B12)` (Schur).
  rw [hMblocks, hSchur]
  exact schurComplement_normal_form Δ B12 B21 hΔ

/-- **The chart factorization** `M = L · E · H` — the converse of `normalize_chart_matrix`. For a
chart matrix `M` of `rank ≤ r` (pivot `Δ` invertible), the gauge units recover `M` from the normal
form: `(Lmatk M) · diag(I_r,0) · (Hmatk M) = M`. Obtained by left/right multiplying the
normalization `L⁻¹ M H⁻¹ = E` by the units `L`, `H` (`isUnit_Lmatk`/`isUnit_Hmatk`). -/
theorem factor_chart_matrix (M : Matrix (Fin p) (Fin q) k) (hp : r ≤ p) (hq : r ≤ q)
    (hΔ : IsUnit (chartΔ M hp hq).det) (hrank : M.rank ≤ r) :
    Lmatk M hp hq * normalForm p q r hp hq * Hmatk M hp hq = M := by
  have hnf := normalize_chart_matrix M hp hq hΔ hrank
  have hLd : IsUnit (Lmatk M hp hq).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_Lmatk M hp hq)
  have hHd : IsUnit (Hmatk M hp hq).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_Hmatk M hp hq hΔ)
  -- from `L⁻¹ M H⁻¹ = E`: `L · E · H = L · (L⁻¹ · M · H⁻¹) · H = M`.
  rw [← hnf]
  have hL1 : Lmatk M hp hq * (Lmatk M hp hq)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hLd
  have hH1 : (Hmatk M hp hq)⁻¹ * Hmatk M hp hq = 1 := Matrix.nonsing_inv_mul _ hHd
  rw [show Lmatk M hp hq * ((Lmatk M hp hq)⁻¹ * M * (Hmatk M hp hq)⁻¹) * Hmatk M hp hq
      = (Lmatk M hp hq * (Lmatk M hp hq)⁻¹) * M * ((Hmatk M hp hq)⁻¹ * Hmatk M hp hq) from by
        simp only [Matrix.mul_assoc], hL1, hH1, Matrix.one_mul, Matrix.mul_one]

end DLNFibre.Core
