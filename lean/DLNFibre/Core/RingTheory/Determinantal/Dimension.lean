import DLNFibre.Core.RingTheory.Determinantal.Schur

/-!
# `Matrix` — rank-stratum dimension / codimension closed forms (Mathlib-mirror)

The dimension and codimension of the rank-`≤ r` determinantal stratum of `p × q` matrices, as
**closed-form natural numbers** with the classical "codimension + dimension = ambient" identity:

> `rankStratumDim r p q = r · (p + q − r)`,
> `rankStratumCodim r p q = (p − r) · (q − r)`,
> `rankStratumDim r p q + rankStratumCodim r p q = p · q`  (for `r ≤ p`, `r ≤ q`).

These are the **matrix-general** dimension facts — pure `Nat` arithmetic plus the identification of
`rankStratumDim` with the `k`-dimension of the explicit pivot-chart parameter space
(`Matrix.finrank_pivotRankChart_params`, `Schur.lean`). They carry no determinantal-geometry engine
and no field hypotheses beyond what the `finrank` cross-check needs; they live in the bare `Matrix`
namespace so any consumer of the determinantal stratum can name its dimension and codimension.

## What is general here, and what is engine-bound (a precision note)

The *closed forms* and their arithmetic are general matrix content (this file). The **theorem that
the rank-`≤ r` determinantal variety actually HAS variety dimension `rankStratumDim`** — i.e. the
geometric statement `varietyDim Σ̄^r = r(n + m − r)` — is **Proved** in
`DLNFibre.Core.DeterminantalStratumDim` (`varietyDim_productRankLocusLE_stratum`), via the
project's orbit-closure codimension engine. Its load-bearing input is the **Proved, zero-cited**
"Brick A" (`codimRepCanonical_productRankLocusLE_eq_cCodim`, `DLNFibre.Core.SigmaCodim`): the
geometric codimension of `Σ̄^r` equals the combinatorial `cCodim d r = C`. **Brick A is Proved here,
not cited** — there is no Eagon–Northcott / Bruns–Vetter citation behind it; the determinantal
codimension is re-derived from the quiver-orbit codimension engine. (The only *cited* results in the
repository are the analytic RLCT bricks `cited_watanabe_upper` / `ln_lower`, which live on the `DLN`
side and play no role in the dimension/codimension.) This file supplies only the arithmetic those
geometric theorems consume; it does not, and must not, restate the geometric dimension as a bare
matrix fact (that would drag the orbit engine into a Mathlib-mirror module) or as a cited assumption
(that would under-claim a Proved result).

**Dependency rule:** mirrors `Mathlib.LinearAlgebra.Matrix.*`; no `DLNFibre.DLN` import.
-/

namespace Matrix

open Module

universe u

/-! ## The closed-form natural numbers -/

/-- **Rank-stratum dimension** `rankStratumDim r p q = r · (p + q − r)`: the variety dimension of
the rank-`≤ r` locus of `p × q` matrices (the geometric statement that it is attained lives in
`DLNFibre.Core.DeterminantalStratumDim`). -/
def rankStratumDim (r p q : ℕ) : ℕ := r * (p + q - r)

/-- **Rank-stratum codimension** `rankStratumCodim r p q = (p − r) · (q − r)`: the codimension of
the rank-`≤ r` locus of `p × q` matrices inside the ambient `p · q`-dimensional matrix space. -/
def rankStratumCodim (r p q : ℕ) : ℕ := (p - r) * (q - r)

@[simp] theorem rankStratumDim_def (r p q : ℕ) : rankStratumDim r p q = r * (p + q - r) := rfl

@[simp] theorem rankStratumCodim_def (r p q : ℕ) :
    rankStratumCodim r p q = (p - r) * (q - r) := rfl

/-! ## The codimension + dimension = ambient identity -/

/-- **Codimension + dimension = ambient (`Nat`).** For `r ≤ p` and `r ≤ q`,
`(p − r)(q − r) + r(p + q − r) = p · q` — the codimension of the rank-`≤ r` determinantal stratum
plus its dimension is the dimension `p · q` of the ambient `p × q` matrix space. Pure `Nat`
arithmetic (the matrix-general core of the determinantal dimension count). -/
theorem rankStratumCodim_add_rankStratumDim_eq (r p q : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
    rankStratumCodim r p q + rankStratumDim r p q = p * q := by
  rw [rankStratumCodim_def, rankStratumDim_def]
  obtain ⟨a, rfl⟩ := Nat.le.dest hp
  obtain ⟨b, rfl⟩ := Nat.le.dest hq
  simp only [Nat.add_sub_cancel_left]
  have h : r + a + (r + b) - r = r + a + b := by omega
  rw [h]; ring

/-- **Dimension as ambient − codimension.** Rearrangement of
`rankStratumCodim_add_rankStratumDim_eq`: `r(p + q − r) = p · q − (p − r)(q − r)`. -/
theorem rankStratumDim_eq_ambient_sub_codim (r p q : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
    rankStratumDim r p q = p * q - rankStratumCodim r p q := by
  have h := rankStratumCodim_add_rankStratumDim_eq r p q hp hq
  omega

/-! ## Anchoring `rankStratumDim` to the pivot-chart parameter space

The closed form `rankStratumDim r p q` is the `k`-dimension of the explicit Schur pivot-chart
parameter space `Matrix m m k × Matrix m n k × Matrix l m k` (with `r = card m`, `p = card l + r`,
`q = card n + r`) — the parametrization `pivotRankChartEquiv` of `Schur.lean`. This ties the closed
form to a genuine `finrank` witness (not merely a polynomial), so a consumer can read the dimension
off the chart. -/

/-- **The pivot-chart parameter space has `finrank = rankStratumDim`.** For `r = card m`,
`p = card l + r`, `q = card n + r`, the affine parameter space
`Matrix m m k × Matrix m n k × Matrix l m k` of the rank-`= r` Schur chart `pivotRankChartEquiv`
has `k`-dimension `rankStratumDim r p q = r · (p + q − r)`. Combines the block-count `finrank`
(`finrank_pivotRankChart_params`) with the arithmetic `dim_params_eq_delta`. -/
theorem finrank_pivotRankChart_params_eq_rankStratumDim {k : Type u} [Field k]
    {m n l : Type u} [Fintype m] [Fintype n] [Fintype l] :
    finrank k (Matrix m m k × Matrix m n k × Matrix l m k)
      = rankStratumDim (Fintype.card m) (Fintype.card l + Fintype.card m)
          (Fintype.card n + Fintype.card m) := by
  rw [finrank_pivotRankChart_params, rankStratumDim_def]
  -- the three block counts sum to `r(p + q − r)`: `r = card m`, `p = card l + r`, `q = card n + r`
  have h := dim_params_eq_delta (Fintype.card m)
    (Fintype.card l + Fintype.card m) (Fintype.card n + Fintype.card m)
    (Nat.le_add_left _ _) (Nat.le_add_left _ _)
  simpa only [Nat.add_sub_cancel] using h

end Matrix
