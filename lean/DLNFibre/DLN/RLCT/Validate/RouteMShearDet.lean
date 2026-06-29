import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Real.Basic

/-!
# `RouteMShearDet` — the abstract det-`1` unitriangular shear (the staircase `−N·W` shear, network-free)

The reusable det-`1` core of the direction-2 staircase factorization (`coarse-route-grading-obstruction.md`
→ the validated per-piece factorization): the global interior-chart Jacobian factors as
`(radial/spectator pivot blow-ups) ∘ (a det-`1` unitriangular SHEAR carrying the bilinear `−N_s·W_s` +
Schur KEPT terms)`. The shear's determinant is `1` because, under a 2-value grading
`{modified coords} / {kept coords}`, its standard-basis matrix is block-triangular with the diagonal
blocks the IDENTITY (the modified rows read only OTHER, kept coords; the kept rows are projections).

This module abstracts the `(2,2,2)` `RouteM222Det.shear222Deriv_det` idiom (the `id + N`, `N² = 0`
nilpotent argument) into a **network-free, opaque-width** lemma. It is the foundational brick: any
endomorphism whose matrix is block-triangular under a grading with IDENTITY diagonal blocks has det `1`
(and abs-det `1`) — the det-irrelevance of the staircase shear, INDEPENDENT of the chart's bilinear
detail (which only needs to verify the block-tri + identity-diagonal hypotheses).

The 2-value `{modified}/{kept}` grading is an ENDOMORPHISM grading (same coordinate on rows and columns),
so it is NOT subject to the input/output partition mismatch that blocks the L-value layer grading
(`RouteMGradingObstruction`): the shear genuinely is square block-triangular under one grading.

* `blockTri_identityDiag_det_one` — `M.BlockTriangular b` + identity diagonal blocks ⟹ `det M = 1`.
* `fderiv_det_one_of_shear` — the fderiv-level form: a `HasFDerivAt` map whose matrix is block-tri with
  identity diagonal blocks (under a 2-value or any grading) has `|det D| = 1`.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (determinant + matrix; no analysis beyond the CLM).
-/

open scoped BigOperators
open Matrix

namespace DLNFibre.DLN.RLCT

/-- **Block-triangular with identity diagonal blocks ⟹ det `1`.** If `M : Matrix (Fin N) (Fin N) ℝ` is
`BlockTriangular b` and within each grade the block is the identity (`b i = b j → M i j = if i = j then 1
else 0`), then `det M = 1`. The det-irrelevance core of a unitriangular shear: `Matrix.BlockTriangular.det`
gives `det = ∏ det(toSquareBlock)`, and each diagonal block is the identity (det `1`). Abstracts
`RouteM222Det.shear222Deriv_det`'s tail to any grading / opaque width. -/
theorem blockTri_identityDiag_det_one {N : ℕ} {α : Type*} [DecidableEq α] [LinearOrder α]
    (M : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → α) (htri : M.BlockTriangular b)
    (hdiag : ∀ i j : Fin N, b i = b j → M i j = if i = j then 1 else 0) :
    M.det = 1 := by
  rw [htri.det]
  apply Finset.prod_eq_one
  intro a _
  have hid : M.toSquareBlock b a = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    have hMij : M.toSquareBlock b a ⟨i, hi⟩ ⟨j, hj⟩ = M i j := rfl
    rw [hMij, hdiag i j (by rw [hi, hj]), Matrix.one_apply]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, if_neg (by rw [Subtype.mk_eq_mk]; exact h)]
  rw [hid, Matrix.det_one]

/-- **The fderiv-level det-`1` shear.** A differentiable self-map `f` of `Fin N → ℝ` (`HasFDerivAt f D u`)
whose standard-basis Jacobian matrix is block-triangular under a grading `b` with identity diagonal blocks
has `|det D| = 1`. The det-irrelevance of the staircase shear at the fderiv level: feed the
`shear222Deriv_det`-style block-tri + identity-diagonal facts (verified per chart) and conclude det `1`,
network-free. -/
theorem fderiv_det_one_of_shear {N : ℕ} {α : Type*} [DecidableEq α] [LinearOrder α]
    (D : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) (b : Fin N → α)
    (htri : (LinearMap.toMatrix' (D : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ))).BlockTriangular b)
    (hdiag : ∀ i j : Fin N,
      b i = b j → LinearMap.toMatrix' (D : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)) i j
        = if i = j then 1 else 0) :
    |LinearMap.det (D : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ))| = 1 := by
  rw [← LinearMap.det_toMatrix' (D : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)),
    blockTri_identityDiag_det_one _ b htri hdiag, abs_one]

/-! ## Non-vacuity: the identity and a genuine shear both fire -/

/-- **Non-vacuity (identity).** The identity matrix is block-triangular under any grading with identity
diagonal blocks, so `det = 1` — the lemma fires. -/
example {N : ℕ} (b : Fin N → ℕ) :
    (1 : Matrix (Fin N) (Fin N) ℝ).det = 1 :=
  blockTri_identityDiag_det_one 1 b (Matrix.blockTriangular_one)
    (fun i j _ => by rw [Matrix.one_apply])

/-- **Non-vacuity (genuine shear).** A `2×2` unitriangular shear `!![1, c; 0, 1]` graded by the row index
`(0 ↦ grade 0 (modified, reads col 1), 1 ↦ grade 1 (kept))` is block-triangular with identity diagonal
blocks: the single off-diagonal `c = M 0 1` has `b 1 = 1 > 0 = b 0`, so it is NOT a `b j < b i` entry and
sits strictly off-grade. `det = 1` — the coupling `c` is det-irrelevant. -/
example (c : ℝ) :
    (!![(1 : ℝ), c; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  refine blockTri_identityDiag_det_one _ (fun i : Fin 2 => if i = 0 then 0 else 1) ?_ ?_
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i j hb
    fin_cases i <;> fin_cases j <;> simp_all

end DLNFibre.DLN.RLCT
