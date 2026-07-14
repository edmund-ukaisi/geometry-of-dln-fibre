import DLNFibre.DLN.RLCT.Validate.RouteMSJPivotBlowup
import Mathlib.Data.Matrix.ColumnRowPartitioned

set_option linter.style.longLine false

/-!
# `RouteMSJIncidenceChart` — Brick D joint-resolution: the minor-chart corank-Gram monomialization

**Thread `genm-sj5-brickdbuild`, aoyagi-full Stage 2.** The load-bearing algebraic identity the
incidence-rank resolution (`genm-incidencepp/incidence-cert.md`) is built around: on the `b×b`-minor chart
`Q_b = D·[I_b | X]` (`D : b×b`, `X : b×d`, `n = b+d`), the corank Gram factors as

    det(Q_b Q_bᵀ) = (det D)² · det(I_b + X Xᵀ).

The rank-drop singularity lives ENTIRELY in `|det D|` (the incidence monomial); `det(I + X Xᵀ) ≥ 1` is a
unit (bounded away from 0), and `X` (the transverse-Schur coordinate) is independent of `D`. This
disjoint-variable factoring is what lets the det-Gram and the transverse Schur monomialize simultaneously
with no blow-up conflict (cert §0, §2). Network-free matrix algebra; sorry-free; axiom-clean.
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped BigOperators

/-- **The column-partitioned Gram** `(fromCols U V)·(fromCols U V)ᵀ = U Uᵀ + V Vᵀ`. The reusable block
identity behind every chart-Gram computation (`transpose_fromCols` + `fromCols_mul_fromRows`). -/
theorem fromCols_mul_transpose {m n₁ n₂ : ℕ} (U : Matrix (Fin m) (Fin n₁) ℝ)
    (V : Matrix (Fin m) (Fin n₂) ℝ) :
    (Matrix.fromCols U V) * (Matrix.fromCols U V)ᵀ = U * Uᵀ + V * Vᵀ := by
  rw [Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows]

/-- **The minor-chart Gram congruence.** For `Q_b = D·[I_b | X]` (`[I_b | X] = fromCols 1 X`), the corank
Gram is the congruence `D·(I + X Xᵀ)·Dᵀ`: the block product `[I|X]·[I|X]ᵀ = I·I + X·Xᵀ = I + X Xᵀ`. -/
theorem chartGram_congr {b d : ℕ} (D : Matrix (Fin b) (Fin b) ℝ) (X : Matrix (Fin b) (Fin d) ℝ) :
    (D * Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X) * (D * Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X)ᵀ
      = D * ((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ) * Dᵀ := by
  have hE : (Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X)
      * (Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X)ᵀ
      = (1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ := by
    have h11 : (1 : Matrix (Fin b) (Fin b) ℝ) * (1 : Matrix (Fin b) (Fin b) ℝ)ᵀ = 1 := by
      rw [Matrix.transpose_one, Matrix.one_mul]
    rw [Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows, h11]
  calc (D * Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X) * (D * Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X)ᵀ
      = D * ((Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X) * (Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X)ᵀ) * Dᵀ := by
        rw [Matrix.transpose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc D]
    _ = D * ((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ) * Dᵀ := by rw [hE]

/-- **The corank-Gram monomialization (cert §0 load-bearing identity).** On the `b×b`-minor chart
`Q_b = D·[I_b | X]`, `det(Q_b Q_bᵀ) = (det D)² · det(I_b + X Xᵀ)` — the rank-drop singularity is the
`(det D)²` monomial; `det(I + X Xᵀ)` is a `D`-independent unit `≥ 1`. -/
theorem det_chartGram {b d : ℕ} (D : Matrix (Fin b) (Fin b) ℝ) (X : Matrix (Fin b) (Fin d) ℝ) :
    ((D * Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X) * (D * Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X)ᵀ).det
      = (D.det) ^ 2 * (1 + X * Xᵀ).det := by
  rw [chartGram_congr, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]; ring

/-! ## The transverse-Schur push-through (Woodbury) -/

/-- **The push-through identity** `(I_d + Xᵀ X)⁻¹ = I_b − Xᵀ (I_b + X Xᵀ)⁻¹ X` (Woodbury at
`A = 1, U = Xᵀ, C = 1, V = X`). The algebraic heart of the transverse-Schur monomialization: it converts
the `b×b` Schur residual `I − Xᵀ (I + X Xᵀ)⁻¹ X` into the `d×d` inverse Gram `(I + Xᵀ X)⁻¹`. Needs
`I + X Xᵀ` invertible (holds on the full-rank chart: `I + X Xᵀ ≻ 0`). -/
theorem pushThrough {b d : ℕ} (X : Matrix (Fin b) (Fin d) ℝ)
    (h : IsUnit ((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ)) :
    ((1 : Matrix (Fin d) (Fin d) ℝ) + Xᵀ * X)⁻¹
      = 1 - Xᵀ * ((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ)⁻¹ * X := by
  have hAC : IsUnit ((1 : Matrix (Fin b) (Fin b) ℝ)⁻¹
      + X * (1 : Matrix (Fin d) (Fin d) ℝ)⁻¹ * Xᵀ) := by simpa using h
  have key := Matrix.add_mul_mul_inv_eq_sub (1 : Matrix (Fin d) (Fin d) ℝ) Xᵀ 1 X
    isUnit_one isUnit_one hAC
  simpa using key

/-! ## The chart null direction `N = [−X ; I_d]` — the transverse Schur monomialized by `W` -/

/-- The chart null direction `N = [−X ; I_d]` (`n×d`) annihilates `Q_b = D·[I_b | X]`: `Q_b · N = 0`
(so `col N = ker Q_b = (row Q_b)^⊥`, the transverse subspace `I − Π_b` projects onto). -/
theorem chartNull_Qb {b d : ℕ} (D : Matrix (Fin b) (Fin b) ℝ) (X : Matrix (Fin b) (Fin d) ℝ) :
    (D * Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X)
        * Matrix.fromRows (-X) (1 : Matrix (Fin d) (Fin d) ℝ) = 0 := by
  rw [Matrix.mul_assoc, Matrix.fromCols_mul_fromRows]
  simp

/-- The pivot rows map the null direction to `W`: `Q_p · N = W` for `Q_p = [U | U X + W]`. This is the
transverse-Schur monomialization — the transverse energy of `Q_p` is carried entirely by `W`. -/
theorem chartNull_Qp {u b d : ℕ} (U : Matrix (Fin u) (Fin b) ℝ) (W : Matrix (Fin u) (Fin d) ℝ)
    (X : Matrix (Fin b) (Fin d) ℝ) :
    Matrix.fromCols U (U * X + W) * Matrix.fromRows (-X) (1 : Matrix (Fin d) (Fin d) ℝ) = W := by
  rw [Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_neg, neg_add_cancel_left]

/-- The null-direction Gram `Nᵀ N = I_d + Xᵀ X` — the `d×d` inverse Gram that monomializes the transverse
Schur: `Q_p (I − Π_b) Q_pᵀ = W (Nᵀ N)⁻¹ Wᵀ = W (I + Xᵀ X)⁻¹ Wᵀ`. -/
theorem chartNull_gram {b d : ℕ} (X : Matrix (Fin b) (Fin d) ℝ) :
    (Matrix.fromRows (-X) (1 : Matrix (Fin d) (Fin d) ℝ))ᵀ
        * Matrix.fromRows (-X) (1 : Matrix (Fin d) (Fin d) ℝ)
      = (1 : Matrix (Fin d) (Fin d) ℝ) + Xᵀ * X := by
  rw [Matrix.transpose_fromRows, Matrix.fromCols_mul_fromRows]
  simp only [Matrix.transpose_neg, Matrix.transpose_one, Matrix.neg_mul, Matrix.mul_neg,
    Matrix.one_mul]
  abel

/-- **The swap identity** `(I_b + X Xᵀ)⁻¹ X = X (I_d + Xᵀ X)⁻¹` — the second ingredient (with
`pushThrough`) of the block-route projection identity `I − Π_b = N(NᵀN)⁻¹Nᵀ`. From the commutation
`(I + X Xᵀ) X = X (I + Xᵀ X)` (both `= X + X Xᵀ X`), inverting on both sides. -/
theorem chartSwap {b d : ℕ} (X : Matrix (Fin b) (Fin d) ℝ)
    (hA : IsUnit ((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ).det)
    (hB : IsUnit ((1 : Matrix (Fin d) (Fin d) ℝ) + Xᵀ * X).det) :
    ((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ)⁻¹ * X
      = X * ((1 : Matrix (Fin d) (Fin d) ℝ) + Xᵀ * X)⁻¹ := by
  have hcomm : ((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ) * X
      = X * ((1 : Matrix (Fin d) (Fin d) ℝ) + Xᵀ * X) := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
    exact congrArg (X + ·) (Matrix.mul_assoc X Xᵀ X)
  calc ((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ)⁻¹ * X
      = ((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ)⁻¹ * X
          * (((1 : Matrix (Fin d) (Fin d) ℝ) + Xᵀ * X) * ((1 : Matrix (Fin d) (Fin d) ℝ) + Xᵀ * X)⁻¹) := by
        rw [Matrix.mul_nonsing_inv _ hB, Matrix.mul_one]
    _ = ((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ)⁻¹
          * (((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ) * X) * ((1 : Matrix (Fin d) (Fin d) ℝ) + Xᵀ * X)⁻¹ := by
        rw [← Matrix.mul_assoc (((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ)⁻¹ * X)
              ((1 : Matrix (Fin d) (Fin d) ℝ) + Xᵀ * X) (((1 : Matrix (Fin d) (Fin d) ℝ) + Xᵀ * X)⁻¹),
          Matrix.mul_assoc (((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ)⁻¹) X
              ((1 : Matrix (Fin d) (Fin d) ℝ) + Xᵀ * X), hcomm]
    _ = X * ((1 : Matrix (Fin d) (Fin d) ℝ) + Xᵀ * X)⁻¹ := by
        rw [← Matrix.mul_assoc (((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ)⁻¹)
              ((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ) X, Matrix.nonsing_inv_mul _ hA,
          Matrix.one_mul]

/-! ## The block-route projection complement `I − Π_b = N (NᵀN)⁻¹ Nᵀ` and the transverse-Schur Gram -/

/-- **D-cancellation (cert §0 / build-design).** The orthogonal projection onto `row(Q_b)` for
`Q_b = D·[I | X]` is `D`-independent: `Q_bᵀ(Q_bQ_bᵀ)⁻¹Q_b = [I;Xᵀ]·(I+XXᵀ)⁻¹·[I|X]`. The `D` factors
cancel (`chartGram_congr` reduces the middle Gram, `mul_inv_rev` splits the inverse). Needs `D` invertible. -/
theorem chartProj_Dcancel {b d : ℕ} (D : Matrix (Fin b) (Fin b) ℝ) (X : Matrix (Fin b) (Fin d) ℝ)
    (hD : IsUnit D.det) :
    (D * Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X)ᵀ
        * ((D * Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X)
            * (D * Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X)ᵀ)⁻¹
        * (D * Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X)
      = Matrix.fromRows (1 : Matrix (Fin b) (Fin b) ℝ) Xᵀ * ((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ)⁻¹
          * Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X := by
  have hDt : IsUnit (Dᵀ).det := by rw [Matrix.det_transpose]; exact hD
  have hCt : (Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X)ᵀ = Matrix.fromRows 1 Xᵀ := by
    rw [Matrix.transpose_fromCols, Matrix.transpose_one]
  have hinv : (D * ((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ) * Dᵀ)⁻¹
      = Dᵀ⁻¹ * (((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ)⁻¹ * D⁻¹) := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  rw [chartGram_congr, hinv, Matrix.transpose_mul, hCt]
  simp only [Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left D (Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X) hD,
      Matrix.mul_nonsing_inv_cancel_left Dᵀ
        (((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ)⁻¹ * Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X)
        hDt]

/-- **The 4-block projection identity.** `Π_b + P_N = I_n` at the reduced (D-cancelled) level:
`[I;Xᵀ](I+XXᵀ)⁻¹[I|X] + N(I+XᵀX)⁻¹Nᵀ = I` for `N = [−X;I_d]`, `Nᵀ = [−Xᵀ|I_d]`. The four blocks match
`I_n = [[I,0],[0,I]]` via `pushThrough` (top-left + bottom-right) and `chartSwap` (the two off-diagonals). -/
theorem chartProjRed_block {b d : ℕ} (X : Matrix (Fin b) (Fin d) ℝ)
    (hP : IsUnit ((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ))
    (hQ : IsUnit ((1 : Matrix (Fin d) (Fin d) ℝ) + Xᵀ * X)) :
    Matrix.fromRows 1 Xᵀ * ((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ)⁻¹ * Matrix.fromCols 1 X
      + Matrix.fromRows (-X) 1 * ((1 : Matrix (Fin d) (Fin d) ℝ) + Xᵀ * X)⁻¹ * Matrix.fromCols (-Xᵀ) 1
      = 1 := by
  have hPdet := (Matrix.isUnit_iff_isUnit_det _).mp hP
  have hQdet := (Matrix.isUnit_iff_isUnit_det _).mp hQ
  have hPsym : (((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ)⁻¹)ᵀ
      = ((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv]; congr 1
    rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hQsym : (((1 : Matrix (Fin d) (Fin d) ℝ) + Xᵀ * X)⁻¹)ᵀ
      = ((1 : Matrix (Fin d) (Fin d) ℝ) + Xᵀ * X)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv]; congr 1
    rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hswapT : Xᵀ * ((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ)⁻¹
      = ((1 : Matrix (Fin d) (Fin d) ℝ) + Xᵀ * X)⁻¹ * Xᵀ := by
    have h := congrArg Matrix.transpose (chartSwap X hPdet hQdet)
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hPsym, hQsym] at h
    exact h
  have hTL : ((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ)⁻¹
      + X * ((1 : Matrix (Fin d) (Fin d) ℝ) + Xᵀ * X)⁻¹ * Xᵀ = 1 := by
    have hpt := pushThrough Xᵀ (by simpa using hQ)
    simp only [Matrix.transpose_transpose] at hpt
    rw [hpt]; abel
  have hBR : Xᵀ * ((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ)⁻¹ * X
      + ((1 : Matrix (Fin d) (Fin d) ℝ) + Xᵀ * X)⁻¹ = 1 := by
    rw [pushThrough X hP]; abel
  have hTR : ((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ)⁻¹ * X
      + -(X * ((1 : Matrix (Fin d) (Fin d) ℝ) + Xᵀ * X)⁻¹) = 0 := by
    rw [chartSwap X hPdet hQdet]; abel
  have hBL : Xᵀ * ((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ)⁻¹
      + -(((1 : Matrix (Fin d) (Fin d) ℝ) + Xᵀ * X)⁻¹ * Xᵀ) = 0 := by
    rw [hswapT]; abel
  have eT1 : Matrix.fromRows (1 : Matrix (Fin b) (Fin b) ℝ) Xᵀ
        * ((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ)⁻¹ * Matrix.fromCols 1 X
      = Matrix.fromBlocks (((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ)⁻¹)
          (((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ)⁻¹ * X)
          (Xᵀ * ((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ)⁻¹)
          (Xᵀ * ((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ)⁻¹ * X) := by
    rw [Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols]
    simp only [Matrix.one_mul, Matrix.mul_one]
  have eT2 : Matrix.fromRows (-X) (1 : Matrix (Fin d) (Fin d) ℝ)
        * ((1 : Matrix (Fin d) (Fin d) ℝ) + Xᵀ * X)⁻¹ * Matrix.fromCols (-Xᵀ) 1
      = Matrix.fromBlocks (X * ((1 : Matrix (Fin d) (Fin d) ℝ) + Xᵀ * X)⁻¹ * Xᵀ)
          (-(X * ((1 : Matrix (Fin d) (Fin d) ℝ) + Xᵀ * X)⁻¹))
          (-(((1 : Matrix (Fin d) (Fin d) ℝ) + Xᵀ * X)⁻¹ * Xᵀ))
          (((1 : Matrix (Fin d) (Fin d) ℝ) + Xᵀ * X)⁻¹) := by
    have hneg : (-X) * ((1 : Matrix (Fin d) (Fin d) ℝ) + Xᵀ * X)⁻¹ * (-Xᵀ)
        = X * ((1 : Matrix (Fin d) (Fin d) ℝ) + Xᵀ * X)⁻¹ * Xᵀ := by
      rw [Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_neg]; abel
    rw [Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols, hneg]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg]
  rw [eT1, eT2, Matrix.fromBlocks_add, hTL, hTR, hBL, hBR, Matrix.fromBlocks_one]

/-- **The projection complement `I − Π_b = N (NᵀN)⁻¹ Nᵀ`** for `Π_b = Q_bᵀ(Q_bQ_bᵀ)⁻¹Q_b` the orthogonal
projection onto `row(Q_b)`, `Q_b = D·[I|X]`, `N = [−X;I_d]`. Combines `chartProj_Dcancel` (drops `D`) with
`chartProjRed_block` (the 4-block match); `I − Π_b` is the orthogonal projection onto `ker(Q_b) = col(N)`. -/
theorem chartProjComplement {b d : ℕ} (D : Matrix (Fin b) (Fin b) ℝ) (X : Matrix (Fin b) (Fin d) ℝ)
    (hD : IsUnit D.det) (hP : IsUnit ((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ))
    (hQ : IsUnit ((1 : Matrix (Fin d) (Fin d) ℝ) + Xᵀ * X)) :
    (1 : Matrix (Fin b ⊕ Fin d) (Fin b ⊕ Fin d) ℝ)
      - (D * Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X)ᵀ
          * ((D * Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X)
              * (D * Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X)ᵀ)⁻¹
          * (D * Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X)
      = Matrix.fromRows (-X) (1 : Matrix (Fin d) (Fin d) ℝ)
          * ((Matrix.fromRows (-X) (1 : Matrix (Fin d) (Fin d) ℝ))ᵀ
              * Matrix.fromRows (-X) (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹
          * (Matrix.fromRows (-X) (1 : Matrix (Fin d) (Fin d) ℝ))ᵀ := by
  rw [chartProj_Dcancel D X hD, chartNull_gram, Matrix.transpose_fromRows, Matrix.transpose_neg,
    Matrix.transpose_one, ← chartProjRed_block X hP hQ]
  abel

/-- **The transverse-Schur Gram identity (cert §3, piece (i)).** For pivot rows `Q_p = [U | U X + W]`,
the transverse energy of `Q_p` on the complement of `row(Q_b)` is monomialised by `W`:
`Q_p (I − Π_b) Q_pᵀ = W (I + Xᵀ X)⁻¹ Wᵀ`. Wired from `chartProjComplement` (`I−Π_b = N(NᵀN)⁻¹Nᵀ`),
`chartNull_Qp` (`Q_p N = W`), and `chartNull_gram` (`NᵀN = I + XᵀX`). -/
theorem transverseSchurGram {u b d : ℕ} (D : Matrix (Fin b) (Fin b) ℝ) (X : Matrix (Fin b) (Fin d) ℝ)
    (U : Matrix (Fin u) (Fin b) ℝ) (W : Matrix (Fin u) (Fin d) ℝ)
    (hD : IsUnit D.det) (hP : IsUnit ((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ))
    (hQ : IsUnit ((1 : Matrix (Fin d) (Fin d) ℝ) + Xᵀ * X)) :
    Matrix.fromCols U (U * X + W)
      * ((1 : Matrix (Fin b ⊕ Fin d) (Fin b ⊕ Fin d) ℝ)
          - (D * Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X)ᵀ
              * ((D * Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X)
                  * (D * Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X)ᵀ)⁻¹
              * (D * Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X))
      * (Matrix.fromCols U (U * X + W))ᵀ
      = W * ((1 : Matrix (Fin d) (Fin d) ℝ) + Xᵀ * X)⁻¹ * Wᵀ := by
  have hQpN : Matrix.fromCols U (U * X + W) * Matrix.fromRows (-X) (1 : Matrix (Fin d) (Fin d) ℝ) = W :=
    chartNull_Qp U W X
  have hNQp : (Matrix.fromRows (-X) (1 : Matrix (Fin d) (Fin d) ℝ))ᵀ * (Matrix.fromCols U (U * X + W))ᵀ
      = Wᵀ := by
    rw [← Matrix.transpose_mul, hQpN]
  rw [chartProjComplement D X hD hP hQ, chartNull_gram]
  simp only [← Matrix.mul_assoc]
  rw [hQpN, Matrix.mul_assoc, hNQp]

end DLNFibre.DLN.RLCT
