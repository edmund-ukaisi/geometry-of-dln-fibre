import Mathlib

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSchurShear` — the Cramer minor-ratio shear bound (N2b long-pole)

The load-bearing bridge that makes the N2b two-sided comparison constants ABSOLUTE: on the bounded
complete-pivoting cell (where the top-left `j×j` minor `M11` is a **max-modulus** `j×j` minor), every
entry of the Gauss shear `M11⁻¹·M12` (and its transpose-dual `M21·M11⁻¹`) has modulus `≤ 1`.

This is the classical **complete-pivoting** fact (`minorpivot-cert.md` R2, sympy-exact for `(r,k)` up to
`(4,3)`): each shear entry is a Cramer minor-ratio `(a j×j minor of R)/det M11`, and the numerator minor
is `≤ |det M11|` in modulus because `M11` is the max-modulus minor.

The chain (all four steps pinned against Mathlib v4.29):
* `(M11⁻¹ * M12) i b = (M11⁻¹ *ᵥ (M12 col b)) i`                      (matrix-product = mulVec entry)
* `(M11⁻¹ *ᵥ v) i = (det M11)⁻¹ * (M11.updateCol i v).det`            (`inv_def` + `cramer_apply`)
* `M11.updateCol i (M12 col b) = R.submatrix top (update cols i (j+b))`  (updateCol = column-swap submatrix)
* `|(M11.updateCol i v).det| ≤ |det M11|`                              (the `hpivot` max-minor bound)

The numerator submatrix is a genuine `j×j` minor of `R` (top-block rows; columns = `M11`'s columns with
one swapped for an `M12` column), so the supplied `hpivot` (∀ `j×j` minors `≤ |M11.det|`) applies directly.
-/

open Matrix

namespace DLNFibre.DLN.RLCT

/-- `(M11⁻¹ *ᵥ v) i = (det M11)⁻¹ · (M11.updateCol i v).det` — the Cramer entry form of an inverse-mulVec
(no invertibility hypothesis; `det⁻¹` is the field inverse). -/
theorem inv_mulVec_eq_cramer_ratio {j : ℕ} (M11 : Matrix (Fin j) (Fin j) ℝ) (v : Fin j → ℝ)
    (i : Fin j) :
    (M11⁻¹ *ᵥ v) i = (M11.det)⁻¹ * (M11.updateCol i v).det := by
  rw [Matrix.inv_def, Matrix.smul_mulVec, Pi.smul_apply, ← Matrix.cramer_eq_adjugate_mulVec,
    Matrix.cramer_apply]
  simp [Ring.inverse_eq_inv']

/-- `(M11⁻¹ * M12) i b = (M11⁻¹ *ᵥ (b-th column of M12)) i`. -/
theorem inv_mul_eq_inv_mulVec_col {j n : ℕ} (M11 : Matrix (Fin j) (Fin j) ℝ)
    (M12 : Matrix (Fin j) (Fin n) ℝ) (i : Fin j) (b : Fin n) :
    (M11⁻¹ * M12) i b = (M11⁻¹ *ᵥ (fun k => M12 k b)) i := by
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

/-- `M11.updateCol i v = R.submatrix top (Function.update leftCols i rightCol)` when `M11` is the
`(top, leftCols)`-submatrix of `R` and `v` is the `rightCol`-column of the `top`-rows of `R`: replacing
column `i` of the minor by an outside column `rightCol` is the same minor with the column index
swapped. -/
theorem updateCol_submatrix_eq {r j : ℕ} (R : Matrix (Fin r) (Fin r) ℝ)
    (top : Fin j → Fin r) (leftCols : Fin j → Fin r) (rightCol : Fin r) (i : Fin j) :
    (R.submatrix top leftCols).updateCol i (fun a => R (top a) rightCol)
      = R.submatrix top (Function.update leftCols i rightCol) := by
  ext a c
  rw [Matrix.updateCol_apply]
  by_cases h : c = i
  · subst h; simp [Matrix.submatrix_apply]
  · simp [Matrix.submatrix_apply, h]

/-- **The column-shear minor-ratio bound.** On the max-modulus-`j`-minor cell, every entry of the Gauss
column shear `M11⁻¹·M12` has modulus `≤ 1`. Here `M11 = R.submatrix top leftCols` (the `j×j` pivot
minor), `M12 = R.submatrix top rightCols` (the top-rows at the columns `rightCols`); the column-swap
minors stay `j×j` minors of `R`, so `hpivot` bounds the numerator. -/
theorem colShear_entry_le_one {r j n : ℕ} (R : Matrix (Fin r) (Fin r) ℝ)
    (top : Fin j → Fin r) (leftCols : Fin j → Fin r) (rightCols : Fin n → Fin r)
    (hpivot : ∀ (I : Fin j → Fin r) (J : Fin j → Fin r),
        |(R.submatrix I J).det| ≤ |(R.submatrix top leftCols).det|)
    (hne : (R.submatrix top leftCols).det ≠ 0)
    (i : Fin j) (b : Fin n) :
    |((R.submatrix top leftCols)⁻¹ * (R.submatrix top rightCols)) i b| ≤ 1 := by
  set M11 := R.submatrix top leftCols with hM11
  -- the b-th column of M12 = R.submatrix top rightCols is `fun a => R (top a) (rightCols b)`
  have hcol : (fun k => (R.submatrix top rightCols) k b) = (fun a => R (top a) (rightCols b)) := by
    funext a; simp [Matrix.submatrix_apply]
  rw [inv_mul_eq_inv_mulVec_col, hcol, inv_mulVec_eq_cramer_ratio,
    updateCol_submatrix_eq R top leftCols (rightCols b) i]
  rw [abs_mul, abs_inv]
  -- |det M11|⁻¹ · |minor| ≤ 1  ⟺  |minor| ≤ |det M11|
  have hpos : 0 < |M11.det| := abs_pos.2 hne
  rw [inv_mul_eq_div, div_le_one hpos]
  exact hpivot top (Function.update leftCols i (rightCols b))

/-- **The row-shear minor-ratio bound** (the transpose dual of `colShear_entry_le_one`). On the
max-modulus-`j`-minor cell, every entry of the Gauss row shear `M21·M11⁻¹` has modulus `≤ 1`. Here
`M21 = R.submatrix botRows leftCols` (the bottom-rows at the pivot columns) and the row-swap minors
stay `j×j` minors of `R` (read off `Rᵀ`), so `hpivot` bounds the numerator. -/
theorem rowShear_entry_le_one {r j m : ℕ} (R : Matrix (Fin r) (Fin r) ℝ)
    (top : Fin j → Fin r) (leftCols : Fin j → Fin r) (botRows : Fin m → Fin r)
    (hpivot : ∀ (I : Fin j → Fin r) (J : Fin j → Fin r),
        |(R.submatrix I J).det| ≤ |(R.submatrix top leftCols).det|)
    (hne : (R.submatrix top leftCols).det ≠ 0)
    (a : Fin m) (i : Fin j) :
    |((R.submatrix botRows leftCols) * (R.submatrix top leftCols)⁻¹) a i| ≤ 1 := by
  -- transpose to a column shear on `Rᵀ`: ((M21·M11⁻¹)ᵀ) i a = ((M11ᵀ)⁻¹ · M21ᵀ) i a.
  set M11 := R.submatrix top leftCols with hM11
  have htr : ((R.submatrix botRows leftCols) * M11⁻¹) a i
      = (M11ᵀ⁻¹ * (R.submatrix botRows leftCols)ᵀ) i a := by
    rw [← Matrix.transpose_nonsing_inv, ← Matrix.transpose_mul, Matrix.transpose_apply]
  rw [htr]
  -- Now M11ᵀ = Rᵀ.submatrix leftCols top, (M21)ᵀ = Rᵀ.submatrix leftCols botRows: a col shear on Rᵀ.
  -- a minor of Rᵀ is `(R.submatrix J I)ᵀ`, det invariant under transpose, so hpivot transfers.
  have hpivotT : ∀ (I : Fin j → Fin r) (J : Fin j → Fin r),
      |(Rᵀ.submatrix I J).det| ≤ |(Rᵀ.submatrix leftCols top).det| := by
    intro I J
    rw [← Matrix.transpose_submatrix, Matrix.det_transpose, ← Matrix.transpose_submatrix,
      Matrix.det_transpose]
    exact hpivot J I
  have hneT : (Rᵀ.submatrix leftCols top).det ≠ 0 := by
    rw [← Matrix.transpose_submatrix, Matrix.det_transpose]; rwa [hM11] at hne
  have hM11T : M11ᵀ = Rᵀ.submatrix leftCols top := by
    rw [hM11, Matrix.transpose_submatrix]
  have hM21T : (R.submatrix botRows leftCols)ᵀ = Rᵀ.submatrix leftCols botRows := by
    rw [Matrix.transpose_submatrix]
  rw [hM11T, hM21T]
  exact colShear_entry_le_one Rᵀ leftCols top botRows hpivotT hneT i a

end DLNFibre.DLN.RLCT
