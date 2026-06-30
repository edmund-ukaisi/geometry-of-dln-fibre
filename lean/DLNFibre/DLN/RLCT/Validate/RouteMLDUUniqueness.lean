import DLNFibre.DLN.RLCT.Validate.RouteMSchurFrameDet

/-!
# LDU-product uniqueness (the R1-LOWER interior `injOn` atom #1)

For `t × t` matrices over `ℝ`, the unit-lower · diagonal · unit-upper factorization is **unique**
when the diagonal is nonzero:

    `(1 + lowMatL l) · diag q · (1 + upMatL u) = (1 + lowMatL l') · diag q' · (1 + upMatL u')`
    with `∀ i, q i ≠ 0`  ⟹  `l = l'`, `q = q'`, `u = u'`.

This is the foundational matrix-algebra atom consumed by `genm-r1lower`'s `kLens`-injective leg
(`injon-skeleton.md`, atom #1). It is standalone (no Mathlib LU-uniqueness lemma is directly usable)
and reusable bedrock. The proof is the inverse/conjugation route: rearrange to
`P · diag q = diag q' · Q` with `P = (1+L')⁻¹·(1+L)` unit-lower and `Q = (1+U')·(1+U)⁻¹`
unit-upper, read entries (`P i j · q j = q' i · Q i j`), and use the strict triangularity of
`P, Q` together with `q i ≠ 0` to force `q = q'`, `P = 1`, `Q = 1`.

The unit-triangular factors are `BlockTriangular` (`OrderDual.toDual` for lower, `id` for upper)
with all diagonal entries `1`, hence determinant `1` and invertible; the inverse of a
block-triangular matrix is block-triangular (`Matrix.blockTriangular_inv_of_blockTriangular`).
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped Matrix

namespace RouteMLDUUniqueness

variable {t : ℕ}

/-! ## Block-triangularity of the unit-triangular factors -/

/-- `lowMatL l` is block-lower-triangular (zero on and above the diagonal, w.r.t. `toDual`). -/
theorem lowMatL_blockTri (l : LowIdx t → ℝ) :
    (lowMatL l).BlockTriangular OrderDual.toDual := by
  intro i j hij
  -- `toDual j < toDual i ↔ i < j`, i.e. `i < j` (above the diagonal): `lowMatL l i j = 0`.
  have hlt : i < j := by simpa using hij
  rw [lowMatL_apply, dif_neg (asymm hlt)]

/-- `upMatL u` is block-upper-triangular (zero on and below the diagonal, w.r.t. `id`). -/
theorem upMatL_blockTri (u : UpIdx t → ℝ) :
    (upMatL u).BlockTriangular id := by
  intro i j hij
  -- `id j < id i ↔ j < i` (below the diagonal): `upMatL u i j = 0`.
  have hlt : j < i := hij
  rw [upMatL_apply, dif_neg (asymm hlt)]

/-- `1 + lowMatL l` is block-lower-triangular. -/
theorem oneAddLow_blockTri (l : LowIdx t → ℝ) :
    ((1 : Matrix (Fin t) (Fin t) ℝ) + lowMatL l).BlockTriangular OrderDual.toDual :=
  (blockTriangular_one).add (lowMatL_blockTri l)

/-- `1 + upMatL u` is block-upper-triangular. -/
theorem oneAddUp_blockTri (u : UpIdx t → ℝ) :
    ((1 : Matrix (Fin t) (Fin t) ℝ) + upMatL u).BlockTriangular id :=
  (blockTriangular_one).add (upMatL_blockTri u)

/-! ## Diagonal entries are `1` -/

/-- `(1 + lowMatL l)` has all diagonal entries `1`. -/
@[simp] theorem oneAddLow_diag (l : LowIdx t → ℝ) (i : Fin t) :
    ((1 : Matrix (Fin t) (Fin t) ℝ) + lowMatL l) i i = 1 := by
  rw [Matrix.add_apply, Matrix.one_apply_eq, lowMatL_apply, dif_neg (lt_irrefl _), add_zero]

/-- `(1 + upMatL u)` has all diagonal entries `1`. -/
@[simp] theorem oneAddUp_diag (u : UpIdx t → ℝ) (i : Fin t) :
    ((1 : Matrix (Fin t) (Fin t) ℝ) + upMatL u) i i = 1 := by
  rw [Matrix.add_apply, Matrix.one_apply_eq, upMatL_apply, dif_neg (lt_irrefl _), add_zero]

/-! ## Determinant `1`, hence invertibility -/

/-- `det (1 + lowMatL l) = 1`. -/
theorem oneAddLow_det (l : LowIdx t → ℝ) :
    ((1 : Matrix (Fin t) (Fin t) ℝ) + lowMatL l).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (oneAddLow_blockTri l)]
  simp

/-- `det (1 + upMatL u) = 1`. -/
theorem oneAddUp_det (u : UpIdx t → ℝ) :
    ((1 : Matrix (Fin t) (Fin t) ℝ) + upMatL u).det = 1 := by
  rw [Matrix.det_of_upperTriangular (oneAddUp_blockTri u)]
  simp

/-- `det (1 + lowMatL l)` is a unit. -/
theorem oneAddLow_isUnit_det (l : LowIdx t → ℝ) :
    IsUnit ((1 : Matrix (Fin t) (Fin t) ℝ) + lowMatL l).det := by
  rw [oneAddLow_det]; exact isUnit_one

/-- `det (1 + upMatL u)` is a unit. -/
theorem oneAddUp_isUnit_det (u : UpIdx t → ℝ) :
    IsUnit ((1 : Matrix (Fin t) (Fin t) ℝ) + upMatL u).det := by
  rw [oneAddUp_det]; exact isUnit_one

/-! ## The diagonal of a product of two same-handed triangular matrices

Stated with the triangularity given as the entrywise zero condition over `Fin t`'s native `<`
(lower: zero strictly above the diagonal; upper: zero strictly below). For the diagonal entry of the
product only the `k = i` term of `∑_k A i k · B k i` survives. -/

/-- Diagonal of a product of two **lower**-triangular matrices: `(A·B) i i = A i i · B i i`. Here
"lower-triangular" is `A i j = 0` whenever `i < j`. -/
theorem lowerTri_mul_diag {A B : Matrix (Fin t) (Fin t) ℝ}
    (hA : ∀ i j, i < j → A i j = 0) (hB : ∀ i j, i < j → B i j = 0) (i : Fin t) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_trichotomy k i with h | h | h
    · rw [hB k i h, mul_zero]
    · exact absurd h hk
    · rw [hA i k h, zero_mul]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- Diagonal of a product of two **upper**-triangular matrices: `(A·B) i i = A i i · B i i`. Here
"upper-triangular" is `A i j = 0` whenever `j < i`. -/
theorem upperTri_mul_diag {A B : Matrix (Fin t) (Fin t) ℝ}
    (hA : ∀ i j, j < i → A i j = 0) (hB : ∀ i j, j < i → B i j = 0) (i : Fin t) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_trichotomy k i with h | h | h
    · rw [hA i k h, zero_mul]
    · exact absurd h hk
    · rw [hB k i h, mul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-! ## Triangularity in the `Fin t`-native `<` form

Translate `BlockTriangular · toDual` / `BlockTriangular · id` into the entrywise zero conditions
`i < j → … = 0` (lower) / `j < i → … = 0` (upper) that `lowerTri_mul_diag`/`upperTri_mul_diag`
consume. -/

/-- `BlockTriangular · toDual` ⟺ zero strictly above the diagonal. -/
theorem lowerTri_of_blockTri {A : Matrix (Fin t) (Fin t) ℝ}
    (hA : A.BlockTriangular OrderDual.toDual) (i j : Fin t) (hij : i < j) : A i j = 0 :=
  hA (by simpa using hij)

/-- `BlockTriangular · id` ⟺ zero strictly below the diagonal. -/
theorem upperTri_of_blockTri {A : Matrix (Fin t) (Fin t) ℝ} (hA : A.BlockTriangular id)
    (i j : Fin t) (hij : j < i) : A i j = 0 :=
  hA hij

/-! ## The main uniqueness theorem -/

/-- **LDU-product uniqueness.** The unit-lower · diagonal · unit-upper factorization is unique when
the diagonal is nonzero: if
`(1 + lowMatL l) · diag q · (1 + upMatL u) = (1 + lowMatL l') · diag q' · (1 + upMatL u')`
and `∀ i, q i ≠ 0`, then `l = l'`, `q = q'`, `u = u'`. -/
theorem lduCore_unique (l l' : LowIdx t → ℝ) (q q' : Fin t → ℝ) (u u' : UpIdx t → ℝ)
    (hq : ∀ i, q i ≠ 0)
    (hprod : (1 + lowMatL l) * Matrix.diagonal q * (1 + upMatL u)
           = (1 + lowMatL l') * Matrix.diagonal q' * (1 + upMatL u')) :
    l = l' ∧ q = q' ∧ u = u' := by
  -- Abbreviations for the four unit factors.
  set Ll : Matrix (Fin t) (Fin t) ℝ := 1 + lowMatL l with hLl
  set Ll' : Matrix (Fin t) (Fin t) ℝ := 1 + lowMatL l' with hLl'
  set Uu : Matrix (Fin t) (Fin t) ℝ := 1 + upMatL u with hUu
  set Uu' : Matrix (Fin t) (Fin t) ℝ := 1 + upMatL u' with hUu'
  -- Block-triangularity of the four factors.
  have hLlBT : Ll.BlockTriangular OrderDual.toDual := oneAddLow_blockTri l
  have hLl'BT : Ll'.BlockTriangular OrderDual.toDual := oneAddLow_blockTri l'
  have hUuBT : Uu.BlockTriangular id := oneAddUp_blockTri u
  have hUu'BT : Uu'.BlockTriangular id := oneAddUp_blockTri u'
  -- The four factors are invertible (det = 1).
  have hLlU : IsUnit Ll.det := oneAddLow_isUnit_det l
  have hLl'U : IsUnit Ll'.det := oneAddLow_isUnit_det l'
  have hUuU : IsUnit Uu.det := oneAddUp_isUnit_det u
  have hUu'U : IsUnit Uu'.det := oneAddUp_isUnit_det u'
  -- The conjugation matrices `P` (lower) and `Q` (upper).
  set P : Matrix (Fin t) (Fin t) ℝ := Ll'⁻¹ * Ll with hP
  set Q : Matrix (Fin t) (Fin t) ℝ := Uu' * Uu⁻¹ with hQ
  -- `P` and `Q` are block-triangular (inverse of triangular is triangular; product preserves).
  have hPinvBT : (Ll'⁻¹).BlockTriangular OrderDual.toDual :=
    haveI : Invertible Ll' := Ll'.invertibleOfIsUnitDet hLl'U
    Matrix.blockTriangular_inv_of_blockTriangular hLl'BT
  have hQinvBT : (Uu⁻¹).BlockTriangular id :=
    haveI : Invertible Uu := Uu.invertibleOfIsUnitDet hUuU
    Matrix.blockTriangular_inv_of_blockTriangular hUuBT
  have hPBT : P.BlockTriangular OrderDual.toDual := hPinvBT.mul hLlBT
  have hQBT : Q.BlockTriangular id := hUu'BT.mul hQinvBT
  -- The rearranged equation `P · diag q = diag q' · Q`, derived by conjugating `hprod`:
  -- left-multiply by `Ll'⁻¹` (kills `Ll'`), right-multiply by `Uu⁻¹` (kills `Uu`).
  have hkey : P * Matrix.diagonal q = Matrix.diagonal q' * Q := by
    rw [hP, hQ]
    -- Conjugate `hprod` by `Ll'⁻¹ · _ · Uu⁻¹`, then cancel via the `@[simp]` inverse lemmas.
    have h := congrArg (fun M => Ll'⁻¹ * M * Uu⁻¹) hprod
    simp only at h
    simp only [Matrix.mul_assoc] at h ⊢
    rw [Matrix.mul_nonsing_inv _ hUuU, Matrix.mul_one] at h
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ hLl'U] at h
    exact h
  -- Triangularity of `P, Q` in `Fin t`-native form.
  have hPlo : ∀ i j, i < j → P i j = 0 := lowerTri_of_blockTri hPBT
  have hQup : ∀ i j, j < i → Q i j = 0 := upperTri_of_blockTri hQBT
  -- Diagonal entries of `P` and `Q` are `1`.
  have hLl'lo : ∀ i j, i < j → Ll' i j = 0 := lowerTri_of_blockTri hLl'BT
  have hUu'up : ∀ i j, j < i → Uu' i j = 0 := upperTri_of_blockTri hUu'BT
  have hUuup : ∀ i j, j < i → Uu i j = 0 := upperTri_of_blockTri hUuBT
  -- Diagonal entries of the four unit factors are `1` (abbreviation-level form).
  have hLldiag : ∀ i, Ll i i = 1 := fun i => by rw [hLl]; exact oneAddLow_diag l i
  have hLl'diag : ∀ i, Ll' i i = 1 := fun i => by rw [hLl']; exact oneAddLow_diag l' i
  have hUudiag : ∀ i, Uu i i = 1 := fun i => by rw [hUu]; exact oneAddUp_diag u i
  have hUu'diag : ∀ i, Uu' i i = 1 := fun i => by rw [hUu']; exact oneAddUp_diag u' i
  have hPdiag : ∀ i, P i i = 1 := by
    intro i
    -- `Ll' * P = Ll'·(Ll'⁻¹·Ll) = Ll`, and `(Ll'·P) i i = Ll' i i · P i i = P i i`.
    have hmul : Ll' * P = Ll := by
      rw [hP, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hLl'U, Matrix.one_mul]
    have hd := lowerTri_mul_diag hLl'lo hPlo i
    rw [hmul, hLldiag, hLl'diag, one_mul] at hd
    exact hd.symm
  have hQdiag : ∀ i, Q i i = 1 := by
    intro i
    -- `Q * Uu = (Uu'·Uu⁻¹)·Uu = Uu'`, and `(Q·Uu) i i = Q i i · Uu i i = Q i i`.
    have hmul : Q * Uu = Uu' := by
      rw [hQ, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hUuU, Matrix.mul_one]
    have hd := upperTri_mul_diag hQup hUuup i
    rw [hmul, hUu'diag, hUudiag, mul_one] at hd
    exact hd.symm
  -- The entry equation `P i j · q j = q' i · Q i j`.
  have hentry : ∀ i j, P i j * q j = q' i * Q i j := by
    intro i j
    have := congrFun (congrFun hkey i) j
    rwa [Matrix.mul_diagonal, Matrix.diagonal_mul] at this
  -- `q = q'` from the diagonal.
  have hqeq : q = q' := by
    funext i
    have := hentry i i
    rw [hPdiag, hQdiag, one_mul, mul_one] at this
    exact this
  -- `P = 1` and `Q = 1`.
  have hP1 : P = 1 := by
    funext i j
    rw [Matrix.one_apply]
    rcases lt_trichotomy i j with h | h | h
    · -- `i < j`: `P i j = 0` directly.
      rw [if_neg (ne_of_lt h), hPlo i j h]
    · rw [if_pos h, ← h, hPdiag]
    · -- `j < i`: `Q i j = 0` (upper), so `P i j · q j = 0`, `q j ≠ 0`.
      rw [if_neg (ne_of_gt h)]
      have he := hentry i j
      rw [hQup i j h, mul_zero] at he
      exact (mul_eq_zero.mp he).resolve_right (hq j)
  have hQ1 : Q = 1 := by
    funext i j
    rw [Matrix.one_apply]
    rcases lt_trichotomy i j with h | h | h
    · -- `i < j`: `P i j = 0` (lower), so `0 = q' i · Q i j`, `q' i = q i ≠ 0`.
      rw [if_neg (ne_of_lt h)]
      have he := hentry i j
      rw [hPlo i j h, zero_mul] at he
      have : q' i ≠ 0 := by rw [← hqeq]; exact hq i
      exact (mul_eq_zero.mp he.symm).resolve_left this
    · rw [if_pos h, ← h, hQdiag]
    · rw [if_neg (ne_of_gt h), hQup i j h]
  -- Recover `Ll = Ll'` and `Uu = Uu'`.
  have hLeq : Ll = Ll' := by
    -- `P = 1` ⟹ `Ll'⁻¹ * Ll = 1` ⟹ `Ll = Ll'`.
    have : Ll'⁻¹ * Ll = 1 := by rw [← hP]; exact hP1
    have h2 := congrArg (fun M => Ll' * M) this
    simp only at h2
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hLl'U, Matrix.one_mul, Matrix.mul_one] at h2
    exact h2
  have hUeq : Uu = Uu' := by
    -- `Q = 1` ⟹ `Uu' * Uu⁻¹ = 1` ⟹ `Uu' = Uu`.
    have : Uu' * Uu⁻¹ = 1 := by rw [← hQ]; exact hQ1
    have h2 := congrArg (fun M => M * Uu) this
    simp only at h2
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hUuU, Matrix.mul_one, Matrix.one_mul] at h2
    exact h2.symm
  -- Extract the coordinate functions from the matrix equalities.
  refine ⟨?_, hqeq, ?_⟩
  · -- `lowMatL l = lowMatL l'` from `Ll = Ll'`; read off strict-lower entries.
    funext p
    obtain ⟨⟨i, j⟩, hp⟩ := p
    have hentry : Ll i j = Ll' i j := by rw [hLeq]
    rw [hLl, hLl', Matrix.add_apply, Matrix.add_apply, lowMatL_apply, lowMatL_apply,
      dif_pos hp, dif_pos hp] at hentry
    simpa using add_left_cancel hentry
  · -- `upMatL u = upMatL u'` from `Uu = Uu'`; read off strict-upper entries.
    funext p
    obtain ⟨⟨i, j⟩, hp⟩ := p
    have hentry : Uu i j = Uu' i j := by rw [hUeq]
    rw [hUu, hUu', Matrix.add_apply, Matrix.add_apply, upMatL_apply, upMatL_apply,
      dif_pos hp, dif_pos hp] at hentry
    simpa using add_left_cancel hentry

end RouteMLDUUniqueness

end DLNFibre.DLN.RLCT
