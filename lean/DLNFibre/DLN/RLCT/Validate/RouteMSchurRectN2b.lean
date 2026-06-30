import DLNFibre.DLN.RLCT.Validate.RouteMSchur

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSchurRectN2b` — the RECTANGULAR N2b minor-pivot split

The asymmetric (`R : Fin m → Fin n`) generalisation of the square `schur_minorPivot_split`
(`RouteMSchur`, `R : Fin r → Fin r`). The two-sided uniform `frobSq` comparison with a `t×t` invertible
pivot minor `M11`, residual Schur complement `Sc : (m−t)×(n−t)`, output width `p`.

The core algebra is already block-dimension-generic — `schur_abstract_comparison {j s p}` (pivot dim `j`,
residual ROW dim `s`, S-width `p`) and the shear bounds `rowShear_entry_le_one` (independent index maps,
transpose-dualised) apply verbatim with `j = t`, `s = m − t`. The ONE genuinely new ingredient is a
two-residual-dim key identity `schur_key_identity_rect {j sr sc p}` (the square version
`schur_key_identity {j s p}` conflates the residual's row count `sr` and column count `sc` into one `s` —
fine when square, but the rectangular Schur complement is `(m−t)×(n−t)` with `sr = m−t ≠ sc = n−t`).

## The split shape (mirrors `schur_minorPivot_split` faithfully)

For `R : Fin m → Fin n`, `t ≤ m`, `t ≤ n`, on the bounded complete-pivoting cell (`|R| ≤ 1`, top-left
`t×t` minor `M11` is a max-modulus `t×t` minor, `det M11 ≠ 0`):

    c₀·(frobSq (R·S)_top + frobSq (Sc·S_bot)) ≤ frobSq (R·S) ≤ c₁·(frobSq (R·S)_top + frobSq (Sc·S_bot))

with `Sc = M22 − M21·M11⁻¹·M12 : (m−t)×(n−t)`, `(R·S)_top` the top `t` rows of `R·S`, `S_bot` the bottom
`n−t` rows of `S`, and UNIFORM constants `(c₀, c₁) = (1/(2+2·t·(m−t)), 2+2·t·(m−t))`.
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators

/-! ## A two-residual-dim key identity (the one new algebraic ingredient) -/

/-- **The N2b key identity (rectangular, two residual dims).** Blocks as raw functions; `Minv` a LEFT
inverse of `M11` (`∑ᵢ Minv t i · M11 i k = δ_{tk}`). With `A := M21·Minv` (row shear) and
`Sc := M22 − A·M12`, the bottom block of `R·S` equals `A·(R·S)_top + Sc·S_bot`. The residual now has
INDEPENDENT row dim `sr` and column/contraction dim `sc` (`M22 : sr × sc`, `M12 : j × sc`,
`M21 : sr × j`, `Sbot : sc → p`). The `sr = sc` square case is the banked `schur_key_identity`. Proof
is verbatim the square one — the column index `b : Fin sc` is never tied to the row index `a : Fin sr`. -/
theorem schur_key_identity_rect {j sr sc p : ℕ}
    (M11 : Fin j → Fin j → ℝ) (M12 : Fin j → Fin sc → ℝ)
    (M21 : Fin sr → Fin j → ℝ) (M22 : Fin sr → Fin sc → ℝ)
    (Minv : Fin j → Fin j → ℝ) (Stop : Fin j → Fin p → ℝ) (Sbot : Fin sc → Fin p → ℝ)
    (hinv : ∀ t k, (∑ i, Minv t i * M11 i k) = if t = k then 1 else 0)
    (a : Fin sr) (col : Fin p) :
    ((∑ i, M21 a i * Stop i col) + ∑ b, M22 a b * Sbot b col)
      = (∑ i : Fin j, (rmatMul M21 Minv) a i * ((∑ k, M11 i k * Stop k col)
            + ∑ b, M12 i b * Sbot b col))
        + rmatMul (fun x y => M22 x y - rmatMul (rmatMul M21 Minv) M12 x y) Sbot a col := by
  have hpiv : ∀ k : Fin j, (∑ i, (rmatMul M21 Minv) a i * M11 i k) = M21 a k := by
    intro k
    simp only [rmatMul]
    calc (∑ i, (∑ t, M21 a t * Minv t i) * M11 i k)
        = ∑ i, ∑ t, (M21 a t * Minv t i * M11 i k) := by
          refine Finset.sum_congr rfl (fun i _ => ?_); rw [Finset.sum_mul]
      _ = ∑ t, M21 a t * (∑ i, Minv t i * M11 i k) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun t _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_); ring
      _ = ∑ t, M21 a t * (if t = k then 1 else 0) := by
          refine Finset.sum_congr rfl (fun t _ => ?_); rw [hinv t k]
      _ = M21 a k := by simp
  have hAM12 : ∀ b : Fin sc,
      rmatMul (rmatMul M21 Minv) M12 a b = ∑ i, (rmatMul M21 Minv) a i * M12 i b := by
    intro b; simp [rmatMul]
  have e1 : ∀ i : Fin j, (rmatMul M21 Minv) a i * ((∑ k, M11 i k * Stop k col)
          + ∑ b, M12 i b * Sbot b col)
      = (∑ k, (rmatMul M21 Minv) a i * M11 i k * Stop k col)
        + ∑ b, (rmatMul M21 Minv) a i * M12 i b * Sbot b col := by
    intro i; rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> (refine Finset.sum_congr rfl (fun _ _ => ?_); ring)
  rw [Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_add_distrib]
  have hM11part : (∑ i : Fin j, ∑ k, (rmatMul M21 Minv) a i * M11 i k * Stop k col)
      = ∑ i, M21 a i * Stop i col := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Finset.sum_mul, hpiv k]
  have hM12part : (∑ i : Fin j, ∑ b, (rmatMul M21 Minv) a i * M12 i b * Sbot b col)
      = ∑ b, (rmatMul (rmatMul M21 Minv) M12) a b * Sbot b col := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [hAM12 b, ← Finset.sum_mul]
  rw [hM11part, hM12part, add_assoc]
  congr 1
  symm
  change (∑ b, (rmatMul (rmatMul M21 Minv) M12) a b * Sbot b col)
      + rmatMul (fun x y => M22 x y - rmatMul (rmatMul M21 Minv) M12 x y) Sbot a col
    = ∑ b, M22 a b * Sbot b col
  simp only [rmatMul]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_); ring

/-! ## The rectangular shear bound (Cramer minor-ratio, `R : Fin m → Fin n`) -/

open Matrix

/-- `M11.updateCol i v = R.submatrix top (update leftCols i rightCol)` for rectangular `R` (rows
`top : Fin j → Fin m`, cols `leftCols : Fin j → Fin n`, outside column `rightCol : Fin n`). The
rectangular sibling of `updateCol_submatrix_eq`. -/
theorem updateCol_submatrix_eq_rect {m n j : ℕ} (R : Matrix (Fin m) (Fin n) ℝ)
    (top : Fin j → Fin m) (leftCols : Fin j → Fin n) (rightCol : Fin n) (i : Fin j) :
    (R.submatrix top leftCols).updateCol i (fun a => R (top a) rightCol)
      = R.submatrix top (Function.update leftCols i rightCol) := by
  ext a c
  rw [Matrix.updateCol_apply]
  by_cases h : c = i
  · subst h; simp [Matrix.submatrix_apply]
  · simp [Matrix.submatrix_apply, h]

/-- **The column-shear minor-ratio bound (rectangular `R`).** On the max-modulus-`j`-minor cell, every
entry of the Gauss column shear `M11⁻¹·M12` has modulus `≤ 1`, where `M11 = R.submatrix top leftCols`
(the `j×j` pivot minor) and `M12 = R.submatrix top rightCols` (`top : Fin j → Fin m` rows,
`leftCols : Fin j → Fin n` / `rightCols : Fin nc → Fin n` cols). The column-swap minors stay `j×j`
minors of `R`, so `hpivot` bounds the numerator. Identical Cramer chain to the square
`colShear_entry_le_one`, with `R : Fin m → Fin n` rectangular (index maps into `Fin m` rows, `Fin n`
cols). -/
theorem colShear_entry_le_one_rect {m n j nc : ℕ} (R : Matrix (Fin m) (Fin n) ℝ)
    (top : Fin j → Fin m) (leftCols : Fin j → Fin n) (rightCols : Fin nc → Fin n)
    (hpivot : ∀ (I : Fin j → Fin m) (J : Fin j → Fin n),
        |(R.submatrix I J).det| ≤ |(R.submatrix top leftCols).det|)
    (hne : (R.submatrix top leftCols).det ≠ 0)
    (i : Fin j) (b : Fin nc) :
    |((R.submatrix top leftCols)⁻¹ * (R.submatrix top rightCols)) i b| ≤ 1 := by
  set M11 := R.submatrix top leftCols with hM11
  have hcol : (fun k => (R.submatrix top rightCols) k b) = (fun a => R (top a) (rightCols b)) := by
    funext a; simp [Matrix.submatrix_apply]
  rw [inv_mul_eq_inv_mulVec_col, hcol, inv_mulVec_eq_cramer_ratio,
    updateCol_submatrix_eq_rect R top leftCols (rightCols b) i]
  rw [abs_mul, abs_inv]
  have hpos : 0 < |M11.det| := abs_pos.2 hne
  rw [inv_mul_eq_div, div_le_one hpos]
  exact hpivot top (Function.update leftCols i (rightCols b))

/-- **The row-shear minor-ratio bound (rectangular `R`).** On the max-modulus-`j`-minor cell, every
entry of the Gauss row shear `M21·M11⁻¹` has modulus `≤ 1`, where `M21 = R.submatrix botRows leftCols`
(`botRows : Fin mr → Fin m` rows, `leftCols : Fin j → Fin n` pivot cols). Transpose dual of
`colShear_entry_le_one_rect` on `Rᵀ : Fin n → Fin m` (row-swap minors of `R` are column-swap minors of
`Rᵀ`, det invariant under transpose). -/
theorem rowShear_entry_le_one_rect {m n j mr : ℕ} (R : Matrix (Fin m) (Fin n) ℝ)
    (top : Fin j → Fin m) (leftCols : Fin j → Fin n) (botRows : Fin mr → Fin m)
    (hpivot : ∀ (I : Fin j → Fin m) (J : Fin j → Fin n),
        |(R.submatrix I J).det| ≤ |(R.submatrix top leftCols).det|)
    (hne : (R.submatrix top leftCols).det ≠ 0)
    (a : Fin mr) (i : Fin j) :
    |((R.submatrix botRows leftCols) * (R.submatrix top leftCols)⁻¹) a i| ≤ 1 := by
  set M11 := R.submatrix top leftCols with hM11
  have htr : ((R.submatrix botRows leftCols) * M11⁻¹) a i
      = (M11ᵀ⁻¹ * (R.submatrix botRows leftCols)ᵀ) i a := by
    rw [← Matrix.transpose_nonsing_inv, ← Matrix.transpose_mul, Matrix.transpose_apply]
  rw [htr]
  -- a minor of `Rᵀ` is `(R.submatrix J I)ᵀ`, det invariant under transpose, so `hpivot` transfers.
  have hpivotT : ∀ (I : Fin j → Fin n) (J : Fin j → Fin m),
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
  exact colShear_entry_le_one_rect Rᵀ leftCols top botRows hpivotT hneT i a

/-! ## The rectangular N2b split (the foundation brick) -/

/-- **N2b — `schur_minorPivot_split_rect` (rectangular `R : Fin m → Fin n`, PROVED).** On the bounded
complete-pivoting cell (`|R| ≤ 1`, the top-left `t×t` minor `M11` is a max-modulus `t×t` minor,
`det M11 ≠ 0`), the disjoint Morse ⊕ Schur-complement TWO-SIDED bounded comparison with UNIFORM
constants. The asymmetric generalisation of `schur_minorPivot_split`: `Δ`-row count `m`, column /
contraction count `n`, residual `Sc : (m−t)×(n−t)` (NOT square `(r−t)×(r−t)`).

    c₀·(frobSq (R·S)_top + frobSq (Sc·S_bot)) ≤ frobSq (R·S) ≤ c₁·(frobSq (R·S)_top + frobSq (Sc·S_bot))

with `(c₀, c₁) = (1/(2+2·t·(m−t)), 2+2·t·(m−t))`, `(R·S)_top` the top `t` rows of `R·S`, `S_bot` the
bottom `n−t` rows of `S`, `Sc = M22 − M21·M11⁻¹·M12 : (m−t)×(n−t)`. NO determinant-identity conjunct
(`R` is rectangular — `det R` is undefined; the square version's det conjunct is unused by the carve
consumer). Core algebra reused verbatim from the dim-generic `schur_abstract_comparison {j s p}`
(`j = t`, `s = m−t`) + `schur_key_identity_rect` + the rectangular shear bound. -/
theorem schur_minorPivot_split_rect {m n p : ℕ} (t : ℕ) (htm : t ≤ m) (htn : t ≤ n) :
    ∃ (c₀ c₁ : ℝ), 0 < c₀ ∧ 0 < c₁ ∧
      ∀ (R : Matrix (Fin m) (Fin n) ℝ) (S : Fin n → Fin p → ℝ),
        (∀ a b, |R a b| ≤ 1) →
        (∀ (I : Fin t → Fin m) (J : Fin t → Fin n),
          |(R.submatrix I J).det| ≤ |(Matrix.of (fun a b : Fin t =>
            R ⟨a, lt_of_lt_of_le a.2 htm⟩ ⟨b, lt_of_lt_of_le b.2 htn⟩)).det|) →
        (Matrix.of (fun a b : Fin t =>
            R ⟨a, lt_of_lt_of_le a.2 htm⟩ ⟨b, lt_of_lt_of_le b.2 htn⟩)).det ≠ 0 →
        ∃ (Sc : Matrix (Fin (m - t)) (Fin (n - t)) ℝ),
          Sc = (Matrix.of (fun (a : Fin (m - t)) (b : Fin (n - t)) =>
                  R ⟨t + a, by omega⟩ ⟨t + b, by omega⟩) : Matrix (Fin (m - t)) (Fin (n - t)) ℝ)
                - (Matrix.of (fun (a : Fin (m - t)) (b : Fin t) =>
                      R ⟨t + a, by omega⟩ ⟨b, lt_of_lt_of_le b.2 htn⟩)
                      : Matrix (Fin (m - t)) (Fin t) ℝ)
                  * (Matrix.of (fun a b : Fin t =>
                      R ⟨a, lt_of_lt_of_le a.2 htm⟩ ⟨b, lt_of_lt_of_le b.2 htn⟩)
                      : Matrix (Fin t) (Fin t) ℝ)⁻¹
                  * (Matrix.of (fun (a : Fin t) (b : Fin (n - t)) =>
                      R ⟨a, lt_of_lt_of_le a.2 htm⟩ ⟨t + b, by omega⟩)
                      : Matrix (Fin t) (Fin (n - t)) ℝ) ∧
          c₀ * (frobSq (fun a : Fin t => rmatMul (fun x y => R x y) S ⟨a, lt_of_lt_of_le a.2 htm⟩)
                  + frobSq (rmatMul (fun a b => Sc a b)
                      (fun a : Fin (n - t) => S ⟨t + a, by omega⟩)))
            ≤ frobSq (rmatMul (fun a b => R a b) S) ∧
          frobSq (rmatMul (fun a b => R a b) S)
            ≤ c₁ * (frobSq (fun a : Fin t => rmatMul (fun x y => R x y) S ⟨a, lt_of_lt_of_le a.2 htm⟩)
                  + frobSq (rmatMul (fun a b => Sc a b)
                      (fun a : Fin (n - t) => S ⟨t + a, by omega⟩))) := by
  refine ⟨1 / (2 + 2 * (t : ℝ) * ((m - t : ℕ) : ℝ)), 2 + 2 * (t : ℝ) * ((m - t : ℕ) : ℝ),
    by positivity, by positivity, ?_⟩
  intro R S hbd hpivot hne
  -- the four blocks (raw-function form) and the inverse pivot block
  set M11f : Fin t → Fin t → ℝ :=
    fun a b => R ⟨a, lt_of_lt_of_le a.2 htm⟩ ⟨b, lt_of_lt_of_le b.2 htn⟩ with hM11f
  set M12f : Fin t → Fin (n - t) → ℝ :=
    fun a b => R ⟨a, lt_of_lt_of_le a.2 htm⟩ ⟨t + b, by omega⟩ with hM12f
  set M21f : Fin (m - t) → Fin t → ℝ :=
    fun a b => R ⟨t + a, by omega⟩ ⟨b, lt_of_lt_of_le b.2 htn⟩ with hM21f
  set M22f : Fin (m - t) → Fin (n - t) → ℝ :=
    fun a b => R ⟨t + a, by omega⟩ ⟨t + b, by omega⟩ with hM22f
  set M11 : Matrix (Fin t) (Fin t) ℝ := Matrix.of M11f with hM11
  set Stop : Fin t → Fin p → ℝ := fun a col => S ⟨a, lt_of_lt_of_le a.2 htn⟩ col with hStop
  set Sbot : Fin (n - t) → Fin p → ℝ := fun a col => S ⟨t + a, by omega⟩ col with hSbot
  set Scf : Fin (m - t) → Fin (n - t) → ℝ :=
    fun x y => M22f x y - rmatMul (rmatMul M21f (M11⁻¹ : Matrix (Fin t) (Fin t) ℝ)) M12f x y with hScf
  set gtop : Fin t → Fin p → ℝ :=
    fun a col => rmatMul (fun x y => R x y) S ⟨a, lt_of_lt_of_le a.2 htm⟩ col with hgtop
  set gbot : Fin (m - t) → Fin p → ℝ :=
    fun a col => rmatMul (fun x y => R x y) S ⟨t + a, by omega⟩ col with hgbot
  set A : Fin (m - t) → Fin t → ℝ := rmatMul M21f (M11⁻¹ : Matrix (Fin t) (Fin t) ℝ) with hA
  set Sch : Fin (m - t) → Fin p → ℝ := rmatMul Scf Sbot with hSch
  -- pivot inverse: Minv·M11 = I (left inverse), as a δ-sum
  have hunit : IsUnit M11.det := isUnit_iff_ne_zero.2 hne
  have hMinv : ∀ tt k, (∑ i, (M11⁻¹ : Matrix (Fin t) (Fin t) ℝ) tt i * M11f i k)
      = if tt = k then 1 else 0 := by
    intro tt k
    have hmul : ((M11⁻¹ : Matrix (Fin t) (Fin t) ℝ) * M11) tt k = if tt = k then 1 else 0 := by
      rw [Matrix.nonsing_inv_mul M11 hunit]; simp [Matrix.one_apply]
    rw [Matrix.mul_apply] at hmul
    rw [← hmul]; rfl
  -- the contraction split: gtop = M11·Stop + M12·Sbot, gbot = M21·Stop + M22·Sbot (over Fin n)
  have hgtop_split : ∀ a col,
      gtop a col = (∑ k, M11f a k * Stop k col) + ∑ b, M12f a b * Sbot b col := by
    intro a col
    rw [hgtop]; simp only [rmatMul]
    rw [fin_sum_block_split t htn (fun x => R ⟨a, lt_of_lt_of_le a.2 htm⟩ x * S x col)]
  have hgbot_split : ∀ a col,
      gbot a col = (∑ k, M21f a k * Stop k col) + ∑ b, M22f a b * Sbot b col := by
    intro a col
    rw [hgbot]; simp only [rmatMul]
    rw [fin_sum_block_split t htn (fun x => R ⟨t + a, by omega⟩ x * S x col)]
  -- the KEY IDENTITY: gbot = A·gtop + Sch  (via the two-residual-dim key identity)
  have hid : ∀ a col, gbot a col = rmatMul A gtop a col + Sch a col := by
    intro a col
    rw [hgbot_split a col]
    rw [show (rmatMul A gtop a col) = ∑ i, A a i * gtop i col from rfl]
    have := schur_key_identity_rect M11f M12f M21f M22f
      (M11⁻¹ : Matrix (Fin t) (Fin t) ℝ) Stop Sbot hMinv a col
    rw [this]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_); rw [hgtop_split i col]
  -- index maps: top : Fin t → Fin m, bot : Fin (m−t) → Fin m, leftCols : Fin t → Fin n
  set topI : Fin t → Fin m := fun a => ⟨a, lt_of_lt_of_le a.2 htm⟩ with htopI
  set leftC : Fin t → Fin n := fun b => ⟨b, lt_of_lt_of_le b.2 htn⟩ with hleftC
  set botI : Fin (m - t) → Fin m := fun a => ⟨t + a, by omega⟩ with hbotI
  have hM11_sub : M11 = R.submatrix topI leftC := by
    rw [hM11]; ext a b; simp [Matrix.submatrix_apply, hM11f, htopI, hleftC]
  have hM21_sub : Matrix.of M21f = R.submatrix botI leftC := by
    ext a b; simp [Matrix.submatrix_apply, hM21f, hleftC, hbotI]
  -- the shear bound |A| ≤ 1  (rectangular rowShear, with top/bot index maps)
  have hAbd : ∀ a i, |A a i| ≤ 1 := by
    intro a i
    have hpiv' : ∀ (I : Fin t → Fin m) (J : Fin t → Fin n),
        |(R.submatrix I J).det| ≤ |(R.submatrix topI leftC).det| := by
      intro I J; rw [← hM11_sub]; exact hpivot I J
    have hne' : (R.submatrix topI leftC).det ≠ 0 := by rw [← hM11_sub]; exact hne
    have hrow := rowShear_entry_le_one_rect R topI leftC botI hpiv' hne' a i
    have hAeq : A a i
        = ((R.submatrix botI leftC) * (R.submatrix topI leftC)⁻¹) a i := by
      rw [hA]
      rw [show ((R.submatrix botI leftC) * (R.submatrix topI leftC)⁻¹) a i
          = ∑ k, (R.submatrix botI leftC) a k * (R.submatrix topI leftC)⁻¹ k i from
        by rw [Matrix.mul_apply]]
      rw [← hM21_sub, ← hM11_sub]
      rfl
    rw [hAeq]; exact hrow
  -- the abstract comparison (provides both bounds with the uniform constants)
  have hcmp := schur_abstract_comparison gtop gbot Sch A hAbd hid
  -- the frobSq row-block split: frobSq(R·S) = frobSq gtop + frobSq gbot
  have hRSsplit : frobSq (rmatMul (fun a b => R a b) S) = frobSq gtop + frobSq gbot := by
    rw [frobSq_fin_block_split t htm (rmatMul (fun a b => R a b) S)]
  -- the Sc·S_bot term matches Sch (Matrix-mult = rmatMul; Sbot' fun = Sbot)
  have hScf_eq : (fun a b => (Matrix.of M22f - Matrix.of M21f * M11⁻¹ * Matrix.of M12f) a b) = Scf := by
    funext x y
    have hprod : (Matrix.of M21f * M11⁻¹ * Matrix.of M12f) x y
        = rmatMul (rmatMul M21f (M11⁻¹ : Matrix (Fin t) (Fin t) ℝ)) M12f x y := by
      rw [Matrix.mul_apply]
      simp only [rmatMul]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [Matrix.mul_apply]; rfl
    rw [hScf]
    change (Matrix.of M22f - Matrix.of M21f * M11⁻¹ * Matrix.of M12f) x y
        = M22f x y - rmatMul (rmatMul M21f (M11⁻¹ : Matrix (Fin t) (Fin t) ℝ)) M12f x y
    rw [Matrix.sub_apply, Matrix.of_apply, hprod]
  have hSch_eq : frobSq (rmatMul (fun a b => (Matrix.of M22f - Matrix.of M21f * M11⁻¹ * Matrix.of M12f) a b)
      (fun a : Fin (n - t) => S ⟨t + a, by omega⟩)) = frobSq Sch := by
    rw [hScf_eq, hSch]
  have hgtop_eq : frobSq (fun a : Fin t => rmatMul (fun x y => R x y) S ⟨a, lt_of_lt_of_le a.2 htm⟩)
      = frobSq gtop := rfl
  refine ⟨Matrix.of M22f - Matrix.of M21f * M11⁻¹ * Matrix.of M12f, rfl, ?_, ?_⟩
  · rw [hRSsplit, hgtop_eq, hSch_eq]; exact hcmp.1
  · rw [hRSsplit, hgtop_eq, hSch_eq]; exact hcmp.2

end DLNFibre.DLN.RLCT
