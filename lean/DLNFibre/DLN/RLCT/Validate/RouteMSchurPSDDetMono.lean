import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement

set_option linter.style.longLine false

/-!
# `RouteMSchurPSDDetMono` — Loewner-order determinant monotonicity (non-spectral)

The reusable matrix-algebra lemma the CHARGED corank recursion needs (couplerad §w3-percorank): for real
positive-semidefinite matrices, `0 ⪯ Y ⪯ X ⟹ det Y ≤ det X` (Minkowski's determinant monotonicity), proved
WITHOUT eigenvalues (dodging the documented D-C `IsHermitian.eigenvalues` whnf/isDefEq trap). Route: the
Schur-complement recursion `det X = X₁₁ · det(X/X₁₁)` (`Matrix.det_fromBlocks₁₁`), with the Schur complement
Loewner-monotone via the variational identity `vᵀ(X/X₁₁)v = min_u [u;v]ᵀX[u;v]` (complete the square).

`Matrix.PosSemidef.det_nonneg` is the `Y = 0` instance (`det 0 = 0 ≤ det X`), so the induction proves both
at once — no `PosSemidef.sqrt` / continuous-functional-calculus import needed.

## Status: COMPLETE. `det_le_det_of_posSemidef_sub` (`0 ⪯ Y ⪯ X → det Y ≤ det X`) is sorry-free +
## axiom-clean `[propext, Classical.choice, Quot.sound]` (NATIVE, no eigenvalues). Chain:
## `blockQuadForm_expand` → `blockSchurComplPSD` + variational identity → Schur PSD + Loewner-monotone →
## `posSemidef_pivotRow_zero` + complete-square lower bound → `det_fromBlocks₁₁` pivot step + induction.
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

/-! ## The block quadratic-form expansion (the heart) -/

/-- **Block quadratic-form expansion for a `1 ⊕ k` symmetric matrix.** For a symmetric block matrix `M`
over `Fin 1 ⊕ Fin k`, the quadratic form at `w = (u, v)` expands as the pivot term + the (symmetry-merged)
cross term + the lower block form: `w ⬝ᵥ M *ᵥ w = M₁₁·u² + 2u·(∑ⱼ M(inl 0)(inr j)·vⱼ) + ∑ⱼₗ vⱼ·M(inr j)(inr
l)·vₗ`. The starting point for completing the square (the `d·(u + d⁻¹ r·v)²` form and the Schur complement
follow by `ring` once `d := M₁₁ ≠ 0`). Uses symmetry only to merge the two cross terms. -/
theorem blockQuadForm_expand {k : ℕ} (M : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) ℝ)
    (hsymm : ∀ p q, M p q = M q p) (u : ℝ) (v : Fin k → ℝ) :
    (Sum.elim (fun _ : Fin 1 => u) v) ⬝ᵥ (M *ᵥ (Sum.elim (fun _ : Fin 1 => u) v))
      = M (Sum.inl 0) (Sum.inl 0) * u ^ 2
        + 2 * u * (∑ j, M (Sum.inl 0) (Sum.inr j) * v j)
        + ∑ j, ∑ l, v j * M (Sum.inr j) (Sum.inr l) * v l := by
  classical
  -- Expand the dot product / mulVec over the `Fin 1 ⊕ Fin k` index into the four blocks.
  simp only [dotProduct, mulVec, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Fin.sum_univ_one, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  -- rewrite the lower-cross term via symmetry `M (inr x) (inl 0) = M (inl 0) (inr x)`
  rw [show (∑ x : Fin k, v x * (M (Sum.inr x) (Sum.inl 0) * u))
        = ∑ x : Fin k, u * (M (Sum.inl 0) (Sum.inr x) * v x) from
      Finset.sum_congr rfl (fun x _ => by rw [hsymm (Sum.inr x) (Sum.inl 0)]; ring)]
  have h2 : (∑ i : Fin k, 2 * u * (M (Sum.inl 0) (Sum.inr i) * v i))
      = (∑ x : Fin k, u * (M (Sum.inl 0) (Sum.inr x) * v x))
        + (∑ x : Fin k, u * (M (Sum.inl 0) (Sum.inr x) * v x)) := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun x _ => by ring)
  have hdd : (∑ j : Fin k, ∑ l : Fin k, v j * M (Sum.inr j) (Sum.inr l) * v l)
      = ∑ x : Fin k, ∑ x_1 : Fin k, v x * (M (Sum.inr x) (Sum.inr x_1) * v x_1) :=
    Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun x_1 _ => by ring))
  rw [h2, hdd]; ring

/-! ## The Schur complement and its variational quadratic form -/

/-- **The `1⊕k` Schur complement** `Sc j l := M(inr j)(inr l) − M₁₁⁻¹·M(inr j)(inl 0)·M(inl 0)(inr l)`
(pivot `M₁₁ = M (inl 0)(inl 0)`; Lean's `0⁻¹ = 0` makes it the plain lower block when the pivot is `0`). -/
noncomputable def blockSchurComplPSD {k : ℕ} (M : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun j l => M (Sum.inr j) (Sum.inr l)
    - (M (Sum.inl 0) (Sum.inl 0))⁻¹ * (M (Sum.inr j) (Sum.inl 0) * M (Sum.inl 0) (Sum.inr l))

/-- **The Schur-complement quadratic form, closed form.** `v ⬝ᵥ Sc *ᵥ v = ∑ⱼₗ vⱼ·M(inr j)(inr l)·vₗ −
M₁₁⁻¹·(∑ⱼ M(inl 0)(inr j)·vⱼ)²` (the second sum factors as a square via symmetry). -/
theorem blockSchurComplPSD_quadForm_closed {k : ℕ} (M : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) ℝ)
    (hsymm : ∀ p q, M p q = M q p) (v : Fin k → ℝ) :
    v ⬝ᵥ (blockSchurComplPSD M *ᵥ v)
      = (∑ j, ∑ l, v j * M (Sum.inr j) (Sum.inr l) * v l)
        - (M (Sum.inl 0) (Sum.inl 0))⁻¹ * (∑ j, M (Sum.inl 0) (Sum.inr j) * v j) ^ 2 := by
  classical
  set d := M (Sum.inl 0) (Sum.inl 0) with hd
  -- Step 1: expand `v ⬝ᵥ Sc v` as one double sum with the sub kept inside each summand.
  have hL : v ⬝ᵥ (blockSchurComplPSD M *ᵥ v)
      = ∑ j, ∑ l, (v j * M (Sum.inr j) (Sum.inr l) * v l
          - d⁻¹ * ((v j * M (Sum.inr j) (Sum.inl 0)) * (M (Sum.inl 0) (Sum.inr l) * v l))) := by
    simp only [dotProduct, mulVec, blockSchurComplPSD, Matrix.of_apply, Finset.mul_sum, hd]
    exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => by ring))
  rw [hL]
  simp only [Finset.sum_sub_distrib]
  congr 1
  -- Step 2: the pivot-correction double sum factors as `d⁻¹ · R²` (via symmetry + product-of-sums).
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [hsymm (Sum.inr j) (Sum.inl 0)]; ring

/-- **The variational identity: `v ⬝ᵥ Sc *ᵥ v` is the block QF at the minimiser `u* = −M₁₁⁻¹·(row·v)`.**
So for `M` PSD the Schur form is nonneg (`= w* ⬝ᵥ M *ᵥ w* ≥ 0`), and it is `≤` the block QF at every `u`. -/
theorem blockSchurComplPSD_quadForm_eq_blockQuadForm_min {k : ℕ}
    (M : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) ℝ) (hsymm : ∀ p q, M p q = M q p) (v : Fin k → ℝ) :
    v ⬝ᵥ (blockSchurComplPSD M *ᵥ v)
      = (Sum.elim (fun _ : Fin 1 =>
            -(M (Sum.inl 0) (Sum.inl 0))⁻¹ * (∑ j, M (Sum.inl 0) (Sum.inr j) * v j)) v)
          ⬝ᵥ (M *ᵥ (Sum.elim (fun _ : Fin 1 =>
            -(M (Sum.inl 0) (Sum.inl 0))⁻¹ * (∑ j, M (Sum.inl 0) (Sum.inr j) * v j)) v)) := by
  rw [blockSchurComplPSD_quadForm_closed M hsymm v,
    blockQuadForm_expand M hsymm
      (-(M (Sum.inl 0) (Sum.inl 0))⁻¹ * (∑ j, M (Sum.inl 0) (Sum.inr j) * v j)) v]
  set d := M (Sum.inl 0) (Sum.inl 0) with hd
  set R := ∑ j, M (Sum.inl 0) (Sum.inr j) * v j with hR
  -- both sides equal `(∑∑ vMv) − d⁻¹·R²`; the pivot terms collapse via `d·d⁻² = d⁻¹` (holds even d=0).
  have hdd : d * (d⁻¹ * d⁻¹) = d⁻¹ := by
    rcases eq_or_ne d 0 with h | h
    · simp [h]
    · field_simp
  ring_nf
  rw [hR] at *
  nlinarith [hdd, sq_nonneg R]

/-! ## Schur complement is Hermitian and PSD (when `M` is PSD) -/

/-- The Schur complement of a symmetric matrix is symmetric (Hermitian over ℝ). -/
theorem blockSchurComplPSD_isHermitian {k : ℕ} (M : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) ℝ)
    (hsymm : ∀ p q, M p q = M q p) : (blockSchurComplPSD M).IsHermitian := by
  ext j l
  simp only [Matrix.conjTranspose_apply, blockSchurComplPSD, Matrix.of_apply, star_trivial]
  rw [hsymm (Sum.inr l) (Sum.inr j), hsymm (Sum.inr l) (Sum.inl 0), hsymm (Sum.inl 0) (Sum.inr j)]
  ring

/-- **The Schur complement of a PSD matrix is PSD** (`v ⬝ᵥ Sc *ᵥ v = w* ⬝ᵥ M *ᵥ w* ≥ 0` via the
variational identity). Non-spectral. -/
theorem blockSchurComplPSD_posSemidef {k : ℕ} (M : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) ℝ)
    (hM : M.PosSemidef) : (blockSchurComplPSD M).PosSemidef := by
  have hsymm : ∀ p q, M p q = M q p := fun p q => by
    have := hM.isHermitian.apply q p; simpa using this
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (blockSchurComplPSD_isHermitian M hsymm) (fun v => ?_)
  have hstar : (star v : Fin k → ℝ) = v := funext (fun i => star_trivial (v i))
  rw [hstar, blockSchurComplPSD_quadForm_eq_blockQuadForm_min M hsymm v]
  set w := Sum.elim (fun _ : Fin 1 =>
      -(M (Sum.inl 0) (Sum.inl 0))⁻¹ * (∑ j, M (Sum.inl 0) (Sum.inr j) * v j)) v with hw
  have hsw : (star w : Fin 1 ⊕ Fin k → ℝ) = w := funext (fun i => star_trivial (w i))
  have := hM.dotProduct_mulVec_nonneg w
  rwa [hsw] at this

/-! ## PSD zero-row fact + the complete-square lower bound -/

/-- **PSD with a zero pivot has a zero pivot row.** If `M` is PSD and `M₁₁ = 0`, then every off-pivot
entry `M(inl 0)(inr j) = 0`. (From `0 ≤ QF at (s, eⱼ) = 2s·M(inl0)(inr j) + M(inr j)(inr j)` ∀s, which
forces the linear coefficient to vanish.) Non-spectral (uses `blockQuadForm_expand`). -/
theorem posSemidef_pivotRow_zero {k : ℕ} (M : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) ℝ)
    (hM : M.PosSemidef) (h0 : M (Sum.inl 0) (Sum.inl 0) = 0) (j : Fin k) :
    M (Sum.inl 0) (Sum.inr j) = 0 := by
  have hsymm : ∀ p q, M p q = M q p := fun p q => by
    have := hM.isHermitian.apply q p; simpa using this
  have key : ∀ s : ℝ,
      0 ≤ 2 * s * M (Sum.inl 0) (Sum.inr j) + M (Sum.inr j) (Sum.inr j) := by
    intro s
    have hexp := blockQuadForm_expand M hsymm s (Pi.single j 1)
    have hpos := hM.dotProduct_mulVec_nonneg (Sum.elim (fun _ : Fin 1 => s) (Pi.single j (1 : ℝ)))
    have hstar : (star (Sum.elim (fun _ : Fin 1 => s) (Pi.single j (1 : ℝ)))
        : Fin 1 ⊕ Fin k → ℝ) = Sum.elim (fun _ => s) (Pi.single j 1) :=
      funext (fun i => star_trivial _)
    rw [hstar, hexp, h0] at hpos
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at hpos
    linarith [hpos]
  by_contra hb
  have h1 := key (-(M (Sum.inr j) (Sum.inr j) + 1) / (2 * M (Sum.inl 0) (Sum.inr j)))
  have hcalc : 2 * (-(M (Sum.inr j) (Sum.inr j) + 1) / (2 * M (Sum.inl 0) (Sum.inr j)))
        * M (Sum.inl 0) (Sum.inr j) = -(M (Sum.inr j) (Sum.inr j) + 1) := by
    field_simp
  rw [hcalc] at h1
  linarith

/-- **The complete-square lower bound.** For `M` PSD, the Schur-complement quadratic form is `≤` the block
QF at EVERY `u`: `v ⬝ᵥ Sc *ᵥ v ≤ [u;v]ᵀ M [u;v]` (the Schur value is the minimum over the pivot coord).
`d = M₁₁ ≥ 0`; if `d > 0` the gap is `d·(u+d⁻¹R)² ≥ 0`, if `d = 0` the pivot row vanishes so `R = 0`. -/
theorem blockSchurComplPSD_le_blockQuadForm {k : ℕ} (M : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) ℝ)
    (hM : M.PosSemidef) (u : ℝ) (v : Fin k → ℝ) :
    v ⬝ᵥ (blockSchurComplPSD M *ᵥ v)
      ≤ (Sum.elim (fun _ : Fin 1 => u) v) ⬝ᵥ (M *ᵥ (Sum.elim (fun _ : Fin 1 => u) v)) := by
  have hsymm : ∀ p q, M p q = M q p := fun p q => by
    have := hM.isHermitian.apply q p; simpa using this
  rw [blockSchurComplPSD_quadForm_closed M hsymm v, blockQuadForm_expand M hsymm u v]
  set d := M (Sum.inl 0) (Sum.inl 0) with hd
  set R := ∑ j, M (Sum.inl 0) (Sum.inr j) * v j with hR
  have hdnn : 0 ≤ d := hM.diag_nonneg
  rcases eq_or_lt_of_le hdnn with hd0 | hdpos
  · -- pivot `d = 0` ⟹ pivot row zero ⟹ `R = 0`
    have hR0 : R = 0 := by
      rw [hR]; refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [posSemidef_pivotRow_zero M hM hd0.symm j, zero_mul]
    rw [hR0, ← hd0]; simp
  · -- pivot `d > 0` ⟹ gap `= d·(u + d⁻¹R)² ≥ 0`
    have hne : d ≠ 0 := hdpos.ne'
    have hid : d * (u + d⁻¹ * R) ^ 2 = d * u ^ 2 + 2 * u * R + d⁻¹ * R ^ 2 := by
      field_simp; ring
    have hnn : 0 ≤ d * (u + d⁻¹ * R) ^ 2 := mul_nonneg hdpos.le (sq_nonneg _)
    linarith [hid, hnn]

/-! ## The Schur complement is Loewner-monotone -/

/-- **Schur complement is Loewner-monotone.** If `0 ⪯ Y ⪯ X` (both PSD, `X − Y` PSD) then
`Sc_Y ⪯ Sc_X`. Chain: `v⬝Sc_X⬝v = w*⬝X⬝w* ≥ w*⬝Y⬝w* ≥ v⬝Sc_Y⬝v` — the variational identity for `X`, then
`X ⪰ Y` at the minimiser `w*`, then the complete-square lower bound for `Y`. Non-spectral. -/
theorem blockSchurComplPSD_loewner_mono {k : ℕ} (X Y : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) ℝ)
    (hY : Y.PosSemidef) (hXY : (X - Y).PosSemidef) :
    (blockSchurComplPSD X - blockSchurComplPSD Y).PosSemidef := by
  have hX : X.PosSemidef := by
    have h := hY.add hXY; rwa [show Y + (X - Y) = X from by abel] at h
  have hsymmX : ∀ p q, X p q = X q p := fun p q => by
    have := hX.isHermitian.apply q p; simpa using this
  have hsymmY : ∀ p q, Y p q = Y q p := fun p q => by
    have := hY.isHermitian.apply q p; simpa using this
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((blockSchurComplPSD_isHermitian X hsymmX).sub (blockSchurComplPSD_isHermitian Y hsymmY)) (fun v => ?_)
  have hstar : (star v : Fin k → ℝ) = v := funext (fun i => star_trivial (v i))
  rw [hstar, Matrix.sub_mulVec, dotProduct_sub]
  set wX := Sum.elim (fun _ : Fin 1 =>
      -(X (Sum.inl 0) (Sum.inl 0))⁻¹ * (∑ j, X (Sum.inl 0) (Sum.inr j) * v j)) v with hwX
  -- variational identity for X
  have hSX := blockSchurComplPSD_quadForm_eq_blockQuadForm_min X hsymmX v
  rw [← hwX] at hSX
  -- lower bound for Y at the X-minimiser `wX`
  have hSY := blockSchurComplPSD_le_blockQuadForm Y hY
    (-(X (Sum.inl 0) (Sum.inl 0))⁻¹ * (∑ j, X (Sum.inl 0) (Sum.inr j) * v j)) v
  rw [← hwX] at hSY
  -- `X ⪰ Y` at `wX`: `wX⬝Y⬝wX ≤ wX⬝X⬝wX`
  have hgeq : wX ⬝ᵥ (Y *ᵥ wX) ≤ wX ⬝ᵥ (X *ᵥ wX) := by
    have hsw : (star wX : Fin 1 ⊕ Fin k → ℝ) = wX := funext (fun i => star_trivial (wX i))
    have := hXY.dotProduct_mulVec_nonneg wX
    rw [hsw, Matrix.sub_mulVec, dotProduct_sub] at this
    linarith
  rw [hSX]; linarith [hSY, hgeq]

/-! ## The determinant pivot step and the main monotonicity theorem -/

/-- The `(0,0)` entry of the inverse of an invertible `1×1` matrix is the scalar inverse. -/
private theorem invOf_fin_one_apply (A : Matrix (Fin 1) (Fin 1) ℝ) [Invertible A] :
    (⅟ A) 0 0 = (A 0 0)⁻¹ := by
  rw [invOf_eq_nonsing_inv, inv_def, adjugate_fin_one, det_fin_one]
  simp [Ring.inverse_eq_inv']

/-- The det-`fromBlocks` Schur complement of the `1⊕k` reshape equals `blockSchurComplPSD`. -/
private theorem detBlocks_schur_eq {k : ℕ} (M : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) ℝ)
    [Invertible M.toBlocks₁₁] :
    M.toBlocks₂₂ - M.toBlocks₂₁ * ⅟ M.toBlocks₁₁ * M.toBlocks₁₂ = blockSchurComplPSD M := by
  ext j l
  simp only [Matrix.sub_apply, Matrix.mul_apply, blockSchurComplPSD, Matrix.of_apply,
    Matrix.toBlocks₂₂, Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, Matrix.toBlocks₁₁, Matrix.of_apply,
    Fin.sum_univ_one]
  rw [invOf_fin_one_apply]
  simp only [Matrix.of_apply]
  ring

/-- **Loewner-order determinant monotonicity (non-spectral).** For real matrices, `0 ⪯ Y ⪯ X` (i.e. `Y`
and `X − Y` both PSD) implies `det Y ≤ det X`. Minkowski's inequality via the Schur-complement recursion —
NO eigenvalues. `PosSemidef.det_nonneg` is the `Y = 0` instance. -/
theorem det_le_det_of_posSemidef_sub :
    ∀ {N : ℕ} (X Y : Matrix (Fin N) (Fin N) ℝ), Y.PosSemidef → (X - Y).PosSemidef → Y.det ≤ X.det := by
  intro N
  induction N with
  | zero => intro X Y _ _; simp [Matrix.det_fin_zero]
  | succ n ih =>
    intro X Y hY hXY
    set e : Fin (n + 1) ≃ Fin 1 ⊕ Fin n :=
      (finCongr (Nat.add_comm n 1)).trans finSumFinEquiv.symm with he
    set X' := X.submatrix e.symm e.symm with hX'def
    set Y' := Y.submatrix e.symm e.symm with hY'def
    have hY'psd : Y'.PosSemidef := hY.submatrix _
    have hXY'psd : (X' - Y').PosSemidef := by
      have hsub : X' - Y' = (X - Y).submatrix ⇑e.symm ⇑e.symm := by
        rw [hX'def, hY'def]; ext i j; simp [Matrix.submatrix_apply, Matrix.sub_apply]
      rw [hsub]; exact hXY.submatrix _
    have hX'psd : X'.PosSemidef := by
      have h := hY'psd.add hXY'psd; rwa [show Y' + (X' - Y') = X' from by abel] at h
    rw [show Y.det = Y'.det from (det_submatrix_equiv_self e.symm Y).symm,
      show X.det = X'.det from (det_submatrix_equiv_self e.symm X).symm]
    set dX := X'.toBlocks₁₁.det with hdX
    set dY := Y'.toBlocks₁₁.det with hdY
    have hdX_eq : dX = X' (Sum.inl 0) (Sum.inl 0) := by rw [hdX, det_fin_one]; rfl
    have hdY_eq : dY = Y' (Sum.inl 0) (Sum.inl 0) := by rw [hdY, det_fin_one]; rfl
    have hdX0 : 0 ≤ dX := hdX_eq ▸ hX'psd.diag_nonneg
    have hdY0 : 0 ≤ dY := hdY_eq ▸ hY'psd.diag_nonneg
    have hdYX : dY ≤ dX := by
      have : 0 ≤ (X' - Y') (Sum.inl 0) (Sum.inl 0) := hXY'psd.diag_nonneg
      rw [Matrix.sub_apply] at this; rw [hdX_eq, hdY_eq]; linarith
    rcases eq_or_lt_of_le hdX0 with hdX_zero | hdX_pos
    · -- pivot `dX = 0`: both matrices have a zero pivot row ⟹ both dets `0`.
      have hXrow : ∀ j, X' (Sum.inl 0) j = 0 := by
        rintro (i | j)
        · rw [Subsingleton.elim i 0, ← hdX_eq]; exact hdX_zero.symm
        · exact posSemidef_pivotRow_zero X' hX'psd (hdX_eq ▸ hdX_zero.symm) j
      have hYrow : ∀ j, Y' (Sum.inl 0) j = 0 := by
        have hdY_zero : dY = 0 := le_antisymm (hdX_zero ▸ hdYX) hdY0
        rintro (i | j)
        · rw [Subsingleton.elim i 0, ← hdY_eq]; exact hdY_zero
        · exact posSemidef_pivotRow_zero Y' hY'psd (hdY_eq ▸ hdY_zero) j
      rw [Matrix.det_eq_zero_of_row_eq_zero (Sum.inl 0) hXrow,
        Matrix.det_eq_zero_of_row_eq_zero (Sum.inl 0) hYrow]
    · -- pivot `dX > 0`: Schur recursion + IH.
      have hdX_ne : dX ≠ 0 := hdX_pos.ne'
      letI : Invertible X'.toBlocks₁₁ := X'.toBlocks₁₁.invertibleOfIsUnitDet (isUnit_iff_ne_zero.2 hdX_ne)
      have hXdet : X'.det = dX * (blockSchurComplPSD X').det := by
        conv_lhs => rw [← Matrix.fromBlocks_toBlocks X']
        rw [Matrix.det_fromBlocks₁₁, detBlocks_schur_eq X']
      -- `dY` may be `0` (then `det Y' = 0`); else the same recursion.
      have hScX_psd : (blockSchurComplPSD X').PosSemidef := blockSchurComplPSD_posSemidef X' hX'psd
      have hScY_psd : (blockSchurComplPSD Y').PosSemidef := blockSchurComplPSD_posSemidef Y' hY'psd
      have hScmono : (blockSchurComplPSD X' - blockSchurComplPSD Y').PosSemidef :=
        blockSchurComplPSD_loewner_mono X' Y' hY'psd hXY'psd
      have hdet0 : (0 : ℝ) ≤ (0 : Matrix (Fin n) (Fin n) ℝ).det := by
        rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn; simp [Matrix.det_fin_zero]
        · exact le_of_eq (Matrix.det_eq_zero_of_row_eq_zero (⟨0, hn⟩ : Fin n) (fun _ => rfl)).symm
      have hScdetY0 : 0 ≤ (blockSchurComplPSD Y').det := by
        have h := ih (blockSchurComplPSD Y') 0 (by simpa using Matrix.PosSemidef.zero)
          (by simpa using hScY_psd)
        linarith
      have hScmono_det : (blockSchurComplPSD Y').det ≤ (blockSchurComplPSD X').det :=
        ih _ _ hScY_psd hScmono
      rcases eq_or_lt_of_le hdY0 with hdY_zero | hdY_pos
      · -- `dY = 0` ⟹ `det Y' = 0 ≤ det X'`.
        have hYrow : ∀ j, Y' (Sum.inl 0) j = 0 := by
          rintro (i | j)
          · rw [Subsingleton.elim i 0, ← hdY_eq]; exact hdY_zero.symm
          · exact posSemidef_pivotRow_zero Y' hY'psd (hdY_eq ▸ hdY_zero.symm) j
        rw [Matrix.det_eq_zero_of_row_eq_zero (Sum.inl 0) hYrow, hXdet]
        exact mul_nonneg hdX0 (le_trans hScdetY0 hScmono_det)
      · have hdY_ne : dY ≠ 0 := hdY_pos.ne'
        letI : Invertible Y'.toBlocks₁₁ :=
          Y'.toBlocks₁₁.invertibleOfIsUnitDet (isUnit_iff_ne_zero.2 hdY_ne)
        have hYdet : Y'.det = dY * (blockSchurComplPSD Y').det := by
          conv_lhs => rw [← Matrix.fromBlocks_toBlocks Y']
          rw [Matrix.det_fromBlocks₁₁, detBlocks_schur_eq Y']
        rw [hXdet, hYdet]
        calc dY * (blockSchurComplPSD Y').det
            ≤ dX * (blockSchurComplPSD Y').det := by
              apply mul_le_mul_of_nonneg_right hdYX hScdetY0
          _ ≤ dX * (blockSchurComplPSD X').det := by
              apply mul_le_mul_of_nonneg_left hScmono_det hdX0

/-- **A real PSD matrix has nonnegative determinant** (the `Y = 0` corollary of the monotonicity;
Mathlib v4.29 lacks a direct `PosSemidef.det_nonneg`). -/
theorem posSemidef_det_nonneg {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ} (hM : M.PosSemidef) :
    0 ≤ M.det := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp [Matrix.det_fin_zero]
  · have h := det_le_det_of_posSemidef_sub M 0 (by simpa using Matrix.PosSemidef.zero)
      (by simpa using hM)
    rwa [Matrix.det_eq_zero_of_row_eq_zero (⟨0, hN⟩ : Fin N) (fun _ => rfl)] at h

end DLNFibre.DLN.RLCT
