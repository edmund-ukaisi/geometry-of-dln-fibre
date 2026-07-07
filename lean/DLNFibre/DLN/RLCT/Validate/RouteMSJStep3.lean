import DLNFibre.DLN.RLCT.Validate.RouteMSJChartAlgebra

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJStep3` — the STEP-3 unit block-elimination (general widths)

The **Z-independent unit block-elimination** of Aoyagi's `(S,J)` resolution
(`expeditions/2026-06-20-aoyagi-full/threads/genm-sjjoint-design/chart-lemma-probe.md`, step 3), at
**general (opaque `Fintype`) widths** — the general-width lift of the `(2,2,2)` templates
(`Case222Resolution.blockForm`/`blockForm_step3`). It is the FORWARD factorisation of an arbitrary
block matrix with invertible pivot into three unit factors — the inverse of the banked
block-diagonalising conjugation `schur_cov` (`RouteMSJPivotChart`):

    fromBlocks A B C D  =  invSchurLeft A C · (fromBlocks A 0 0 Γ) · invSchurRight A B,
    invSchurLeft A C := [[1, 0], [C·A⁻¹, 1]],   invSchurRight A B := [[1, A⁻¹·B], [0, 1]],
    Γ := schurCompl A B C D = D − C·A⁻¹·B.

Both unit factors are **det 1** (`det_invSchurLeft`/`det_invSchurRight`) and depend ONLY on the
block `(A, B, C)`, NOT on any downstream product `Z` — the "Z-independent" property the
sequential-resolution invariant requires. On the loss of an upstream–block–downstream product
`P · (fromBlocks A B C D) · Z` the two unit factors are ABSORBED into the adjacent factors
(`frobSq_step3_absorb`):

    frobSq (P · (fromBlocks A B C D) · Z)
      = frobSq ((P · invSchurLeft A C) · (fromBlocks A 0 0 Γ) · (invSchurRight A B · Z)),

exact because the matrices inside `frobSq` are equal (no Frobenius-invariance of the non-orthogonal
unit factors is used — the left factor rides into the upstream `P`, the right into the downstream
`Z`). The block-diagonal core then row-splits cleanly (`frobSq_blockDiag_split`):

    frobSq ((fromBlocks A 0 0 Γ) · W) = frobSq (A · W_top) + frobSq (Γ · W_bot).

## FIDELITY — what STEP-3 does and does NOT do (route finding, decorrelated Codex xhigh)

STEP-3 is a corank-DECREMENTING block-diagonalisation with unit absorption; it is **NOT** an
isotropisation. The corank block `Γ` still enters the residual `frobSq (Γ · W_bot)` coupled to the
downstream `W_bot` — it does NOT become the isotropic `frobSq Γ` unless `W_bot` already carries a
literal identity channel. The exact isotropic peel shape `frobSq Δ + W` (the input of the pure peels
`matBox_corank_dominates_absZ_lt_top` / `matBox_corank_residual_absZ_le`, `RouteMSJCorankPure`) is
reachable ONLY through a literal identity channel in the downstream (`frobSq_identityChannel`):

    frobSq (A₀ · fromBlocks 1 0 0 Z) = frobSq (A₀_left) + frobSq (A₀_right · Z),

i.e. when the pivot columns of `A₀` meet an identity block of the downstream, the left `t`-column
block `A₀_left` enters ISOTROPICALLY (`frobSq A₀_left`) and everything else folds into the additive
core `frobSq (A₀_right · Z)`. This is the honest bridge to the pure peels. On the general degenerate
strata, where the downstream has NO identity channel, the recursion instead terminates on the
`monomial × (unit ≥ 1)` endpoint (the `(2,2,2)` mechanism `blockForm_step3` + `step3_unit_ge_one` +
`integrableOn_monomial_mul_unit_iff`), NOT on a final pure `frobSq Δ + W` peel. (The banked
`frobSq_schur_block_split` = `corankStep`'s residual is the leading-factor STEP-3 with no upstream
`P`; its residual `frobSq (C·Q̃_p + Γ·Q_b)` is cross-coupled, confirming STEP-3 does not isotropise
it.)

S2-FREE: pure matrix algebra (`fromBlocks`, `schur_cov`, `frobSq` row/column split); axiom-clean
`[propext, Classical.choice, Quot.sound]`. No `monomial_rlct`, no measure theory.
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped BigOperators

/-! ## The Frobenius column-block split (companion of `frobSq_row_split`) -/

/-- **The Frobenius column-block split.** For a matrix with a sum-type COLUMN index `t ⊕ b`, the
squared Frobenius norm splits over the two column blocks:
`frobSq M = frobSq (left cols) + frobSq (right cols)`, the left/right columns being the
`Sum.inl` / `Sum.inr` column submatrices. `Fintype.sum_sum_type` on the INNER (column) sum of
`frobSq`, distributed over the outer row sum. -/
theorem frobSq_col_split {r t b : Type*} [Fintype r] [Fintype t] [Fintype b]
    (M : Matrix r (t ⊕ b) ℝ) :
    frobSq M = frobSq (M.submatrix id Sum.inl) + frobSq (M.submatrix id Sum.inr) := by
  unfold frobSq
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Fintype.sum_sum_type]
  rfl

section Step3

variable {t a b m n : Type*} [Fintype t] [Fintype a] [Fintype b] [Fintype m] [Fintype n]
  [DecidableEq t] [DecidableEq a] [DecidableEq b]

/-- **The unit lower-triangular left factor** `[[1, 0], [C·A⁻¹, 1]]` — the INVERSE of the Schur left
factor `schurLeft` (`RouteMSJPivotChart`). Depends only on the block `(A, C)`, not on any
downstream. -/
noncomputable def invSchurLeft (A : Matrix t t ℝ) (C : Matrix a t ℝ) [Invertible A] :
    Matrix (t ⊕ a) (t ⊕ a) ℝ :=
  fromBlocks 1 0 (C * ⅟A) 1

/-- **The unit upper-triangular right factor** `[[1, A⁻¹·B], [0, 1]]` — the INVERSE of `schurRight`.
Depends only on the block `(A, B)`, not on any downstream. -/
noncomputable def invSchurRight (A : Matrix t t ℝ) (B : Matrix t b ℝ) [Invertible A] :
    Matrix (t ⊕ b) (t ⊕ b) ℝ :=
  fromBlocks 1 (⅟A * B) 0 1

/-- **`det = 1` (left factor).** `invSchurLeft` is unit lower-triangular. -/
theorem det_invSchurLeft (A : Matrix t t ℝ) (C : Matrix a t ℝ) [Invertible A] :
    (invSchurLeft A C).det = 1 := by
  unfold invSchurLeft
  rw [det_fromBlocks_zero₁₂, det_one, det_one, mul_one]

/-- **`det = 1` (right factor).** `invSchurRight` is unit upper-triangular. -/
theorem det_invSchurRight (A : Matrix t t ℝ) (B : Matrix t b ℝ) [Invertible A] :
    (invSchurRight A B).det = 1 := by
  unfold invSchurRight
  rw [det_fromBlocks_zero₂₁, det_one, det_one, mul_one]

/-- **The STEP-3 forward block factorisation (EXACT, general widths).** An arbitrary block matrix
with invertible pivot `A` factors into the two det-1 unit factors and the block-diagonal core:

    fromBlocks A B C D = invSchurLeft A C · (fromBlocks A 0 0 Γ) · invSchurRight A B

The forward direction of the banked `schur_cov` (which conjugates `A₀` TO block-diagonal); this is
the factorisation OF `A₀` the loss recursion consumes. `invSchurLeft`/`invSchurRight` are the
inverses of the banked Schur factors `schurLeft`/`schurRight` (`hL`/`hR`: their products are `1`),
so `schur_cov` recombines to `A₀`. -/
theorem step3_blockFactor (A : Matrix t t ℝ) (B : Matrix t b ℝ) (C : Matrix a t ℝ)
    (D : Matrix a b ℝ) [Invertible A] :
    fromBlocks A B C D
      = invSchurLeft A C * fromBlocks A 0 0 (schurCompl A B C D) * invSchurRight A B := by
  have hL : invSchurLeft A C * schurLeft A C = 1 := by
    rw [invSchurLeft, schurLeft, fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero,
      zero_add, add_neg_cancel]
    exact fromBlocks_one
  have hR : schurRight A B * invSchurRight A B = 1 := by
    rw [invSchurRight, schurRight, fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero,
      zero_add, add_neg_cancel]
    exact fromBlocks_one
  rw [← schur_cov A B C D]
  simp only [Matrix.mul_assoc]
  rw [hR, Matrix.mul_one, ← Matrix.mul_assoc, hL, Matrix.one_mul]

/-- **The STEP-3 loss absorption (EXACT, general widths).** For an upstream factor `P`, the block,
and a downstream factor `Z`, the two unit factors of `step3_blockFactor` are ABSORBED into the
adjacent factors without changing the loss:

    frobSq (P · (fromBlocks A B C D) · Z)
      = frobSq ((P · invSchurLeft A C) · (fromBlocks A 0 0 Γ) · (invSchurRight A B · Z)).

Exact because the matrices inside `frobSq` are equal (`step3_blockFactor` + associativity) — the
left unit rides into the upstream `P`, the right into the downstream `Z`; NO Frobenius-invariance of
the non-orthogonal unit factors is used. The pointwise algebraic content of the
sequential-resolution invariant: the unit factors never touch the deeper factors. -/
theorem frobSq_step3_absorb (P : Matrix m (t ⊕ a) ℝ) (A : Matrix t t ℝ) (B : Matrix t b ℝ)
    (C : Matrix a t ℝ) (D : Matrix a b ℝ) [Invertible A] (Z : Matrix (t ⊕ b) n ℝ) :
    frobSq (P * fromBlocks A B C D * Z)
      = frobSq (P * invSchurLeft A C * fromBlocks A 0 0 (schurCompl A B C D)
          * (invSchurRight A B * Z)) := by
  rw [step3_blockFactor A B C D]
  congr 1
  simp only [Matrix.mul_assoc]

/-- **The block-diagonal core row-split (EXACT).** The loss of the block-diagonal core against a
downstream `W` splits over the two row blocks into the pivot energy `frobSq (A · W_top)` and the
corank residual `frobSq (Γ · W_bot)` (`W_top, W_bot` the pivot / non-pivot row blocks of `W`):

    frobSq ((fromBlocks A 0 0 Γ) · W) = frobSq (A · W_top) + frobSq (Γ · W_bot).

`frobSq_row_split` + `fromBlocks_mul_topRows`/`_botRows` (with the off-diagonal blocks `0`). The
corank block `Γ` still enters COUPLED to `W_bot` (`Γ · W_bot`) — isolated to its own row block, but
NOT isotropised (that needs an identity channel; `frobSq_identityChannel`). -/
theorem frobSq_blockDiag_split (A : Matrix t t ℝ) (Γ : Matrix a b ℝ) (W : Matrix (t ⊕ b) n ℝ) :
    frobSq (fromBlocks A 0 0 Γ * W)
      = frobSq (A * W.submatrix Sum.inl id) + frobSq (Γ * W.submatrix Sum.inr id) := by
  rw [frobSq_row_split (fromBlocks A 0 0 Γ * W), fromBlocks_mul_topRows, fromBlocks_mul_botRows]
  simp only [Matrix.zero_mul, add_zero, zero_add]

end Step3

/-! ## The identity-channel isotropisation — the honest bridge to the pure peels -/

/-- **The identity-channel isotropisation (EXACT).** When the pivot columns of the front factor
`A₀` meet a literal IDENTITY block of the downstream (`Q = fromBlocks 1 0 0 Z`), the left `t`-column
block of `A₀` enters ISOTROPICALLY and the rest folds into the additive core:

    frobSq (A₀ · fromBlocks 1 0 0 Z) = frobSq (A₀_left) + frobSq (A₀_right · Z),

`A₀_left = A₀.submatrix id Sum.inl` (pivot columns), `A₀_right = A₀.submatrix id Sum.inr`. This is
the ONLY shape that feeds the pure peels `matBox_corank_dominates_absZ_lt_top` / `_residual_absZ_le`
(`RouteMSJCorankPure`) — the freed block `A₀_left` enters through its own `frobSq`, with the deeper
loss `frobSq (A₀_right · Z)` as the non-negative additive core `W`. `frobSq_col_split` + the
column-block computation of the product against the identity channel. -/
theorem frobSq_identityChannel {r t c n : Type*} [Fintype r] [Fintype t] [Fintype c] [Fintype n]
    [DecidableEq t] (A₀ : Matrix r (t ⊕ c) ℝ) (Z : Matrix c n ℝ) :
    frobSq (A₀ * fromBlocks (1 : Matrix t t ℝ) 0 0 Z)
      = frobSq (A₀.submatrix id Sum.inl) + frobSq (A₀.submatrix id Sum.inr * Z) := by
  have hinl : (A₀ * fromBlocks (1 : Matrix t t ℝ) 0 0 Z).submatrix id Sum.inl
      = A₀.submatrix id Sum.inl := by
    ext i j
    simp only [Matrix.submatrix_apply, id_eq, Matrix.mul_apply]
    rw [Fintype.sum_sum_type]
    simp only [fromBlocks_apply₁₁, fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero,
      Finset.sum_const_zero, add_zero, Matrix.one_apply, mul_ite, mul_one,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hinr : (A₀ * fromBlocks (1 : Matrix t t ℝ) 0 0 Z).submatrix id Sum.inr
      = A₀.submatrix id Sum.inr * Z := by
    ext i j
    simp only [Matrix.submatrix_apply, id_eq, Matrix.mul_apply]
    rw [Fintype.sum_sum_type]
    simp only [fromBlocks_apply₁₂, fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero,
      Finset.sum_const_zero, zero_add]
  rw [frobSq_col_split (A₀ * fromBlocks (1 : Matrix t t ℝ) 0 0 Z), hinl, hinr]

/-! ## Non-vacuity witness -/

/-- **Non-vacuity of `step3_blockFactor`.** The factorisation is inhabited at the smallest genuine
width (`t = a = b = Fin 1`, pivot `A = 1`): the block-diagonal core is exactly the corank scalar
`Γ = D − C·B`, and the two unit factors reduce to the scalar shears. Witnesses that the
general-width STEP-3 is not vacuous. -/
example (B C D : Matrix (Fin 1) (Fin 1) ℝ) [Invertible (1 : Matrix (Fin 1) (Fin 1) ℝ)] :
    (fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) B C D)
      = invSchurLeft (1 : Matrix (Fin 1) (Fin 1) ℝ) C
          * fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0
              (schurCompl (1 : Matrix (Fin 1) (Fin 1) ℝ) B C D)
          * invSchurRight (1 : Matrix (Fin 1) (Fin 1) ℝ) B :=
  step3_blockFactor 1 B C D

end DLNFibre.DLN.RLCT
