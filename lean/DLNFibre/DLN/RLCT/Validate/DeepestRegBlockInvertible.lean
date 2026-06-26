import DLNFibre.DLN.RLCT.Validate.DeepestRegAbsorbIFT

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestRegBlockInvertible` — the PIN1 reg-block `≃L` from the frame fact

The PIN1 reg-slice derivative (post the `rThresholdSplit → pivotThresholdSplit J` migration) is the
constant LINEAR map, in residual-block order `(P11−I, P12, P21)`:

    F(X, Y, Z) = ( A₁₁·X + A₁₂·Z + Y·B₂₁ ,   Y·B₂₂ ,   A₂₁·X + A₂₂·Z )

with `A := reindex (Pf first)` (the first-layer frame factor, a unit by `hPf`) and
`B := reindex (pivotThresholdSplit r (H last) J) (Qf last)` (the pivot-aligned last-layer frame factor,
whose ₂₂-block `B₂₂` is a unit by the BANKED frame fact `exists_deepest_lastLayer_pivotFrame`).

This module supplies the BEDROCK consumer brick: `F` is a `ContinuousLinearEquiv`. The map is
block-triangular in the two output groups `{(P11, P21)}` and `{P12}`:
- the `Y`-arm `Y ↦ Y·B₂₂` is invertible iff `IsUnit B₂₂` (right-multiplication by a unit);
- with `Y` recovered, subtract `Y·B₂₁` from `P11`; the `(X, Z)`-pair then solves through `A` (a unit).

The bricks are stated ABSTRACTLY on the block spaces (matrix `≃L`s for the `·A` / `·B₂₂` arms + the
shear), so they are reusable and decoupled from the `regResidualPack` enumeration. The value-fold (the
several-hundred-line strict-derivative assembly identifying the reg-slice derivative WITH this `F`) is
the remaining PIN1 step; this module is the invertibility it lands on.

## Status (l2-pin tide, 2026-06-24)

The COMPLETE assembled reg-block `≃L` is PROVED sorry-free, axiom-clean (`[propext, Classical.choice,
Quot.sound]`, NO sorryAx):
- the arm bricks `mulRightUnitCLE` (`Y↦Y·B₂₂`), `mulLeftUnitCLE` (`U↦A·U`), `stackRowsCLE`
  (`(X,Z)↦[X;Z]` row-stack), `mulBlockPairCLE` (the `·A`-conjugation `(X,Z)↦(A₁₁X+A₁₂Z, A₂₁X+A₂₂Z)`,
  with `mulBlockPairCLE_apply` giving the explicit block products), and `shearCLE`;
- the assembly `regBlockCLE e0 A hA B21 B22 hB22 : (YSp × (XSp × ZSp)) ≃L (YSp × (XSp × ZSp))` realising
  `(Y, (X, Z)) ↦ (Y·B₂₂, (A₁₁X+A₁₂Z + Y·B₂₁, A₂₁X+A₂₂Z))` (block-triangular: `Y` via `·B₂₂`, then the
  `(X,Z)` pair via `A`, the `Y·B₂₁` cross folded into the first block); `regBlockCLE_apply` is `rfl`-level.

The bridge from the `regResidualPack`-packed `Fin nReg → ℝ` reg-block to this canonical `(Y,(X,Z))`
layout (a fixed permutation `≃L`) is the value-fold's job — it produces the derivative `D_E` whose
reg-block matches `regBlockCLE`, which `regStraightenTotalCLM_equiv_of_regBlock_isUnit` then consumes.
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

/-! ## Right-multiplication by a unit matrix is a `≃L` (the `·B₂₂` and `·B₂₁` arms) -/

/-- **Right-multiplication by a unit matrix is a continuous linear equivalence.** `Y ↦ Y * M` on
`Matrix (Fin p) (Fin q) ℝ` (with `M : Matrix (Fin q) (Fin q) ℝ` a unit) is invertible, with inverse
`Y ↦ Y * M⁻¹`. The `Y`-arm `Y ↦ Y·B₂₂` of `F` (the diagonal block carrying the `P12` residual). -/
noncomputable def mulRightUnitCLE {p q : ℕ} (M : Matrix (Fin q) (Fin q) ℝ) (hM : IsUnit M) :
    Matrix (Fin p) (Fin q) ℝ ≃L[ℝ] Matrix (Fin p) (Fin q) ℝ := by
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM
  refine { toFun := fun Y => Y * M
           invFun := fun Y => Y * M⁻¹
           map_add' := fun Y Y' => by simp [Matrix.add_mul]
           map_smul' := fun c Y => by simp [Matrix.smul_mul]
           left_inv := fun Y => by
             simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv M hdet, Matrix.mul_one]
           right_inv := fun Y => by
             simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul M hdet, Matrix.mul_one]
           continuous_toFun := ?_
           continuous_invFun := ?_ }
  · exact continuous_id.matrix_mul continuous_const
  · exact continuous_id.matrix_mul continuous_const

@[simp] theorem mulRightUnitCLE_apply {p q : ℕ} (M : Matrix (Fin q) (Fin q) ℝ) (hM : IsUnit M)
    (Y : Matrix (Fin p) (Fin q) ℝ) : mulRightUnitCLE (p := p) M hM Y = Y * M := rfl

@[simp] theorem mulRightUnitCLE_symm_apply {p q : ℕ} (M : Matrix (Fin q) (Fin q) ℝ) (hM : IsUnit M)
    (Y : Matrix (Fin p) (Fin q) ℝ) : (mulRightUnitCLE (p := p) M hM).symm Y = Y * M⁻¹ := rfl

/-- **Left-multiplication by a unit matrix is a continuous linear equivalence.** `U ↦ M * U` on
`Matrix (Fin p) (Fin q) ℝ` (with `M : Matrix (Fin p) (Fin p) ℝ` a unit) is invertible, with inverse
`U ↦ M⁻¹ * U`. The `(X, Z)`-pair arm `[X;Z] ↦ A·[X;Z]` of `F` (the first-layer frame factor `A`). -/
noncomputable def mulLeftUnitCLE {p q : ℕ} (M : Matrix (Fin p) (Fin p) ℝ) (hM : IsUnit M) :
    Matrix (Fin p) (Fin q) ℝ ≃L[ℝ] Matrix (Fin p) (Fin q) ℝ := by
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM
  refine { toFun := fun U => M * U
           invFun := fun U => M⁻¹ * U
           map_add' := fun U U' => by simp [Matrix.mul_add]
           map_smul' := fun c U => by simp [Matrix.mul_smul]
           left_inv := fun U => by
             simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul M hdet, Matrix.one_mul]
           right_inv := fun U => by
             simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv M hdet, Matrix.one_mul]
           continuous_toFun := ?_
           continuous_invFun := ?_ }
  · exact continuous_const.matrix_mul continuous_id
  · exact continuous_const.matrix_mul continuous_id

@[simp] theorem mulLeftUnitCLE_apply {p q : ℕ} (M : Matrix (Fin p) (Fin p) ℝ) (hM : IsUnit M)
    (U : Matrix (Fin p) (Fin q) ℝ) : mulLeftUnitCLE (q := q) M hM U = M * U := rfl

@[simp] theorem mulLeftUnitCLE_symm_apply {p q : ℕ} (M : Matrix (Fin p) (Fin p) ℝ) (hM : IsUnit M)
    (U : Matrix (Fin p) (Fin q) ℝ) : (mulLeftUnitCLE (q := q) M hM).symm U = M⁻¹ * U := rfl

/-! ## A one-sided affine shear is a `≃L` (subtract a fixed linear function of one coordinate) -/

/-- **The shear `(u, v) ↦ (u + g v, v)` is a `≃L`** for a continuous linear `g : V →L W`. The inverse is
`(w, v) ↦ (w − g v, v)`. The `P11 = … + Y·B₂₁` cross term is sheared away by this move (with
`u := A₁₁X+A₁₂Z`, `v := Y`, `g v := Y·B₂₁`) before the `(X,Z)`-pair is solved through `A`. -/
def shearCLE {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (g : V →L[ℝ] W) :
    (W × V) ≃L[ℝ] (W × V) where
  toFun := fun p => (p.1 + g p.2, p.2)
  invFun := fun p => (p.1 - g p.2, p.2)
  map_add' := fun p p' => by
    simp only [Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk]; abel_nf
  map_smul' := fun c p => by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, RingHom.id_apply, Prod.smul_mk, smul_add]
  left_inv := fun p => by simp
  right_inv := fun p => by simp
  continuous_toFun := (continuous_fst.add (g.continuous.comp continuous_snd)).prodMk continuous_snd
  continuous_invFun := (continuous_fst.sub (g.continuous.comp continuous_snd)).prodMk continuous_snd

@[simp] theorem shearCLE_apply {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (g : V →L[ℝ] W) (p : W × V) :
    shearCLE g p = (p.1 + g p.2, p.2) := rfl

/-! ## Stacking the `(X, Z)`-pair into a full-height matrix (the row-reindex `≃L`)

The `(X, Z)` residual pair (`X : r×r`, `Z : (a−r)×r`) stacks into `[X; Z] : Fin a × Fin r` by the row
split `e : Fin a ≃ Fin r ⊕ Fin (a−r)`. This is a `≃L`: it is `reindex e.symm (Equiv.refl) ∘ fromBlocks`,
linear and continuous each way. The `A`-conjugation arm of `F` acts on this stacked space (`[X;Z] ↦ A·[X;Z]`). -/

/-- **The block-stack `≃L`** `(X, Z) ↦ [X; Z]` on `Matrix (Fin r) (Fin r) ℝ × Matrix (Fin (a−r)) (Fin r) ℝ
≃L Matrix (Fin a) (Fin r) ℝ`, via the row split `e : Fin a ≃ Fin r ⊕ Fin (a−r)`. Stacks the pair to
`reindex e.symm (Equiv.refl) (fromBlocks X 0 Z 0).toBlocks-column-r`; concretely the matrix whose row `i`
is `X`'s row (when `e i = inl`) or `Z`'s row (when `e i = inr`). -/
noncomputable def stackRowsCLE {a r : ℕ} (e : Fin a ≃ Fin r ⊕ Fin (a - r)) :
    (Matrix (Fin r) (Fin r) ℝ × Matrix (Fin (a - r)) (Fin r) ℝ)
      ≃L[ℝ] Matrix (Fin a) (Fin r) ℝ where
  toFun := fun XZ => Matrix.of (fun (i : Fin a) (k : Fin r) =>
    Sum.elim (fun ir => XZ.1 ir k) (fun iz => XZ.2 iz k) (e i))
  invFun := fun U => (Matrix.of (fun (ir : Fin r) (k : Fin r) => U (e.symm (Sum.inl ir)) k),
    Matrix.of (fun (iz : Fin (a - r)) (k : Fin r) => U (e.symm (Sum.inr iz)) k))
  map_add' := fun XZ XZ' => by
    ext i k
    simp only [Matrix.of_apply, Prod.fst_add, Prod.snd_add, Matrix.add_apply]
    rcases e i with ir | iz <;> simp only [Sum.elim_inl, Sum.elim_inr]
  map_smul' := fun c XZ => by
    ext i k
    simp only [Matrix.of_apply, Prod.smul_fst, Prod.smul_snd, Matrix.smul_apply, RingHom.id_apply]
    rcases e i with ir | iz <;> simp only [Sum.elim_inl, Sum.elim_inr]
  left_inv := fun XZ => by
    ext
    · simp only [Matrix.of_apply, Equiv.apply_symm_apply, Sum.elim_inl]
    · simp only [Matrix.of_apply, Equiv.apply_symm_apply, Sum.elim_inr]
  right_inv := fun U => by
    ext i k
    simp only [Matrix.of_apply]
    rcases h : e i with ir | iz
    · show U (e.symm (Sum.inl ir)) k = U i k; rw [← h, Equiv.symm_apply_apply]
    · show U (e.symm (Sum.inr iz)) k = U i k; rw [← h, Equiv.symm_apply_apply]
  continuous_toFun := by
    refine continuous_matrix (fun i k => ?_)
    have : Continuous (fun XZ : Matrix (Fin r) (Fin r) ℝ × Matrix (Fin (a - r)) (Fin r) ℝ =>
        Sum.elim (fun ir => XZ.1 ir k) (fun iz => XZ.2 iz k) (e i)) := by
      rcases h : e i with ir | iz
      · simp only [h, Sum.elim_inl]; exact continuous_fst.matrix_elem ir k
      · simp only [h, Sum.elim_inr]; exact continuous_snd.matrix_elem iz k
    exact this
  continuous_invFun :=
    (continuous_matrix (fun ir k => continuous_id.matrix_elem (e.symm (Sum.inl ir)) k)).prodMk
      (continuous_matrix (fun iz k => continuous_id.matrix_elem (e.symm (Sum.inr iz)) k))

@[simp] theorem stackRowsCLE_apply {a r : ℕ} (e : Fin a ≃ Fin r ⊕ Fin (a - r))
    (XZ : Matrix (Fin r) (Fin r) ℝ × Matrix (Fin (a - r)) (Fin r) ℝ) (i : Fin a) (k : Fin r) :
    stackRowsCLE e XZ i k = Sum.elim (fun ir => XZ.1 ir k) (fun iz => XZ.2 iz k) (e i) := rfl

/-- `reindex e (Equiv.refl) (stackRowsCLE e (X, Z)) = fromBlocks X 0 Z 0`-with-the-right-column-block:
concretely `reindex e (Equiv.refl (Fin r)) [X;Z] = Sum.elim-stacked = (X stacked over Z)` as a
`Fin r ⊕ Fin (a−r)` × `Fin r` matrix whose `inl`-rows are `X` and `inr`-rows are `Z`. -/
theorem reindex_stackRowsCLE {a r : ℕ} (e : Fin a ≃ Fin r ⊕ Fin (a - r))
    (X : Matrix (Fin r) (Fin r) ℝ) (Z : Matrix (Fin (a - r)) (Fin r) ℝ) :
    Matrix.reindex e (Equiv.refl (Fin r)) (stackRowsCLE e (X, Z))
      = Matrix.of (Sum.elim (fun (ir : Fin r) => X ir) (fun (iz : Fin (a - r)) => Z iz)) := by
  ext i k
  rcases i with ir | iz <;>
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply,
      stackRowsCLE_apply, Equiv.apply_symm_apply, Sum.elim_inl, Sum.elim_inr, Matrix.of_apply]

/-! ## The `(X, Z)`-pair left-conjugation by a unit (`[X;Z] ↦ A·[X;Z]`, re-split into blocks)

The `(X, Z)` pair maps via the first-layer frame factor `A : Fin a × Fin a` (a unit) as
`[X; Z] ↦ A · [X; Z]`, re-split into the two block-rows. With `A` read in `Fin r ⊕ Fin (a−r)` blocks
(`Aᵢⱼ := (reindex e e A).toBlocksᵢⱼ`), the result pair is `(A₁₁X + A₁₂Z, A₂₁X + A₂₂Z)`. The `≃L` is
`stackRowsCLE ∘ mulLeftUnitCLE A ∘ stackRowsCLE.symm`. -/

/-- **The `(X, Z)`-pair `·A`-conjugation `≃L`** `(X, Z) ↦ (A₁₁X + A₁₂Z, A₂₁X + A₂₂Z)` for a unit
`A : Matrix (Fin a) (Fin a) ℝ`, with `Aᵢⱼ` read in the `e : Fin a ≃ Fin r ⊕ Fin (a−r)` block split. -/
noncomputable def mulBlockPairCLE {a r : ℕ} (e : Fin a ≃ Fin r ⊕ Fin (a - r))
    (A : Matrix (Fin a) (Fin a) ℝ) (hA : IsUnit A) :
    (Matrix (Fin r) (Fin r) ℝ × Matrix (Fin (a - r)) (Fin r) ℝ)
      ≃L[ℝ] (Matrix (Fin r) (Fin r) ℝ × Matrix (Fin (a - r)) (Fin r) ℝ) :=
  (stackRowsCLE e).trans ((mulLeftUnitCLE A hA).trans (stackRowsCLE e).symm)

/-- **The `·A`-conjugation `≃L` acts by the block products** `(X, Z) ↦ (A₁₁X + A₁₂Z, A₂₁X + A₂₂Z)`,
with `Aᵢⱼ := (reindex e e A).toBlocksᵢⱼ`. The apply identity the value-fold's `[X;Z]`-arm consumes. -/
theorem mulBlockPairCLE_apply {a r : ℕ} (e : Fin a ≃ Fin r ⊕ Fin (a - r))
    (A : Matrix (Fin a) (Fin a) ℝ) (hA : IsUnit A)
    (X : Matrix (Fin r) (Fin r) ℝ) (Z : Matrix (Fin (a - r)) (Fin r) ℝ) :
    mulBlockPairCLE e A hA (X, Z)
      = ((Matrix.reindex e e A).toBlocks₁₁ * X + (Matrix.reindex e e A).toBlocks₁₂ * Z,
         (Matrix.reindex e e A).toBlocks₂₁ * X + (Matrix.reindex e e A).toBlocks₂₂ * Z) := by
  -- `mulBlockPairCLE (X,Z) = stackRowsCLE.symm (A * stackRowsCLE (X,Z))`. Reindex the product on the
  -- shared row interface `e` to read off the block-stacked product, then re-split.
  have hAU : Matrix.reindex e (Equiv.refl (Fin r)) (A * stackRowsCLE e (X, Z))
      = (Matrix.reindex e e A)
        * Matrix.of (Sum.elim (fun (ir : Fin r) => X ir) (fun (iz : Fin (a - r)) => Z iz)) := by
    rw [← reindex_stackRowsCLE e X Z]
    simp only [Matrix.reindex_apply, Equiv.refl_symm, Equiv.symm_symm]
    rw [Matrix.submatrix_mul_equiv A (stackRowsCLE e (X, Z)) e.symm e.symm (Equiv.refl (Fin r))]
  -- The block-stacked product: `(reindex e e A) * [X;Z] = fromBlocks (A₁₁X+A₁₂Z) _ (A₂₁X+A₂₂Z) _`'s
  -- column-`Fin r` block. Read the two row-blocks back through `stackRowsCLE.symm`.
  apply Prod.ext
  · funext ir k
    have := congrArg (fun M => M (Sum.inl ir) k) hAU
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply] at this
    rw [show (mulBlockPairCLE e A hA (X, Z)).1 ir k
        = (A * stackRowsCLE e (X, Z)) (e.symm (Sum.inl ir)) k from rfl, this]
    -- `(reindex e e A) * stacked` at `inl ir`: the block formula via `Matrix.mul_apply` + `Fintype.sum_sum_type`.
    simp only [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.add_apply, Matrix.of_apply,
      Sum.elim_inl, Sum.elim_inr, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Equiv.symm_apply_apply]
  · funext iz k
    have := congrArg (fun M => M (Sum.inr iz) k) hAU
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply] at this
    rw [show (mulBlockPairCLE e A hA (X, Z)).2 iz k
        = (A * stackRowsCLE e (X, Z)) (e.symm (Sum.inr iz)) k from rfl, this]
    simp only [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.add_apply, Matrix.of_apply,
      Sum.elim_inl, Sum.elim_inr, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Equiv.symm_apply_apply]

/-! ## The assembled reg-block `≃L` `F` (the PIN1 consumer object)

`F(X, Y, Z) = (A₁₁X + A₁₂Z + Y·B₂₁, Y·B₂₂, A₂₁X + A₂₂Z)` on the residual-block layout
`XSp × (YSp × ZSp)` (the order `regResidualPack` packs: `P11`-block, then `P12`-block, then `P21`-block).
Block-triangular in the groups `{(X,Z)-via-A}` and `{Y-via-B₂₂}`: it is a `≃L` when `IsUnit A` and
`IsUnit B₂₂`. Inverse: `Y = Q·B₂₂⁻¹`, then `(X,Z) = (mulBlockPairCLE A)⁻¹ (P − Y·B₂₁, R)`. The explicit
forward/inverse is cleaner than a composition (the `Y·B₂₁` cross sits nested in the first component). -/

/-- **The assembled reg-block `≃L`** `F(X,Y,Z) = (A₁₁X+A₁₂Z+Y·B₂₁, Y·B₂₂, A₂₁X+A₂₂Z)` on
`XSp × (YSp × ZSp)`, for a unit row-frame `A : Fin a × Fin a` (in the `e0` split) and a unit
`B₂₂` (the lower-right block of the column-frame, in the pivot split) plus the cross block `B₂₁`.
The invertible reg-slice fderiv the value-fold lands on (block-triangular: `Y` via `·B₂₂`, then `(X,Z)`
via `A`, the `Y·B₂₁` cross folded into the first block). -/
noncomputable def regBlockCLE {a r m : ℕ} (e0 : Fin a ≃ Fin r ⊕ Fin (a - r))
    (A : Matrix (Fin a) (Fin a) ℝ) (hA : IsUnit A)
    (B21 : Matrix (Fin m) (Fin r) ℝ) (B22 : Matrix (Fin m) (Fin m) ℝ) (hB22 : IsUnit B22) :
    (Matrix (Fin r) (Fin m) ℝ × (Matrix (Fin r) (Fin r) ℝ × Matrix (Fin (a - r)) (Fin r) ℝ))
      ≃L[ℝ]
    (Matrix (Fin r) (Fin m) ℝ × (Matrix (Fin r) (Fin r) ℝ × Matrix (Fin (a - r)) (Fin r) ℝ)) := by
  -- Layout: `(Y, (X, Z))` (Y = P12-block first, then the X/Z pair). `mulBlockPairCLE` handles `(X,Z)`;
  -- `mulRightUnitCLE B22` handles Y; the cross `Y·B21` adds to the X-block of the pair.
  classical
  have hB22inv : IsUnit B22.det := (Matrix.isUnit_iff_isUnit_det B22).mp hB22
  refine
    { toFun := fun p =>
        (p.1 * B22,
          ((mulBlockPairCLE e0 A hA p.2).1 + p.1 * B21, (mulBlockPairCLE e0 A hA p.2).2))
      invFun := fun q =>
        let Y := q.1 * B22⁻¹
        (Y, (mulBlockPairCLE e0 A hA).symm (q.2.1 - Y * B21, q.2.2))
      map_add' := fun p p' => by
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · show (p.1 + p'.1) * B22 = p.1 * B22 + p'.1 * B22
          rw [Matrix.add_mul]
        · show (mulBlockPairCLE e0 A hA (p.2 + p'.2)).1 + (p.1 + p'.1) * B21
            = ((mulBlockPairCLE e0 A hA p.2).1 + p.1 * B21)
              + ((mulBlockPairCLE e0 A hA p'.2).1 + p'.1 * B21)
          rw [map_add, Matrix.add_mul, Prod.fst_add]; abel
        · show (mulBlockPairCLE e0 A hA (p.2 + p'.2)).2
            = (mulBlockPairCLE e0 A hA p.2).2 + (mulBlockPairCLE e0 A hA p'.2).2
          rw [map_add, Prod.snd_add]
      map_smul' := fun c p => by
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · show (c • p.1) * B22 = c • (p.1 * B22)
          rw [Matrix.smul_mul]
        · show (mulBlockPairCLE e0 A hA (c • p.2)).1 + (c • p.1) * B21
            = c • ((mulBlockPairCLE e0 A hA p.2).1 + p.1 * B21)
          rw [map_smul, Matrix.smul_mul, Prod.smul_fst, smul_add]
        · show (mulBlockPairCLE e0 A hA (c • p.2)).2 = c • (mulBlockPairCLE e0 A hA p.2).2
          rw [map_smul, Prod.smul_snd]
      left_inv := fun p => by
        have hY : p.1 * B22 * B22⁻¹ = p.1 := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv B22 hB22inv, Matrix.mul_one]
        refine Prod.ext hY (?_)
        show (mulBlockPairCLE e0 A hA).symm
            (((mulBlockPairCLE e0 A hA p.2).1 + p.1 * B21) - (p.1 * B22 * B22⁻¹) * B21,
              (mulBlockPairCLE e0 A hA p.2).2) = p.2
        rw [hY,
          show ((mulBlockPairCLE e0 A hA p.2).1 + p.1 * B21) - p.1 * B21
            = (mulBlockPairCLE e0 A hA p.2).1 from by abel,
          show ((mulBlockPairCLE e0 A hA p.2).1, (mulBlockPairCLE e0 A hA p.2).2)
            = mulBlockPairCLE e0 A hA p.2 from rfl,
          ContinuousLinearEquiv.symm_apply_apply]
      right_inv := fun q => by
        have hY : q.1 * B22⁻¹ * B22 = q.1 := by
          rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul B22 hB22inv, Matrix.mul_one]
        have hround : mulBlockPairCLE e0 A hA ((mulBlockPairCLE e0 A hA).symm
            (q.2.1 - (q.1 * B22⁻¹) * B21, q.2.2)) = (q.2.1 - (q.1 * B22⁻¹) * B21, q.2.2) :=
          ContinuousLinearEquiv.apply_symm_apply _ _
        refine Prod.ext hY (?_)
        show ((mulBlockPairCLE e0 A hA ((mulBlockPairCLE e0 A hA).symm
              (q.2.1 - (q.1 * B22⁻¹) * B21, q.2.2))).1 + (q.1 * B22⁻¹) * B21,
            (mulBlockPairCLE e0 A hA ((mulBlockPairCLE e0 A hA).symm
              (q.2.1 - (q.1 * B22⁻¹) * B21, q.2.2))).2) = q.2
        rw [hround]
        refine Prod.ext ?_ rfl
        show (q.2.1 - q.1 * B22⁻¹ * B21) + q.1 * B22⁻¹ * B21 = q.2.1
        abel
      continuous_toFun := by
        refine (Continuous.matrix_mul continuous_fst continuous_const).prodMk
          ((Continuous.add ?_ (Continuous.matrix_mul continuous_fst continuous_const)).prodMk ?_)
        · exact (continuous_fst.comp ((mulBlockPairCLE e0 A hA).continuous.comp continuous_snd))
        · exact (continuous_snd.comp ((mulBlockPairCLE e0 A hA).continuous.comp continuous_snd))
      continuous_invFun := by
        refine (Continuous.matrix_mul continuous_fst continuous_const).prodMk ?_
        exact (mulBlockPairCLE e0 A hA).symm.continuous.comp
          ((Continuous.sub (continuous_fst.comp continuous_snd)
            ((Continuous.matrix_mul continuous_fst continuous_const).matrix_mul
              continuous_const)).prodMk (continuous_snd.comp continuous_snd)) }

/-- **`regBlockCLE` acts by the block formula** `(Y, (X, Z)) ↦ (Y·B₂₂, ((A·)₁-block + Y·B₂₁, (A·)₂-block))`,
with the `(A·)`-blocks given by `mulBlockPairCLE_apply`. The apply identity the value-fold matches against. -/
@[simp] theorem regBlockCLE_apply {a r m : ℕ} (e0 : Fin a ≃ Fin r ⊕ Fin (a - r))
    (A : Matrix (Fin a) (Fin a) ℝ) (hA : IsUnit A)
    (B21 : Matrix (Fin m) (Fin r) ℝ) (B22 : Matrix (Fin m) (Fin m) ℝ) (hB22 : IsUnit B22)
    (p : Matrix (Fin r) (Fin m) ℝ × (Matrix (Fin r) (Fin r) ℝ × Matrix (Fin (a - r)) (Fin r) ℝ)) :
    regBlockCLE e0 A hA B21 B22 hB22 p
      = (p.1 * B22,
          ((mulBlockPairCLE e0 A hA p.2).1 + p.1 * B21, (mulBlockPairCLE e0 A hA p.2).2)) := rfl

end DLNFibre.DLN.RLCT
