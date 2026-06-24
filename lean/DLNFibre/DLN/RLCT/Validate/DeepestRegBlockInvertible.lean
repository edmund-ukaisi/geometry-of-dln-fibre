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

The brick is stated ABSTRACTLY on the block spaces (matrix `≃L`s for the `·A` / `·B₂₂` arms + the
shear), so it is reusable and decoupled from the `regResidualPack` enumeration. The value-fold (the
several-hundred-line strict-derivative assembly identifying the reg-slice derivative WITH this `F`) is
the remaining PIN1 step; this module is the invertibility it lands on.

## Status

The block-triangular `≃L` of the canonical residual layout: PROVED sorry-free. The bridge from the
`regResidualPack`-packed `Fin nReg → ℝ` reg-block to this canonical layout is the value-fold's job
(it produces the derivative in the `(P11−I, P12, P21)` block order this `≃L` lives on).
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

end DLNFibre.DLN.RLCT
