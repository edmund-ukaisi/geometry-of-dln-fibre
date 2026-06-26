import DLNFibre.DLN.Aoyagi.BlowupArithmetic
import DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates

/-!
# Case 2 residual-coordinate index bookkeeping

This file relates Aoyagi's p. 13 residual scalar-coordinate index for a
rectangular residual block to the finite Case 2 pivot-entry set.
-/

noncomputable section

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- The scalar residual-coordinate index for the Case 2 residual block is the
finite set of candidate pivot entries in that block.

This is finite index bookkeeping only: it does not construct a selected-entry
chart, a source image, compatible residual factors, or analytic data. -/
def case2ResidualBlockCoordinateIndexEquivPivotEntries
    (n : ℕ → ℕ) (S J : ℕ) :
    AoyagiResidualBlockCoordinateIndex
        (Case2ResidualRowIndex n S J) (Case2ResidualColIndex n S J) ≃
      (case2ResidualBlockPivotEntries n S J : Type) where
  toFun c :=
    ⟨(c.1.1, c.2.1), by
      rw [mem_case2ResidualBlockPivotEntries_iff]
      exact ⟨
        ((mem_case2ResidualBlockRows n S J c.1.1).mp c.1.2).1,
        ((mem_case2ResidualBlockRows n S J c.1.1).mp c.1.2).2,
        ((mem_case2ResidualBlockCols n S J c.2.1).mp c.2.2).1,
        ((mem_case2ResidualBlockCols n S J c.2.1).mp c.2.2).2⟩⟩
  invFun p :=
    (case2ResidualBlockPivotRowOfMem p.2,
      case2ResidualBlockPivotColOfMem p.2)
  left_inv c := by
    rcases c with ⟨i, j⟩
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl
  right_inv p := by
    apply Subtype.ext
    exact case2ResidualBlockPivotOfMem_pair p.2

@[simp]
theorem case2ResidualBlockCoordinateIndexEquivPivotEntries_apply
    (n : ℕ → ℕ) (S J : ℕ)
    (c :
      AoyagiResidualBlockCoordinateIndex
        (Case2ResidualRowIndex n S J) (Case2ResidualColIndex n S J)) :
    (case2ResidualBlockCoordinateIndexEquivPivotEntries n S J c).1 =
      (c.1.1, c.2.1) :=
  rfl

@[simp]
theorem case2ResidualBlockCoordinateIndexEquivPivotEntries_symm_apply_fst
    (n : ℕ → ℕ) (S J : ℕ)
    (p : (case2ResidualBlockPivotEntries n S J : Type)) :
    ((case2ResidualBlockCoordinateIndexEquivPivotEntries n S J).symm p).1.1 =
      p.1.1 :=
  rfl

@[simp]
theorem case2ResidualBlockCoordinateIndexEquivPivotEntries_symm_apply_snd
    (n : ℕ → ℕ) (S J : ℕ)
    (p : (case2ResidualBlockPivotEntries n S J : Type)) :
    ((case2ResidualBlockCoordinateIndexEquivPivotEntries n S J).symm p).2.1 =
      p.1.2 :=
  rfl

end Aoyagi
end DLN
end DLNFibre

