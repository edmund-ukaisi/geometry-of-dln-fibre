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

/-- Separate row and column endpoint equivalences give the full residual
coordinate equivalence to the Case 2 pivot-entry center.

This only packages product-index reindexing.  The row and column equivalences
remain explicit hypotheses. -/
def case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
    {μ ν : Type*} (n : ℕ → ℕ) (S J : ℕ)
    (rowEquiv : μ ≃ Case2ResidualRowIndex n S J)
    (colEquiv : ν ≃ Case2ResidualColIndex n S J) :
    AoyagiResidualBlockCoordinateIndex μ ν ≃
      (case2ResidualBlockPivotEntries n S J : Type) :=
  (Equiv.prodCongr rowEquiv colEquiv).trans
    (case2ResidualBlockCoordinateIndexEquivPivotEntries n S J)

@[simp]
theorem case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs_apply
    {μ ν : Type*} (n : ℕ → ℕ) (S J : ℕ)
    (rowEquiv : μ ≃ Case2ResidualRowIndex n S J)
    (colEquiv : ν ≃ Case2ResidualColIndex n S J)
    (c : AoyagiResidualBlockCoordinateIndex μ ν) :
    (case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
        n S J rowEquiv colEquiv c).1 =
      ((rowEquiv c.1).1, (colEquiv c.2).1) :=
  rfl

/-- Version of `case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs`
with endpoint equivalences oriented out of the Case 2 residual row and column
types. -/
def case2ResidualBlockCoordinateIndexEquivPivotEntriesOfCase2EndpointEquivs
    {μ ν : Type*} (n : ℕ → ℕ) (S J : ℕ)
    (rowEquiv : Case2ResidualRowIndex n S J ≃ μ)
    (colEquiv : Case2ResidualColIndex n S J ≃ ν) :
    AoyagiResidualBlockCoordinateIndex μ ν ≃
      (case2ResidualBlockPivotEntries n S J : Type) :=
  case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
    n S J rowEquiv.symm colEquiv.symm

@[simp]
theorem case2ResidualBlockCoordinateIndexEquivPivotEntriesOfCase2EndpointEquivs_apply
    {μ ν : Type*} (n : ℕ → ℕ) (S J : ℕ)
    (rowEquiv : Case2ResidualRowIndex n S J ≃ μ)
    (colEquiv : Case2ResidualColIndex n S J ≃ ν)
    (c : AoyagiResidualBlockCoordinateIndex μ ν) :
    (case2ResidualBlockCoordinateIndexEquivPivotEntriesOfCase2EndpointEquivs
        n S J rowEquiv colEquiv c).1 =
      ((rowEquiv.symm c.1).1, (colEquiv.symm c.2).1) :=
  rfl

end Aoyagi
end DLN
end DLNFibre
