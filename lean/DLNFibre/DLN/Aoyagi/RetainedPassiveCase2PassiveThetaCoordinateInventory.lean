import DLNFibre.DLN.Aoyagi.Case2ResidualIndex
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSector

/-!
# Case 2 passive-theta coordinate inventory

This file records the finite coordinate-count boundary for the Case 2
passive-theta source.  The selected-entry center fills the tail retained
`C` factor, while the head retained `C` factor is a separate coordinate block.
It proves no source-image coverage, measure transport, Jacobian formula,
normal-crossing statement, pole order, or RLCT extraction.
-/

noncomputable section

namespace DLNFibre
namespace DLN
namespace Aoyagi

namespace Case2PassiveTheta

/-- Scalar coordinates for the head active `C` factor in the two-edge
retained-passive p.13 tuple. -/
abbrev CHeadCoordinateIndex (n : ℕ → ℕ) (S J : ℕ) (τ : Type) :=
  AoyagiResidualBlockCoordinateIndex
    (case2PostPivotTwoEdgeDomain n S J τ (1 : Fin 3))
    (case2PostPivotTwoEdgeDomain n S J τ 0)

/-- Scalar coordinates for the tail active `C` factor in the two-edge
retained-passive p.13 tuple. -/
abbrev CTailCoordinateIndex (n : ℕ → ℕ) (S J : ℕ) (τ : Type) :=
  AoyagiResidualBlockCoordinateIndex
    (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2))
    (case2PostPivotTwoEdgeDomain n S J τ (1 : Fin 3))

/-- Scalar coordinates for the full active `C : Fin 2 -> Matrix ...` field in
the two-edge retained-passive p.13 tuple. -/
abbrev CCoordinateIndex (n : ℕ → ℕ) (S J : ℕ) (τ : Type) :=
  Σ p : Fin 2,
    AoyagiResidualBlockCoordinateIndex
      (case2PostPivotTwoEdgeDomain n S J τ p.succ)
      (case2PostPivotTwoEdgeDomain n S J τ p.castSucc)

/-- The selected-entry center is exactly the scalar coordinate index of the
tail retained-passive `C` factor. -/
def centerEquivCTailCoordinateIndex
    (n : ℕ → ℕ) (S J : ℕ) (τ : Type) :
    Center n S J ≃ CTailCoordinateIndex n S J τ := by
  simpa [Center, CTailCoordinateIndex, case2PostPivotTwoEdgeDomain] using
    (case2ResidualBlockCoordinateIndexEquivPivotEntries n S (J + 1)).symm

/-- The selected-entry center has the same cardinality as the tail active
`C`-factor coordinate index. -/
@[simp]
theorem center_card_eq_cTailCoordinateIndex_card
    (n : ℕ → ℕ) (S J : ℕ) (τ : Type) [Fintype τ] :
    Fintype.card (Center n S J) =
      Fintype.card (CTailCoordinateIndex n S J τ) := by
  classical
  exact Fintype.card_congr (centerEquivCTailCoordinateIndex n S J τ)

/-- The head active `C` factor is the residual-column by free-endpoint block. -/
@[simp]
theorem cHeadCoordinateIndex_card
    (n : ℕ → ℕ) (S J : ℕ) (τ : Type) [Fintype τ] :
    Fintype.card (CHeadCoordinateIndex n S J τ) =
      Fintype.card (Case2ResidualColIndex n S (J + 1)) *
        Fintype.card τ := by
  change
    Fintype.card
      (AoyagiResidualBlockCoordinateIndex
        (Case2ResidualColIndex n S (J + 1)) τ) =
      Fintype.card (Case2ResidualColIndex n S (J + 1)) *
        Fintype.card τ
  exact AoyagiResidualBlockCoordinateIndex.card

/-- The tail active `C` factor is the residual-row by residual-column block. -/
@[simp]
theorem cTailCoordinateIndex_card
    (n : ℕ → ℕ) (S J : ℕ) (τ : Type) [Fintype τ] :
    Fintype.card (CTailCoordinateIndex n S J τ) =
      Fintype.card (Case2ResidualRowIndex n S (J + 1)) *
        Fintype.card (Case2ResidualColIndex n S (J + 1)) := by
  change
    Fintype.card
      (AoyagiResidualBlockCoordinateIndex
        (Case2ResidualRowIndex n S (J + 1))
        (Case2ResidualColIndex n S (J + 1))) =
      Fintype.card (Case2ResidualRowIndex n S (J + 1)) *
        Fintype.card (Case2ResidualColIndex n S (J + 1))
  exact AoyagiResidualBlockCoordinateIndex.card

/-- The full active `C` coordinate inventory splits into head and tail
coordinate blocks. -/
theorem cCoordinateIndex_card_eq_cHead_add_cTail
    (n : ℕ → ℕ) (S J : ℕ) (τ : Type) [Fintype τ] :
    Fintype.card (CCoordinateIndex n S J τ) =
      Fintype.card (CHeadCoordinateIndex n S J τ) +
        Fintype.card (CTailCoordinateIndex n S J τ) := by
  classical
  rw [Fintype.card_sigma]
  rw [Fin.sum_univ_two]
  rfl

/-- The full active `C` coordinate inventory is the head block plus the
selected-entry center.  Thus the center alone is not the full active `C`
coordinate block unless the head block is empty. -/
theorem cCoordinateIndex_card_eq_cHead_add_center
    (n : ℕ → ℕ) (S J : ℕ) (τ : Type) [Fintype τ] :
    Fintype.card (CCoordinateIndex n S J τ) =
      Fintype.card (CHeadCoordinateIndex n S J τ) +
        Fintype.card (Center n S J) := by
  rw [cCoordinateIndex_card_eq_cHead_add_cTail,
    ← center_card_eq_cTailCoordinateIndex_card]

end Case2PassiveTheta

end Aoyagi
end DLN
end DLNFibre
