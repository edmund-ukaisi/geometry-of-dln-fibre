import DLNFibre.DLN.Aoyagi.BlowupArithmetic
import DLNFibre.DLN.Aoyagi.NormalCrossingInterface

/-!
# Case 2 finite exponent-coordinate bridge

This file connects the displayed continuing Case 2 finite blow-up arithmetic
to a supplied coordinate of Aoyagi's A0 finite exponent data.  It does not
construct the exponent data, prove a global minimum, prove chart coverage, or
invoke the normal-crossing-to-RLCT extraction theorem.
-/

namespace DLNFibre
namespace DLN
namespace Aoyagi

open Case2DisplayedSuppliedChartFamilyBoundary

/-- Supplied bridge saying that a coordinate in later A0 finite exponent data
is the displayed continuing Case 2 selected-entry coordinate.

The fields identify only the exponent arrays at the supplied coordinate.  The
structure does not construct the A0 exponent data, prove global lower bounds,
or assert that the formal determinant has been upgraded to an analytic
Jacobian theorem. -/
structure Case2DisplayedContinuingA0ExponentCoordinateBridge
    {τ K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J K}
    {u : K} {residual : ℕ × ℕ → K}
    {hS : 1 ≤ S} {hcont : J + 1 ≤ prefixMinNat n (S + 1)}
    {C : ℕ → τ → K}
    (cert :
      Case2DisplayedContinuingReindexedSourceChartCenterSqFormalJacobianCertificate
        L n S J t numerator leastValue pre u residual hS hcont C)
    (D : AoyagiNormalCrossingExponentData)
    (p : Fin D.numCharts × Fin D.numCoords) : Prop where
  lossExp_eq_one : D.lossExp p.1 p.2 = 1
  jacobianPriorExp_eq_formalPivotExp :
    D.jacobianPriorExp p.1 p.2 =
      ((case2ResidualBlockPivotEntries n S J).erase (J + 1, J + 1)).card

namespace Case2DisplayedContinuingA0ExponentCoordinateBridge

/-- A supplied A0 coordinate matching the displayed continuing Case 2 local
step is active and has finite ratio equal to half the residual-block center
cardinality.

This is not a statement about the global minimum of `D`: that still requires
lower bounds over all active coordinates. -/
theorem activePair_and_ratioAt_eq_centerCard_div_two
    {τ K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J K}
    {u : K} {residual : ℕ × ℕ → K}
    {hS : 1 ≤ S} {hcont : J + 1 ≤ prefixMinNat n (S + 1)}
    {C : ℕ → τ → K}
    {cert :
      Case2DisplayedContinuingReindexedSourceChartCenterSqFormalJacobianCertificate
        L n S J t numerator leastValue pre u residual hS hcont C}
    {D : AoyagiNormalCrossingExponentData}
    {p : Fin D.numCharts × Fin D.numCoords}
    (B : Case2DisplayedContinuingA0ExponentCoordinateBridge cert D p) :
    p ∈ D.activePairs ∧
      D.ratioAt p = ((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2 := by
  refine ⟨D.mem_activePairs_of_lossExp_eq_one B.lossExp_eq_one, ?_⟩
  refine D.ratioAt_eq_nat_div_two_of_lossExp_eq_one_of_jacobianPriorExp_add_one_eq
    B.lossExp_eq_one ?_
  calc
    D.jacobianPriorExp p.1 p.2 + 1 =
        ((case2ResidualBlockPivotEntries n S J).erase (J + 1, J + 1)).card + 1 := by
          rw [B.jacobianPriorExp_eq_formalPivotExp]
    _ = (case2ResidualBlockPivotEntries n S J).card :=
          cert.pivotFirstJacobian_exponent_add_one_eq_centerCard

/-- Active-pair projection from the supplied Case 2/A0 exponent-coordinate
bridge. -/
theorem activePair
    {τ K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J K}
    {u : K} {residual : ℕ × ℕ → K}
    {hS : 1 ≤ S} {hcont : J + 1 ≤ prefixMinNat n (S + 1)}
    {C : ℕ → τ → K}
    {cert :
      Case2DisplayedContinuingReindexedSourceChartCenterSqFormalJacobianCertificate
        L n S J t numerator leastValue pre u residual hS hcont C}
    {D : AoyagiNormalCrossingExponentData}
    {p : Fin D.numCharts × Fin D.numCoords}
    (B : Case2DisplayedContinuingA0ExponentCoordinateBridge cert D p) :
    p ∈ D.activePairs :=
  (B.activePair_and_ratioAt_eq_centerCard_div_two).1

/-- Ratio projection from the supplied Case 2/A0 exponent-coordinate bridge. -/
theorem ratioAt_eq_centerCard_div_two
    {τ K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J K}
    {u : K} {residual : ℕ × ℕ → K}
    {hS : 1 ≤ S} {hcont : J + 1 ≤ prefixMinNat n (S + 1)}
    {C : ℕ → τ → K}
    {cert :
      Case2DisplayedContinuingReindexedSourceChartCenterSqFormalJacobianCertificate
        L n S J t numerator leastValue pre u residual hS hcont C}
    {D : AoyagiNormalCrossingExponentData}
    {p : Fin D.numCharts × Fin D.numCoords}
    (B : Case2DisplayedContinuingA0ExponentCoordinateBridge cert D p) :
    D.ratioAt p = ((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2 :=
  (B.activePair_and_ratioAt_eq_centerCard_div_two).2

end Case2DisplayedContinuingA0ExponentCoordinateBridge

end Aoyagi
end DLN
end DLNFibre
