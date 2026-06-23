import DLNFibre.DLN.Aoyagi.BlowupArithmetic
import DLNFibre.DLN.Aoyagi.NormalCrossingInterface

/-!
# Case 2 finite exponent-coordinate bridge

This file connects the displayed continuing Case 2 finite blow-up arithmetic
to a supplied coordinate of finite normal-crossing exponent data.  It first
provides a generic finite exponent-coordinate bridge, then an A0-facing wrapper
for data intended to represent the full normal-crossing problem.  It does not
construct exponent data, prove the lower bounds needed for an unconditional
global minimum, prove chart coverage, or invoke the normal-crossing-to-RLCT
extraction theorem.
-/

namespace DLNFibre
namespace DLN
namespace Aoyagi

open Case2DisplayedSuppliedChartFamilyBoundary

/-- Generic finite exponent-coordinate bridge saying that a coordinate in
finite normal-crossing exponent data has the displayed continuing Case 2
selected-entry exponents.

The fields identify only the exponent arrays at the supplied coordinate.  The
structure does not construct exponent data, prove global lower bounds, or
assert that the formal determinant has been upgraded to an analytic Jacobian
theorem. -/
structure Case2DisplayedContinuingExponentCoordinateBridge
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

namespace Case2DisplayedContinuingExponentCoordinateBridge

/-- Build the generic Case 2 exponent-coordinate bridge when the matching
exponent equalities are stated on a chart certificate rather than on its
projected finite exponent data.

This is only a projection adapter.  It does not construct the chart
certificate, the coordinate, any chart coverage, or any analytic extraction
input. -/
theorem of_chartCertificate_coord_exponents
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
    {Param R : Type*} [CommMonoid R]
    {Cnc : AoyagiNormalCrossingChartCertificate Param R}
    {p : Fin Cnc.numCharts × Fin Cnc.numCoords}
    (hloss : Cnc.lossExp p.1 p.2 = 1)
    (hjac : Cnc.jacobianPriorExp p.1 p.2 =
      ((case2ResidualBlockPivotEntries n S J).erase (J + 1, J + 1)).card) :
    Case2DisplayedContinuingExponentCoordinateBridge cert Cnc.exponentData p where
  lossExp_eq_one := by
    simpa using hloss
  jacobianPriorExp_eq_formalPivotExp := by
    simpa using hjac

/-- A supplied finite exponent coordinate matching the displayed continuing
Case 2 local step is active and has finite ratio equal to half the
residual-block center cardinality.

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
    (B : Case2DisplayedContinuingExponentCoordinateBridge cert D p) :
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

/-- Active-pair projection from the generic Case 2 exponent-coordinate
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
    (B : Case2DisplayedContinuingExponentCoordinateBridge cert D p) :
    p ∈ D.activePairs :=
  (B.activePair_and_ratioAt_eq_centerCard_div_two).1

/-- Ratio projection from the generic Case 2 exponent-coordinate bridge. -/
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
    (B : Case2DisplayedContinuingExponentCoordinateBridge cert D p) :
    D.ratioAt p = ((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2 :=
  (B.activePair_and_ratioAt_eq_centerCard_div_two).2

/-- If the displayed Case 2 local ratio lower-bounds every active coordinate,
then it is the finite exponent minimum of the supplied finite exponent data.

This does not prove the lower bound, construct exponent data, or prove any
chart/analytic statement. -/
theorem exponentMinimum_eq_centerCard_div_two_of_forall_le
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
    (B : Case2DisplayedContinuingExponentCoordinateBridge cert D p)
    (hle : ∀ p' ∈ D.activePairs,
      ((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2 ≤ D.ratioAt p') :
    D.exponentMinimum =
      ((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2 :=
  D.exponentMinimum_eq_of_activePair_ratioAt_eq_of_forall_le
    B.activePair B.ratioAt_eq_centerCard_div_two hle

end Case2DisplayedContinuingExponentCoordinateBridge

/-- A0-facing wrapper around the generic displayed continuing Case 2
exponent-coordinate bridge.

Use this name only when the supplied finite exponent data is meant to be the
later A0 data for the full normal-crossing problem.  Local finite
microcertificates should use
`Case2DisplayedContinuingExponentCoordinateBridge` directly. -/
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
  toExponentCoordinateBridge :
    Case2DisplayedContinuingExponentCoordinateBridge cert D p

namespace Case2DisplayedContinuingA0ExponentCoordinateBridge

/-- Loss-exponent projection from the A0-facing wrapper. -/
theorem lossExp_eq_one
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
    D.lossExp p.1 p.2 = 1 :=
  B.toExponentCoordinateBridge.lossExp_eq_one

/-- Formal-Jacobian exponent projection from the A0-facing wrapper. -/
theorem jacobianPriorExp_eq_formalPivotExp
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
    D.jacobianPriorExp p.1 p.2 =
      ((case2ResidualBlockPivotEntries n S J).erase (J + 1, J + 1)).card :=
  B.toExponentCoordinateBridge.jacobianPriorExp_eq_formalPivotExp

/-- Build the supplied Case 2/A0 exponent-coordinate bridge when the matching
exponent equalities are stated on a chart certificate rather than on its
projected finite exponent data.

This is only a projection adapter.  It does not construct the chart
certificate, the coordinate, any chart coverage, or any analytic extraction
input. -/
theorem of_chartCertificate_coord_exponents
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
    {Param R : Type*} [CommMonoid R]
    {Cnc : AoyagiNormalCrossingChartCertificate Param R}
    {p : Fin Cnc.numCharts × Fin Cnc.numCoords}
    (hloss : Cnc.lossExp p.1 p.2 = 1)
    (hjac : Cnc.jacobianPriorExp p.1 p.2 =
      ((case2ResidualBlockPivotEntries n S J).erase (J + 1, J + 1)).card) :
    Case2DisplayedContinuingA0ExponentCoordinateBridge cert Cnc.exponentData p where
  toExponentCoordinateBridge :=
    Case2DisplayedContinuingExponentCoordinateBridge.of_chartCertificate_coord_exponents
      hloss hjac

/-- Active pair and ratio projection from the A0-facing wrapper. -/
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
      D.ratioAt p = ((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2 :=
  B.toExponentCoordinateBridge.activePair_and_ratioAt_eq_centerCard_div_two

/-- Active-pair projection from the A0-facing wrapper. -/
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
  B.toExponentCoordinateBridge.activePair

/-- Ratio projection from the A0-facing wrapper. -/
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
  B.toExponentCoordinateBridge.ratioAt_eq_centerCard_div_two

/-- If the displayed Case 2 local ratio lower-bounds every active coordinate,
then it is the finite exponent minimum of the supplied A0 exponent data.

This does not prove the lower bound, construct the A0 exponent data, or prove
any chart/analytic statement. -/
theorem exponentMinimum_eq_centerCard_div_two_of_forall_le
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
    (B : Case2DisplayedContinuingA0ExponentCoordinateBridge cert D p)
    (hle : ∀ p' ∈ D.activePairs,
      ((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2 ≤ D.ratioAt p') :
    D.exponentMinimum =
      ((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2 :=
  B.toExponentCoordinateBridge.exponentMinimum_eq_centerCard_div_two_of_forall_le hle

end Case2DisplayedContinuingA0ExponentCoordinateBridge

end Aoyagi
end DLN
end DLNFibre
