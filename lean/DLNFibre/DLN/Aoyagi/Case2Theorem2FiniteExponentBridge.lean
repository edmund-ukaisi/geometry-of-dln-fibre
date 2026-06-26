import DLNFibre.DLN.Aoyagi.Case2FiniteExponentBridge
import DLNFibre.DLN.Aoyagi.RegularVariableShift
import DLNFibre.DLN.Aoyagi.Theorem2FiniteExponentBridge

/-!
# Case 2 bridge to the finite Theorem 2 exponent formula boundary

This file composes the displayed continuing Case 2 finite exponent bridge with
the supplied finite formula boundary for Aoyagi Theorem 2.  It does not
construct normal-crossing exponent data, prove active-ratio lower bounds,
prove the displayed Theorem 2 lambda equality, prove the order formula, produce
charts, or invoke the normal-crossing-to-RLCT extraction theorem.
-/

namespace DLNFibre
namespace DLN
namespace Aoyagi

open Case2DisplayedSuppliedChartFamilyBoundary

namespace Case2DisplayedContinuingA0ExponentCoordinateBridge

/-- Build the finite Theorem 2 exponent-formula boundary from a displayed
continuing Case 2 coordinate, an explicit global active-ratio lower bound, a
supplied equality from the displayed Case 2 center cardinality to Theorem 2's
lambda formula, and a supplied order equality.

This is finite bookkeeping only.  The lower bound, lambda identification, and
order equality remain explicit supplied hypotheses. -/
theorem theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_centerCard_eq_fromCeilData
    {τ K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {Lcase : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState Lcase n S J K}
    {u : K} {residual : ℕ × ℕ → K}
    {hS : 1 ≤ S} {hcont : J + 1 ≤ prefixMinNat n (S + 1)}
    {C : ℕ → τ → K}
    {cert :
      Case2DisplayedContinuingReindexedSourceChartCenterSqFormalJacobianCertificate
        Lcase n S J t numerator leastValue pre u residual hS hcont C}
    {D : AoyagiNormalCrossingExponentData}
    {p : Fin D.numCharts × Fin D.numCoords}
    (B : Case2DisplayedContinuingA0ExponentCoordinateBridge cert D p)
    {Lthm ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m)
    (hcenter :
      ((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2 =
        aoyagiTheorem2Lambda_fromCeilData Lthm ell H r m data)
    (hleRatio : ∀ p' ∈ D.activePairs,
      ((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2 ≤ D.ratioAt p')
    (horder : D.exponentOrder = data.theorem2OrderFormula) :
    AoyagiTheorem2FiniteExponentFormulaHypothesis D Lthm ell H r m data where
  exponentMinimum_eq_theorem2Lambda_fromCeilData := by
    calc
      D.exponentMinimum =
          ((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2 :=
        B.exponentMinimum_eq_centerCard_div_two_of_forall_le hleRatio
      _ = aoyagiTheorem2Lambda_fromCeilData Lthm ell H r m data := hcenter
  exponentOrder_eq_theorem2OrderFormula := horder

set_option linter.style.longLine false

/-- Build the finite Theorem 2 exponent-formula boundary from a displayed
continuing Case 2 coordinate when the order count is supplied at the displayed
Case 2 candidate ratio.

The chart-count hypotheses are converted to global-minimum chart counts only
after the active-ratio lower bound proves that the Case 2 candidate ratio is
`D.exponentMinimum`. -/
theorem
    theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_centerCard_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le
    {τ K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {Lcase : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState Lcase n S J K}
    {u : K} {residual : ℕ × ℕ → K}
    {hS : 1 ≤ S} {hcont : J + 1 ≤ prefixMinNat n (S + 1)}
    {C : ℕ → τ → K}
    {cert :
      Case2DisplayedContinuingReindexedSourceChartCenterSqFormalJacobianCertificate
        Lcase n S J t numerator leastValue pre u residual hS hcont C}
    {D : AoyagiNormalCrossingExponentData}
    {p : Fin D.numCharts × Fin D.numCoords}
    (B : Case2DisplayedContinuingA0ExponentCoordinateBridge cert D p)
    {Lthm ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m)
    (hcenter :
      ((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2 =
        aoyagiTheorem2Lambda_fromCeilData Lthm ell H r m data)
    (hleRatio : ∀ p' ∈ D.activePairs,
      ((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2 ≤ D.ratioAt p')
    {c : Fin D.numCharts}
    (hchart :
      D.countInChartAtRatio
          (((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2) c =
        data.theorem2OrderFormula)
    (hleChart : ∀ c' : Fin D.numCharts,
      D.countInChartAtRatio
          (((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2) c' ≤
        data.theorem2OrderFormula) :
    AoyagiTheorem2FiniteExponentFormulaHypothesis D Lthm ell H r m data :=
  theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_centerCard_eq_fromCeilData
    B data hcenter hleRatio
    (D.exponentOrder_eq_of_countInChartAtRatio_eq_of_forall_le
      (B.exponentMinimum_eq_centerCard_div_two_of_forall_le hleRatio)
      hchart hleChart)

/-- Regular-variable shifted version of
`theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_centerCard_eq_fromCeilData`.

The Case 2 center-cardinality ratio is a reduced finite exponent.  This theorem
uses the regular-variable shift to compare the reduced ratio plus Aoyagi's
regular term with the full Theorem 2 lambda formula.  The active-ratio lower
bound, shifted lambda identification, endpoint rank bounds, and order equality
remain explicit supplied hypotheses. -/
theorem
    theorem2FiniteExponentFormulaHypothesis_regularVariableCountShift_of_forall_le_of_centerCard_add_regularTerm_eq_fromCeilData
    {τ K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {Lcase : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState Lcase n S J K}
    {u : K} {residual : ℕ × ℕ → K}
    {hS : 1 ≤ S} {hcont : J + 1 ≤ prefixMinNat n (S + 1)}
    {C : ℕ → τ → K}
    {cert :
      Case2DisplayedContinuingReindexedSourceChartCenterSqFormalJacobianCertificate
        Lcase n S J t numerator leastValue pre u residual hS hcont C}
    {D : AoyagiNormalCrossingExponentData}
    {p : Fin D.numCharts × Fin D.numCoords}
    (B : Case2DisplayedContinuingA0ExponentCoordinateBridge cert D p)
    {Lthm ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m)
    (hsource : r ≤ H 1) (htarget : r ≤ H (Lthm + 1))
    (hcenterShift :
      ((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2 +
          aoyagiTheorem2RegularTerm Lthm H r =
        aoyagiTheorem2Lambda_fromCeilData Lthm ell H r m data)
    (hleRatio : ∀ p' ∈ D.activePairs,
      ((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2 ≤ D.ratioAt p')
    (horder : D.exponentOrder = data.theorem2OrderFormula) :
    AoyagiTheorem2FiniteExponentFormulaHypothesis
      (D.jacobianPriorLossShift
        (aoyagiTheorem2RegularVariableCount Lthm H r))
      Lthm ell H r m data := by
  refine
    AoyagiTheorem2FiniteExponentFormulaHypothesis.of_regularVariableCountShift
      data hsource htarget ?_ horder
  calc
    D.exponentMinimum + aoyagiTheorem2RegularTerm Lthm H r =
        ((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2 +
          aoyagiTheorem2RegularTerm Lthm H r := by
      rw [B.exponentMinimum_eq_centerCard_div_two_of_forall_le hleRatio]
    _ = aoyagiTheorem2Lambda_fromCeilData Lthm ell H r m data :=
      hcenterShift

/-- Chart-count version of
`theorem2FiniteExponentFormulaHypothesis_regularVariableCountShift_of_forall_le_of_centerCard_add_regularTerm_eq_fromCeilData`.

The reduced chart-count hypotheses are evaluated at the Case 2 center ratio and
converted to a reduced exponent-order equality before applying the
regular-variable shift. -/
theorem
    theorem2FiniteExponentFormulaHypothesis_regularVariableCountShift_of_forall_le_of_centerCard_add_regularTerm_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le
    {τ K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {Lcase : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState Lcase n S J K}
    {u : K} {residual : ℕ × ℕ → K}
    {hS : 1 ≤ S} {hcont : J + 1 ≤ prefixMinNat n (S + 1)}
    {C : ℕ → τ → K}
    {cert :
      Case2DisplayedContinuingReindexedSourceChartCenterSqFormalJacobianCertificate
        Lcase n S J t numerator leastValue pre u residual hS hcont C}
    {D : AoyagiNormalCrossingExponentData}
    {p : Fin D.numCharts × Fin D.numCoords}
    (B : Case2DisplayedContinuingA0ExponentCoordinateBridge cert D p)
    {Lthm ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m)
    (hsource : r ≤ H 1) (htarget : r ≤ H (Lthm + 1))
    (hcenterShift :
      ((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2 +
          aoyagiTheorem2RegularTerm Lthm H r =
        aoyagiTheorem2Lambda_fromCeilData Lthm ell H r m data)
    (hleRatio : ∀ p' ∈ D.activePairs,
      ((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2 ≤ D.ratioAt p')
    {c : Fin D.numCharts}
    (hchart :
      D.countInChartAtRatio
          (((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2) c =
        data.theorem2OrderFormula)
    (hleChart : ∀ c' : Fin D.numCharts,
      D.countInChartAtRatio
          (((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2) c' ≤
        data.theorem2OrderFormula) :
    AoyagiTheorem2FiniteExponentFormulaHypothesis
      (D.jacobianPriorLossShift
        (aoyagiTheorem2RegularVariableCount Lthm H r))
      Lthm ell H r m data :=
  theorem2FiniteExponentFormulaHypothesis_regularVariableCountShift_of_forall_le_of_centerCard_add_regularTerm_eq_fromCeilData
    B data hsource htarget hcenterShift hleRatio
    (D.exponentOrder_eq_of_countInChartAtRatio_eq_of_forall_le
      (B.exponentMinimum_eq_centerCard_div_two_of_forall_le hleRatio)
      hchart hleChart)

end Case2DisplayedContinuingA0ExponentCoordinateBridge

end Aoyagi
end DLN
end DLNFibre
