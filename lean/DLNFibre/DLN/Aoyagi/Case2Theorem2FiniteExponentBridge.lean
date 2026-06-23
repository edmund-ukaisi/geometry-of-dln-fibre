import DLNFibre.DLN.Aoyagi.Case2FiniteExponentBridge
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

end Case2DisplayedContinuingA0ExponentCoordinateBridge

end Aoyagi
end DLN
end DLNFibre
