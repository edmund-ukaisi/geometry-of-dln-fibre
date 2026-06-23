import DLNFibre.DLN.Aoyagi.Theorem2FiniteExponentBridge

/-!
# Regular-variable finite shift for Aoyagi Theorem 2

This file connects Aoyagi's post-Theorem-3 regular block-entry count to the
existing finite normal-crossing Jacobian/prior exponent shift.  It is only
finite certificate arithmetic: no regular-suspension chart construction,
analytic ideal transport, regular-coordinate additivity theorem, pole-order
theorem, or RLCT theorem is proved here.
-/

namespace DLNFibre
namespace DLN
namespace Aoyagi

namespace AoyagiNormalCrossingExponentData

/-- Shifting Jacobian/prior exponents by Aoyagi's regular block-entry count
shifts the finite minimum by the displayed regular term. -/
theorem exponentMinimum_jacobianPriorLossShift_regularVariableCount
    (D : AoyagiNormalCrossingExponentData)
    (L : ℕ) (H : ℕ → ℕ) {r : ℕ}
    (hsource : r ≤ H 1) (htarget : r ≤ H (L + 1)) :
    (D.jacobianPriorLossShift
        (aoyagiTheorem2RegularVariableCount L H r)).exponentMinimum =
      D.exponentMinimum + aoyagiTheorem2RegularTerm L H r := by
  rw [D.exponentMinimum_jacobianPriorLossShift]
  rw [aoyagiTheorem2RegularTerm_eq_half_regularVariableCount
    L H hsource htarget]

/-- Shifting by Aoyagi's regular block-entry count preserves the finite order. -/
theorem exponentOrder_jacobianPriorLossShift_regularVariableCount
    (D : AoyagiNormalCrossingExponentData)
    (L : ℕ) (H : ℕ → ℕ) (r : ℕ) :
    (D.jacobianPriorLossShift
        (aoyagiTheorem2RegularVariableCount L H r)).exponentOrder =
      D.exponentOrder :=
  D.exponentOrder_jacobianPriorLossShift
    (aoyagiTheorem2RegularVariableCount L H r)

end AoyagiNormalCrossingExponentData

namespace AoyagiNormalCrossingChartCertificate

variable {Param R : Type*} [CommMonoid R]

/-- Chart-certificate projection of the finite regular-variable count shift. -/
theorem exponentData_exponentMinimum_jacobianPriorLossShift_regularVariableCount
    (C : AoyagiNormalCrossingChartCertificate Param R)
    (L : ℕ) (H : ℕ → ℕ) {r : ℕ}
    (hsource : r ≤ H 1) (htarget : r ≤ H (L + 1)) :
    (C.jacobianPriorLossShift
        (aoyagiTheorem2RegularVariableCount L H r)).exponentData.exponentMinimum =
      C.exponentData.exponentMinimum + aoyagiTheorem2RegularTerm L H r := by
  rw [C.exponentData_jacobianPriorLossShift]
  exact
    C.exponentData.exponentMinimum_jacobianPriorLossShift_regularVariableCount
      L H hsource htarget

/-- Chart-certificate projection: the finite order is unchanged by the
regular-variable count shift. -/
theorem exponentData_exponentOrder_jacobianPriorLossShift_regularVariableCount
    (C : AoyagiNormalCrossingChartCertificate Param R)
    (L : ℕ) (H : ℕ → ℕ) (r : ℕ) :
    (C.jacobianPriorLossShift
        (aoyagiTheorem2RegularVariableCount L H r)).exponentData.exponentOrder =
      C.exponentData.exponentOrder := by
  rw [C.exponentData_jacobianPriorLossShift]
  exact
    C.exponentData.exponentOrder_jacobianPriorLossShift_regularVariableCount
      L H r

end AoyagiNormalCrossingChartCertificate

namespace AoyagiTheorem2FiniteExponentFormulaHypothesis

/-- Build the Theorem 2 finite formula boundary after shifting by the
post-Theorem-3 regular block-entry count.

The reduced minimum equality remains supplied in the form saying that the
reduced finite minimum plus Aoyagi's regular term equals the displayed final
lambda formula.  This is only finite exponent-array arithmetic; it does not
construct the regular-suspension chart or prove analytic additivity. -/
theorem of_regularVariableCountShift
    {D : AoyagiNormalCrossingExponentData}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m)
    (hsource : r ≤ H 1) (htarget : r ≤ H (L + 1))
    (hmin :
      D.exponentMinimum + aoyagiTheorem2RegularTerm L H r =
        aoyagiTheorem2Lambda_fromCeilData L ell H r m data)
    (horder : D.exponentOrder = data.theorem2OrderFormula) :
    AoyagiTheorem2FiniteExponentFormulaHypothesis
      (D.jacobianPriorLossShift
        (aoyagiTheorem2RegularVariableCount L H r))
      L ell H r m data where
  exponentMinimum_eq_theorem2Lambda_fromCeilData := by
    rw [D.exponentMinimum_jacobianPriorLossShift_regularVariableCount
      L H hsource htarget]
    exact hmin
  exponentOrder_eq_theorem2OrderFormula := by
    rw [D.exponentOrder_jacobianPriorLossShift_regularVariableCount]
    exact horder

/-- Chart-certificate version of `of_regularVariableCountShift`, using the
projected exponent data of a supplied chart certificate. -/
theorem of_chart_regularVariableCountShift
    {Param R : Type*} [CommMonoid R]
    {C : AoyagiNormalCrossingChartCertificate Param R}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m)
    (hsource : r ≤ H 1) (htarget : r ≤ H (L + 1))
    (hmin :
      C.exponentData.exponentMinimum + aoyagiTheorem2RegularTerm L H r =
        aoyagiTheorem2Lambda_fromCeilData L ell H r m data)
    (horder : C.exponentData.exponentOrder = data.theorem2OrderFormula) :
    AoyagiTheorem2FiniteExponentFormulaHypothesis
      (C.jacobianPriorLossShift
        (aoyagiTheorem2RegularVariableCount L H r)).exponentData
      L ell H r m data := by
  rw [C.exponentData_jacobianPriorLossShift]
  exact of_regularVariableCountShift data hsource htarget hmin horder

end AoyagiTheorem2FiniteExponentFormulaHypothesis

end Aoyagi
end DLN
end DLNFibre
