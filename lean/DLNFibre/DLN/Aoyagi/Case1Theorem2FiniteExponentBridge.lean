import DLNFibre.DLN.Aoyagi.Case1FiniteExponentBridge
import DLNFibre.DLN.Aoyagi.Theorem2FiniteExponentBridge

/-!
# Case 1 bridge to the finite Theorem 2 exponent formula boundary

This file composes the Case 1 selected-entry finite exponent bridge with the
supplied finite formula boundary for Aoyagi Theorem 2.  It does not construct
normal-crossing exponent data, prove active-ratio lower bounds, prove the
displayed Theorem 2 lambda equality, prove chart-count facts, produce charts,
or invoke the normal-crossing-to-RLCT extraction theorem.
-/

namespace DLNFibre
namespace DLN
namespace Aoyagi

namespace Case1SelectedEntryA0ExponentCoordinateBridge

/-- The Case 1 selected-entry candidate ratio. -/
def theorem2CandidateRatio (n : ℕ → ℕ) (S J J1 : ℕ) : ℚ :=
  ((1 + J1 * (n (S + 1) - J) : ℕ) : ℚ) / 2

/-- Build the finite Theorem 2 exponent-formula boundary from a supplied Case
1 selected-entry coordinate, an explicit global active-ratio lower bound, a
supplied equality from the Case 1 selected-entry candidate ratio to Theorem
2's lambda formula, and a supplied order equality.

This is finite bookkeeping only.  The lower bound, lambda identification, and
order equality remain explicit supplied hypotheses. -/
theorem theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_candidateRatio_eq_fromCeilData
    {n : ℕ → ℕ} {S J J1 : ℕ}
    {D : AoyagiNormalCrossingExponentData}
    {p : Fin D.numCharts × Fin D.numCoords}
    (B : Case1SelectedEntryA0ExponentCoordinateBridge n S J J1 D p)
    {Lthm ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m)
    (hcandidate :
      theorem2CandidateRatio n S J J1 =
        aoyagiTheorem2Lambda_fromCeilData Lthm ell H r m data)
    (hleRatio : ∀ p' ∈ D.activePairs,
      theorem2CandidateRatio n S J J1 ≤ D.ratioAt p')
    (horder : D.exponentOrder = data.theorem2OrderFormula) :
    AoyagiTheorem2FiniteExponentFormulaHypothesis D Lthm ell H r m data where
  exponentMinimum_eq_theorem2Lambda_fromCeilData := by
    calc
      D.exponentMinimum = theorem2CandidateRatio n S J J1 := by
        exact B.exponentMinimum_eq_nonpivotCount_add_one_div_two_of_forall_le
          hleRatio
      _ = aoyagiTheorem2Lambda_fromCeilData Lthm ell H r m data := hcandidate
  exponentOrder_eq_theorem2OrderFormula := horder

set_option linter.style.longLine false

/-- Build the finite Theorem 2 exponent-formula boundary from a supplied Case
1 selected-entry coordinate when the order count is supplied at the Case 1
candidate ratio.

The chart-count hypotheses are converted to global-minimum chart counts only
after the active-ratio lower bound proves that the Case 1 candidate ratio is
`D.exponentMinimum`. -/
theorem
    theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_candidateRatio_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le
    {n : ℕ → ℕ} {S J J1 : ℕ}
    {D : AoyagiNormalCrossingExponentData}
    {p : Fin D.numCharts × Fin D.numCoords}
    (B : Case1SelectedEntryA0ExponentCoordinateBridge n S J J1 D p)
    {Lthm ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m)
    (hcandidate :
      theorem2CandidateRatio n S J J1 =
        aoyagiTheorem2Lambda_fromCeilData Lthm ell H r m data)
    (hleRatio : ∀ p' ∈ D.activePairs,
      theorem2CandidateRatio n S J J1 ≤ D.ratioAt p')
    {c : Fin D.numCharts}
    (hchart :
      D.countInChartAtRatio (theorem2CandidateRatio n S J J1) c =
        data.theorem2OrderFormula)
    (hleChart : ∀ c' : Fin D.numCharts,
      D.countInChartAtRatio (theorem2CandidateRatio n S J J1) c' ≤
        data.theorem2OrderFormula) :
    AoyagiTheorem2FiniteExponentFormulaHypothesis D Lthm ell H r m data :=
  theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_candidateRatio_eq_fromCeilData
    B data hcandidate hleRatio
    (D.exponentOrder_eq_of_countInChartAtRatio_eq_of_forall_le
      (B.exponentMinimum_eq_nonpivotCount_add_one_div_two_of_forall_le
        hleRatio)
      hchart hleChart)

end Case1SelectedEntryA0ExponentCoordinateBridge

namespace Case1SelectedOldUnitA0ExponentCoordinateBridge

/-- The selected-old source-moving Case 1 candidate ratio. -/
def theorem2CandidateRatio (n : ℕ → ℕ) (S J J1 : ℕ) : ℚ :=
  Case1SelectedEntryA0ExponentCoordinateBridge.theorem2CandidateRatio n S J J1

/-- Build the finite Theorem 2 exponent-formula boundary from a supplied
selected-old Case 1 coordinate, an explicit global active-ratio lower bound,
a supplied equality from the Case 1 candidate ratio to Theorem 2's lambda
formula, and a supplied order equality.

This wrapper carries the selected-old source boundary through the type of `B`;
it still does not construct the exponent data, coordinate, lower bound, lambda
identification, or order equality. -/
theorem theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_candidateRatio_eq_fromCeilData
    {R : Type*} [CommRing R]
    {Lcase : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre post : IntroducedLabelRecurrenceState Lcase n S J R}
    {u : R} {baseStep : ℕ → R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    {cert :
      Case1SelectedOldUnitSuppliedChartFamilyBoundary R Lcase n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue'
        pre post u baseStep ChartRegular TransitionRegular}
    {D : AoyagiNormalCrossingExponentData}
    {p : Fin D.numCharts × Fin D.numCoords}
    (B : Case1SelectedOldUnitA0ExponentCoordinateBridge cert D p)
    {Lthm ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m)
    (hcandidate :
      theorem2CandidateRatio n S J J1 =
        aoyagiTheorem2Lambda_fromCeilData Lthm ell H r m data)
    (hleRatio : ∀ p' ∈ D.activePairs,
      theorem2CandidateRatio n S J J1 ≤ D.ratioAt p')
    (horder : D.exponentOrder = data.theorem2OrderFormula) :
    AoyagiTheorem2FiniteExponentFormulaHypothesis D Lthm ell H r m data :=
  B.toA0ExponentCoordinateBridge
    |>.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_candidateRatio_eq_fromCeilData
      data hcandidate hleRatio horder

set_option linter.style.longLine false

/-- Build the finite Theorem 2 exponent-formula boundary from a supplied
selected-old Case 1 coordinate when the order count is supplied at the Case 1
candidate ratio.

The chart-count hypotheses are converted to global-minimum chart counts only
after the active-ratio lower bound proves that the Case 1 candidate ratio is
`D.exponentMinimum`. -/
theorem
    theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_candidateRatio_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le
    {R : Type*} [CommRing R]
    {Lcase : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre post : IntroducedLabelRecurrenceState Lcase n S J R}
    {u : R} {baseStep : ℕ → R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    {cert :
      Case1SelectedOldUnitSuppliedChartFamilyBoundary R Lcase n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue'
        pre post u baseStep ChartRegular TransitionRegular}
    {D : AoyagiNormalCrossingExponentData}
    {p : Fin D.numCharts × Fin D.numCoords}
    (B : Case1SelectedOldUnitA0ExponentCoordinateBridge cert D p)
    {Lthm ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m)
    (hcandidate :
      theorem2CandidateRatio n S J J1 =
        aoyagiTheorem2Lambda_fromCeilData Lthm ell H r m data)
    (hleRatio : ∀ p' ∈ D.activePairs,
      theorem2CandidateRatio n S J J1 ≤ D.ratioAt p')
    {c : Fin D.numCharts}
    (hchart :
      D.countInChartAtRatio (theorem2CandidateRatio n S J J1) c =
        data.theorem2OrderFormula)
    (hleChart : ∀ c' : Fin D.numCharts,
      D.countInChartAtRatio (theorem2CandidateRatio n S J J1) c' ≤
        data.theorem2OrderFormula) :
    AoyagiTheorem2FiniteExponentFormulaHypothesis D Lthm ell H r m data :=
  B.toA0ExponentCoordinateBridge
    |>.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_candidateRatio_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le
      data hcandidate hleRatio hchart hleChart

end Case1SelectedOldUnitA0ExponentCoordinateBridge

end Aoyagi
end DLN
end DLNFibre
