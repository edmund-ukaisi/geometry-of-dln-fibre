import DLNFibre.DLN.Aoyagi.Definition3Bridge
import DLNFibre.DLN.Aoyagi.Theorem2FiniteExponentBridge

/-!
# Supplied final assembly boundary for Aoyagi Theorem 2

This file packages the currently explicit final socket for Aoyagi's Theorem 2.
It composes supplied source-facing selected-width provenance, supplied finite
normal-crossing exponent formula equalities, and the A0 extraction hypothesis.

It does not prove selected cutpoint existence, rank-width hypotheses from a
matrix product, source production of the normal-crossing certificate,
finite exponent formula equalities, Lemma 5 no-extra coverage or order count,
chart coverage, pole order without A0, or the analytic extraction theorem.
-/

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- Supplied boundary data sufficient to read the existing A6/A0 bridge as
Aoyagi Theorem 2's displayed formulas.

The selected-width equality records provenance of the displayed selected
widths; the formula conclusions still use only the supplied finite exponent
equalities and the explicit A0 extraction hypothesis. -/
structure AoyagiTheorem2SuppliedFinalBoundary
    (D : AoyagiNormalCrossingExponentData)
    (L ell : ℕ) (H : ℕ → ℕ) (r : ℕ)
    (C : AoyagiSelectedCutpoints ell) (m : Fin (ell + 1) → ℤ)
    (data : AoyagiDefinition3CeilData ell m)
    (lambda : ℚ) (poleOrder : ℕ) : Prop where
  selectedWidths_eq_reduced :
    m = aoyagiSelectedReducedWidths H r C
  extractionHypothesis :
    AoyagiNormalCrossingExtractionHypothesis D lambda poleOrder
  finiteExponentFormula :
    AoyagiTheorem2FiniteExponentFormulaHypothesis D L ell H r m data

namespace AoyagiTheorem2SuppliedFinalBoundary

/-- The supplied selected widths are the integer reduced widths at the selected
cutpoints. -/
theorem selectedWidths_apply_eq_reducedWidthInt
    {D : AoyagiNormalCrossingExponentData}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell} {m : Fin (ell + 1) → ℤ}
    {data : AoyagiDefinition3CeilData ell m} {lambda : ℚ} {poleOrder : ℕ}
    (B : AoyagiTheorem2SuppliedFinalBoundary D L ell H r C m data lambda poleOrder)
    (j : Fin (ell + 1)) :
    m j = aoyagiReducedWidthInt H r (C.cut j) := by
  rw [B.selectedWidths_eq_reduced]
  rfl

/-- Under the supplied selected rank-width hypotheses, selected widths are
ordinary natural reduced widths coerced to integers. -/
theorem selectedWidths_eq_natCast_sub
    {D : AoyagiNormalCrossingExponentData}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell} {m : Fin (ell + 1) → ℤ}
    {data : AoyagiDefinition3CeilData ell m} {lambda : ℚ} {poleOrder : ℕ}
    (B : AoyagiTheorem2SuppliedFinalBoundary D L ell H r C m data lambda poleOrder)
    (hr : ∀ j : Fin (ell + 1), r ≤ H (C.cut j))
    (j : Fin (ell + 1)) :
    m j = ((H (C.cut j) - r : ℕ) : ℤ) := by
  rw [B.selectedWidths_eq_reduced]
  exact aoyagiSelectedReducedWidths_eq_natCast_sub_of_rank_le
    H r C hr j

/-- The supplied selected widths are nonnegative under the supplied selected
rank-width hypotheses. -/
theorem selectedWidths_nonneg
    {D : AoyagiNormalCrossingExponentData}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell} {m : Fin (ell + 1) → ℤ}
    {data : AoyagiDefinition3CeilData ell m} {lambda : ℚ} {poleOrder : ℕ}
    (B : AoyagiTheorem2SuppliedFinalBoundary D L ell H r C m data lambda poleOrder)
    (hr : ∀ j : Fin (ell + 1), r ≤ H (C.cut j))
    (j : Fin (ell + 1)) :
    0 ≤ m j := by
  rw [B.selectedWidths_eq_reduced]
  exact aoyagiSelectedReducedWidths_nonneg_of_rank_le
    H r C hr j

/-- The Nat-indexed selected-width accessor is nonnegative under the supplied
selected rank-width hypotheses. -/
theorem selectedWidthNat_nonneg
    {D : AoyagiNormalCrossingExponentData}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell} {m : Fin (ell + 1) → ℤ}
    {data : AoyagiDefinition3CeilData ell m} {lambda : ℚ} {poleOrder : ℕ}
    (B : AoyagiTheorem2SuppliedFinalBoundary D L ell H r C m data lambda poleOrder)
    (hr : ∀ j : Fin (ell + 1), r ≤ H (C.cut j))
    (i : ℕ) :
    0 ≤ aoyagiSelectedWidthNat ell m i := by
  rw [B.selectedWidths_eq_reduced]
  exact aoyagiSelectedWidthNat_selectedReducedWidths_nonneg_of_rank_le
    H (r := r) (i := i) C hr

/-- A separately supplied source-selected inequality gives Definition 3's
selected-width upper bound. -/
theorem selectedWidth_le_pred
    {ell : ℕ} {m : Fin (ell + 1) → ℤ}
    {data : AoyagiDefinition3CeilData ell m}
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (i : Fin (ell + 1)) :
    m i ≤ data.ceilWidth - 1 :=
  data.selectedWidth_le_pred_of_sourceSelectedInequality
    hsource i

/-- Projection to the ceiling-data form of Aoyagi Theorem 2's displayed
`lambda` formula. -/
theorem lambda_eq_theorem2Lambda_fromCeilData
    {D : AoyagiNormalCrossingExponentData}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell} {m : Fin (ell + 1) → ℤ}
    {data : AoyagiDefinition3CeilData ell m} {lambda : ℚ} {poleOrder : ℕ}
    (B : AoyagiTheorem2SuppliedFinalBoundary D L ell H r C m data lambda poleOrder) :
    lambda = aoyagiTheorem2Lambda_fromCeilData L ell H r m data :=
  B.finiteExponentFormula.lambda_eq_theorem2Lambda_fromCeilData_of_extractionHypothesis
    B.extractionHypothesis

/-- Projection to the average form of Aoyagi Theorem 2's displayed `lambda`
formula. -/
theorem lambda_eq_theorem2Lambda_average
    {D : AoyagiNormalCrossingExponentData}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell} {m : Fin (ell + 1) → ℤ}
    {data : AoyagiDefinition3CeilData ell m} {lambda : ℚ} {poleOrder : ℕ}
    (B : AoyagiTheorem2SuppliedFinalBoundary D L ell H r C m data lambda poleOrder) :
    lambda = aoyagiTheorem2Lambda_average L ell H r data.aParam m :=
  B.finiteExponentFormula.lambda_eq_theorem2Lambda_average_of_extractionHypothesis
    B.extractionHypothesis

/-- Projection to the expanded form of Aoyagi Theorem 2's displayed `lambda`
formula. -/
theorem lambda_eq_theorem2Lambda_expanded
    {D : AoyagiNormalCrossingExponentData}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell} {m : Fin (ell + 1) → ℤ}
    {data : AoyagiDefinition3CeilData ell m} {lambda : ℚ} {poleOrder : ℕ}
    (B : AoyagiTheorem2SuppliedFinalBoundary D L ell H r C m data lambda poleOrder) :
    lambda =
      aoyagiTheorem2Lambda_expanded L ell H r data.aParam data.ceilWidth m :=
  B.finiteExponentFormula.lambda_eq_theorem2Lambda_expanded_of_extractionHypothesis
    B.extractionHypothesis

/-- Projection to Aoyagi Theorem 2's displayed order formula. -/
theorem poleOrder_eq_theorem2OrderFormula
    {D : AoyagiNormalCrossingExponentData}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell} {m : Fin (ell + 1) → ℤ}
    {data : AoyagiDefinition3CeilData ell m} {lambda : ℚ} {poleOrder : ℕ}
    (B : AoyagiTheorem2SuppliedFinalBoundary D L ell H r C m data lambda poleOrder) :
    poleOrder = data.theorem2OrderFormula :=
  B.finiteExponentFormula.poleOrder_eq_theorem2OrderFormula_of_extractionHypothesis
    B.extractionHypothesis

/-- Pair form of the supplied final assembly, using the ceiling-data `lambda`
formula. -/
theorem lambda_and_poleOrder_eq_fromCeilData_and_orderFormula
    {D : AoyagiNormalCrossingExponentData}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell} {m : Fin (ell + 1) → ℤ}
    {data : AoyagiDefinition3CeilData ell m} {lambda : ℚ} {poleOrder : ℕ}
    (B : AoyagiTheorem2SuppliedFinalBoundary D L ell H r C m data lambda poleOrder) :
    lambda = aoyagiTheorem2Lambda_fromCeilData L ell H r m data ∧
      poleOrder = data.theorem2OrderFormula := by
  exact ⟨B.lambda_eq_theorem2Lambda_fromCeilData,
    B.poleOrder_eq_theorem2OrderFormula⟩

/-- Pair form of the supplied final assembly, using the expanded `lambda`
formula. -/
theorem lambda_and_poleOrder_eq_expanded_and_orderFormula
    {D : AoyagiNormalCrossingExponentData}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell} {m : Fin (ell + 1) → ℤ}
    {data : AoyagiDefinition3CeilData ell m} {lambda : ℚ} {poleOrder : ℕ}
    (B : AoyagiTheorem2SuppliedFinalBoundary D L ell H r C m data lambda poleOrder) :
    lambda =
        aoyagiTheorem2Lambda_expanded L ell H r data.aParam data.ceilWidth m ∧
      poleOrder = data.theorem2OrderFormula := by
  exact ⟨B.lambda_eq_theorem2Lambda_expanded, B.poleOrder_eq_theorem2OrderFormula⟩

/-- Average-form projection with the selected-width family rewritten to the
source reduced-width family. -/
theorem lambda_eq_theorem2Lambda_average_selectedReducedWidths
    {D : AoyagiNormalCrossingExponentData}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell} {m : Fin (ell + 1) → ℤ}
    {data : AoyagiDefinition3CeilData ell m} {lambda : ℚ} {poleOrder : ℕ}
    (B : AoyagiTheorem2SuppliedFinalBoundary D L ell H r C m data lambda poleOrder) :
    lambda =
      aoyagiTheorem2Lambda_average L ell H r data.aParam
        (aoyagiSelectedReducedWidths H r C) := by
  simpa [B.selectedWidths_eq_reduced] using B.lambda_eq_theorem2Lambda_average

/-- Expanded-form projection with the selected-width family rewritten to the
source reduced-width family. -/
theorem lambda_eq_theorem2Lambda_expanded_selectedReducedWidths
    {D : AoyagiNormalCrossingExponentData}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell} {m : Fin (ell + 1) → ℤ}
    {data : AoyagiDefinition3CeilData ell m} {lambda : ℚ} {poleOrder : ℕ}
    (B : AoyagiTheorem2SuppliedFinalBoundary D L ell H r C m data lambda poleOrder) :
    lambda =
      aoyagiTheorem2Lambda_expanded L ell H r data.aParam data.ceilWidth
        (aoyagiSelectedReducedWidths H r C) := by
  simpa [B.selectedWidths_eq_reduced] using B.lambda_eq_theorem2Lambda_expanded

end AoyagiTheorem2SuppliedFinalBoundary

end Aoyagi
end DLN
end DLNFibre
