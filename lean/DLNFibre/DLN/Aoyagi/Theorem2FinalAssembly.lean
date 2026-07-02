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

/-- Chart-certificate version of the supplied final boundary.

This replaces the bare finite exponent array by a source-facing
normal-crossing chart certificate and projects its finite exponent data into
the existing final boundary.  The chart-level extraction hypothesis is still
the cited analytic boundary; this structure does not construct charts, prove
coverage, nonvanishing units, finite exponent formula equalities, or the
analytic extraction theorem. -/
structure AoyagiTheorem2SuppliedChartFinalBoundary
    {Param R : Type*} [CommMonoid R]
    (Cnc : AoyagiNormalCrossingChartCertificate Param R)
    (L ell : ℕ) (H : ℕ → ℕ) (r : ℕ)
    (C : AoyagiSelectedCutpoints ell) (m : Fin (ell + 1) → ℤ)
    (data : AoyagiDefinition3CeilData ell m)
    (lambda : ℚ) (poleOrder : ℕ) : Prop where
  selectedWidths_eq_reduced :
    m = aoyagiSelectedReducedWidths H r C
  extractionHypothesis :
    Cnc.ExtractionHypothesis lambda poleOrder
  finiteExponentFormula :
    AoyagiTheorem2FiniteExponentFormulaHypothesis
      Cnc.exponentData L ell H r m data

namespace AoyagiTheorem2SuppliedChartFinalBoundary

/-- Build the chart-certificate final boundary from explicit finite
normal-crossing min/order certificates.

This removes the opaque finite-formula field by consuming an active coordinate
realizing the displayed lambda formula, a global active-ratio lower bound, a
chart realizing the displayed order formula, and a uniform chart-count upper
bound.  It still assumes the chart-level extraction hypothesis as the cited A0
analytic boundary. -/
theorem of_activePair_ratioAt_eq_of_forall_le_of_chart_minCount_eq_of_forall_le
    {Param R : Type*} [CommMonoid R]
    {Cnc : AoyagiNormalCrossingChartCertificate Param R}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {cuts : AoyagiSelectedCutpoints ell} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m)
    {lambda : ℚ} {poleOrder : ℕ}
    (hselected : m = aoyagiSelectedReducedWidths H r cuts)
    (hNC : Cnc.ExtractionHypothesis lambda poleOrder)
    {p : Fin Cnc.numCharts × Fin Cnc.numCoords}
    (hp : p ∈ Cnc.exponentData.activePairs)
    (hratio :
      Cnc.exponentData.ratioAt p =
        aoyagiTheorem2Lambda_fromCeilData L ell H r m data)
    (hleRatio : ∀ p' ∈ Cnc.exponentData.activePairs,
      aoyagiTheorem2Lambda_fromCeilData L ell H r m data ≤
        Cnc.exponentData.ratioAt p')
    {c : Fin Cnc.numCharts}
    (hchart :
      Cnc.exponentData.minCountInChart c = data.theorem2OrderFormula)
    (hleChart : ∀ c' : Fin Cnc.numCharts,
      Cnc.exponentData.minCountInChart c' ≤ data.theorem2OrderFormula) :
    AoyagiTheorem2SuppliedChartFinalBoundary
      Cnc L ell H r cuts m data lambda poleOrder where
  selectedWidths_eq_reduced := hselected
  extractionHypothesis := hNC
  finiteExponentFormula :=
    show
        AoyagiTheorem2FiniteExponentFormulaHypothesis
          Cnc.exponentData L ell H r m data from
      .of_activePair_ratioAt_eq_of_forall_le_of_chart_minCount_eq_of_forall_le
        data hp hratio hleRatio hchart hleChart

/-- Build the chart-certificate final boundary from an active-ratio minimum
certificate and chart counts stated at the displayed candidate ratio.

The ratio-count hypotheses are converted to global-minimum chart counts only
after the active-ratio minimum certificate proves that the displayed ratio is
`Cnc.exponentData.exponentMinimum`. -/
theorem of_activePair_ratioAt_eq_of_forall_le_of_countInChartAtRatio_eq_of_forall_le
    {Param R : Type*} [CommMonoid R]
    {Cnc : AoyagiNormalCrossingChartCertificate Param R}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {cuts : AoyagiSelectedCutpoints ell} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m)
    {lambda : ℚ} {poleOrder : ℕ}
    (hselected : m = aoyagiSelectedReducedWidths H r cuts)
    (hNC : Cnc.ExtractionHypothesis lambda poleOrder)
    {p : Fin Cnc.numCharts × Fin Cnc.numCoords}
    (hp : p ∈ Cnc.exponentData.activePairs)
    (hratio :
      Cnc.exponentData.ratioAt p =
        aoyagiTheorem2Lambda_fromCeilData L ell H r m data)
    (hleRatio : ∀ p' ∈ Cnc.exponentData.activePairs,
      aoyagiTheorem2Lambda_fromCeilData L ell H r m data ≤
        Cnc.exponentData.ratioAt p')
    {c : Fin Cnc.numCharts}
    (hchart :
      Cnc.exponentData.countInChartAtRatio
        (aoyagiTheorem2Lambda_fromCeilData L ell H r m data) c =
          data.theorem2OrderFormula)
    (hleChart : ∀ c' : Fin Cnc.numCharts,
      Cnc.exponentData.countInChartAtRatio
          (aoyagiTheorem2Lambda_fromCeilData L ell H r m data) c' ≤
        data.theorem2OrderFormula) :
    AoyagiTheorem2SuppliedChartFinalBoundary
      Cnc L ell H r cuts m data lambda poleOrder where
  selectedWidths_eq_reduced := hselected
  extractionHypothesis := hNC
  finiteExponentFormula :=
    let hmin :
        Cnc.exponentData.exponentMinimum =
          aoyagiTheorem2Lambda_fromCeilData L ell H r m data :=
      Cnc.exponentData.exponentMinimum_eq_of_activePair_ratioAt_eq_of_forall_le
        hp hratio hleRatio
    { exponentMinimum_eq_theorem2Lambda_fromCeilData := hmin
      exponentOrder_eq_theorem2OrderFormula :=
        Cnc.exponentData.exponentOrder_eq_of_countInChartAtRatio_eq_of_forall_le
          hmin hchart hleChart }

/-- Forget the chart certificate down to its finite exponent data, recovering
the existing supplied final boundary. -/
theorem toSuppliedFinalBoundary
    {Param R : Type*} [CommMonoid R]
    {Cnc : AoyagiNormalCrossingChartCertificate Param R}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell} {m : Fin (ell + 1) → ℤ}
    {data : AoyagiDefinition3CeilData ell m} {lambda : ℚ} {poleOrder : ℕ}
    (B :
      AoyagiTheorem2SuppliedChartFinalBoundary
        Cnc L ell H r C m data lambda poleOrder) :
    AoyagiTheorem2SuppliedFinalBoundary
      Cnc.exponentData L ell H r C m data lambda poleOrder where
  selectedWidths_eq_reduced := B.selectedWidths_eq_reduced
  extractionHypothesis := B.extractionHypothesis.toExponentData
  finiteExponentFormula := B.finiteExponentFormula

/-- Chart-certificate final boundary, projected to the ceiling-data lambda
formula. -/
theorem lambda_eq_theorem2Lambda_fromCeilData
    {Param R : Type*} [CommMonoid R]
    {Cnc : AoyagiNormalCrossingChartCertificate Param R}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell} {m : Fin (ell + 1) → ℤ}
    {data : AoyagiDefinition3CeilData ell m} {lambda : ℚ} {poleOrder : ℕ}
    (B :
      AoyagiTheorem2SuppliedChartFinalBoundary
        Cnc L ell H r C m data lambda poleOrder) :
    lambda = aoyagiTheorem2Lambda_fromCeilData L ell H r m data :=
  B.toSuppliedFinalBoundary.lambda_eq_theorem2Lambda_fromCeilData

/-- Chart-certificate final boundary, projected to Aoyagi's order formula. -/
theorem poleOrder_eq_theorem2OrderFormula
    {Param R : Type*} [CommMonoid R]
    {Cnc : AoyagiNormalCrossingChartCertificate Param R}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell} {m : Fin (ell + 1) → ℤ}
    {data : AoyagiDefinition3CeilData ell m} {lambda : ℚ} {poleOrder : ℕ}
    (B :
      AoyagiTheorem2SuppliedChartFinalBoundary
        Cnc L ell H r C m data lambda poleOrder) :
    poleOrder = data.theorem2OrderFormula :=
  B.toSuppliedFinalBoundary.poleOrder_eq_theorem2OrderFormula

/-- Pair form of the chart-certificate final boundary. -/
theorem lambda_and_poleOrder_eq_fromCeilData_and_orderFormula
    {Param R : Type*} [CommMonoid R]
    {Cnc : AoyagiNormalCrossingChartCertificate Param R}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell} {m : Fin (ell + 1) → ℤ}
    {data : AoyagiDefinition3CeilData ell m} {lambda : ℚ} {poleOrder : ℕ}
    (B :
      AoyagiTheorem2SuppliedChartFinalBoundary
        Cnc L ell H r C m data lambda poleOrder) :
    lambda = aoyagiTheorem2Lambda_fromCeilData L ell H r m data ∧
      poleOrder = data.theorem2OrderFormula :=
  B.toSuppliedFinalBoundary.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula

/-- Direct pair form after supplying chart-level extraction plus finite
active-ratio and chart-count certificates. -/
theorem lambda_and_poleOrder_eq_fromCeilData_and_orderFormula_of_activePair_chartCount
    {Param R : Type*} [CommMonoid R]
    {Cnc : AoyagiNormalCrossingChartCertificate Param R}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {cuts : AoyagiSelectedCutpoints ell} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m)
    {lambda : ℚ} {poleOrder : ℕ}
    (hselected : m = aoyagiSelectedReducedWidths H r cuts)
    (hNC : Cnc.ExtractionHypothesis lambda poleOrder)
    {p : Fin Cnc.numCharts × Fin Cnc.numCoords}
    (hp : p ∈ Cnc.exponentData.activePairs)
    (hratio :
      Cnc.exponentData.ratioAt p =
        aoyagiTheorem2Lambda_fromCeilData L ell H r m data)
    (hleRatio : ∀ p' ∈ Cnc.exponentData.activePairs,
      aoyagiTheorem2Lambda_fromCeilData L ell H r m data ≤
        Cnc.exponentData.ratioAt p')
    {c : Fin Cnc.numCharts}
    (hchart :
      Cnc.exponentData.minCountInChart c = data.theorem2OrderFormula)
    (hleChart : ∀ c' : Fin Cnc.numCharts,
      Cnc.exponentData.minCountInChart c' ≤ data.theorem2OrderFormula) :
    lambda = aoyagiTheorem2Lambda_fromCeilData L ell H r m data ∧
      poleOrder = data.theorem2OrderFormula := by
  let B :
      AoyagiTheorem2SuppliedChartFinalBoundary
        Cnc L ell H r cuts m data lambda poleOrder :=
    of_activePair_ratioAt_eq_of_forall_le_of_chart_minCount_eq_of_forall_le
      data hselected hNC hp hratio hleRatio hchart hleChart
  exact B.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula

/-- Direct pair form when chart counts are supplied at the displayed candidate
ratio rather than as global-minimum chart counts. -/
theorem lambda_and_poleOrder_eq_fromCeilData_and_orderFormula_of_activePair_ratioCount
    {Param R : Type*} [CommMonoid R]
    {Cnc : AoyagiNormalCrossingChartCertificate Param R}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {cuts : AoyagiSelectedCutpoints ell} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m)
    {lambda : ℚ} {poleOrder : ℕ}
    (hselected : m = aoyagiSelectedReducedWidths H r cuts)
    (hNC : Cnc.ExtractionHypothesis lambda poleOrder)
    {p : Fin Cnc.numCharts × Fin Cnc.numCoords}
    (hp : p ∈ Cnc.exponentData.activePairs)
    (hratio :
      Cnc.exponentData.ratioAt p =
        aoyagiTheorem2Lambda_fromCeilData L ell H r m data)
    (hleRatio : ∀ p' ∈ Cnc.exponentData.activePairs,
      aoyagiTheorem2Lambda_fromCeilData L ell H r m data ≤
        Cnc.exponentData.ratioAt p')
    {c : Fin Cnc.numCharts}
    (hchart :
      Cnc.exponentData.countInChartAtRatio
        (aoyagiTheorem2Lambda_fromCeilData L ell H r m data) c =
          data.theorem2OrderFormula)
    (hleChart : ∀ c' : Fin Cnc.numCharts,
      Cnc.exponentData.countInChartAtRatio
          (aoyagiTheorem2Lambda_fromCeilData L ell H r m data) c' ≤
        data.theorem2OrderFormula) :
    lambda = aoyagiTheorem2Lambda_fromCeilData L ell H r m data ∧
      poleOrder = data.theorem2OrderFormula := by
  let B :
      AoyagiTheorem2SuppliedChartFinalBoundary
        Cnc L ell H r cuts m data lambda poleOrder :=
    of_activePair_ratioAt_eq_of_forall_le_of_countInChartAtRatio_eq_of_forall_le
      data hselected hNC hp hratio hleRatio hchart hleChart
  exact B.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula

end AoyagiTheorem2SuppliedChartFinalBoundary

namespace AoyagiDefinition3SourceData

/-- Definition 3 source data plus source-range rank-width hypotheses produce
the selected-width family and ceiling datum needed by the supplied final
Theorem 2 boundary.

This removes a bare selected-width provenance input from the final socket, but
the selected cutpoints, source data, rank-width hypothesis, A0 extraction
hypothesis, and finite exponent formula hypothesis all remain supplied. -/
theorem exists_theorem2SuppliedFinalBoundary_of_rankWidth
    {D : AoyagiNormalCrossingExponentData}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell}
    (S : AoyagiDefinition3SourceData L ell H r C)
    (hr : ∀ s : ℕ, 1 ≤ s → s ≤ L + 1 → r ≤ H s)
    {lambda : ℚ} {poleOrder : ℕ}
    (hNC : AoyagiNormalCrossingExtractionHypothesis D lambda poleOrder)
    (hFormula :
      ∀ {m : Fin (ell + 1) → ℤ}
        (data : AoyagiDefinition3CeilData ell m),
        m = aoyagiSelectedReducedWidths H r C →
        AoyagiTheorem2FiniteExponentFormulaHypothesis D L ell H r m data) :
    ∃ (m : Fin (ell + 1) → ℤ) (data : AoyagiDefinition3CeilData ell m),
      AoyagiTheorem2SuppliedFinalBoundary
          D L ell H r C m data lambda poleOrder ∧
      (∀ j : Fin (ell + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (ell + 1), 0 ≤ m j) ∧
      (∀ i : Fin (ell + 1),
        (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j) ∧
      (∀ i : Fin (ell + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat ell m i) := by
  rcases S.exists_selectedReducedWidthCeilData_of_rankWidth hr with
    ⟨m, data, hm, hnat, hnonneg, hstrict, hupper, hNatNonneg⟩
  refine ⟨m, data, ?_, hnat, hnonneg, hstrict, hupper, hNatNonneg⟩
  exact
    { selectedWidths_eq_reduced := hm
      extractionHypothesis := hNC
      finiteExponentFormula := hFormula data hm }

/-- `L=2` source data removes the separate source-range rank-width input from
the supplied final-boundary socket.

The finite exponent formula and A0 extraction hypotheses remain supplied, and
the selected cutpoints are still the supplied `C`; this theorem only supplies
rank-width from the finite `L=2` Definition 3 classification. -/
theorem exists_theorem2SuppliedFinalBoundary_of_L_eq_two_sourceData
    {D : AoyagiNormalCrossingExponentData}
    {ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell}
    (S : AoyagiDefinition3SourceData 2 ell H r C)
    {lambda : ℚ} {poleOrder : ℕ}
    (hNC : AoyagiNormalCrossingExtractionHypothesis D lambda poleOrder)
    (hFormula :
      ∀ {m : Fin (ell + 1) → ℤ}
        (data : AoyagiDefinition3CeilData ell m),
        m = aoyagiSelectedReducedWidths H r C →
        AoyagiTheorem2FiniteExponentFormulaHypothesis D 2 ell H r m data) :
    ∃ (m : Fin (ell + 1) → ℤ) (data : AoyagiDefinition3CeilData ell m),
      AoyagiTheorem2SuppliedFinalBoundary
          D 2 ell H r C m data lambda poleOrder ∧
      (∀ j : Fin (ell + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (ell + 1), 0 ≤ m j) ∧
      (∀ i : Fin (ell + 1),
        (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j) ∧
      (∀ i : Fin (ell + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat ell m i) :=
  S.exists_theorem2SuppliedFinalBoundary_of_rankWidth
    S.sourceRangeRankWidth_of_L_eq_two_sourceData hNC hFormula

/-- `ell=1` source data removes the separate source-range rank-width input
from the supplied final-boundary socket.

The branch `ell=1` and selected cutpoints remain supplied.  The finite exponent
formula and A0 extraction hypotheses remain supplied. -/
theorem exists_theorem2SuppliedFinalBoundary_of_ell_eq_one_sourceData
    {D : AoyagiNormalCrossingExponentData}
    {L : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints 1}
    (S : AoyagiDefinition3SourceData L 1 H r C)
    {lambda : ℚ} {poleOrder : ℕ}
    (hNC : AoyagiNormalCrossingExtractionHypothesis D lambda poleOrder)
    (hFormula :
      ∀ {m : Fin (1 + 1) → ℤ}
        (data : AoyagiDefinition3CeilData 1 m),
        m = aoyagiSelectedReducedWidths H r C →
        AoyagiTheorem2FiniteExponentFormulaHypothesis D L 1 H r m data) :
    ∃ (m : Fin (1 + 1) → ℤ) (data : AoyagiDefinition3CeilData 1 m),
      AoyagiTheorem2SuppliedFinalBoundary
          D L 1 H r C m data lambda poleOrder ∧
      (∀ j : Fin (1 + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (1 + 1), 0 ≤ m j) ∧
      (∀ i : Fin (1 + 1),
        (1 : ℤ) * m i < ∑ j : Fin (1 + 1), m j) ∧
      (∀ i : Fin (1 + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat 1 m i) :=
  S.exists_theorem2SuppliedFinalBoundary_of_rankWidth
    S.sourceRangeRankWidth_of_ell_eq_one hNC hFormula

/-- Chart-certificate version of
`exists_theorem2SuppliedFinalBoundary_of_rankWidth`.

The chart certificate and its extraction hypothesis remain supplied.  This
only packages the Definition 3 source-selected family and ceiling datum before
calling a supplied finite exponent formula hypothesis for that produced data. -/
theorem exists_theorem2SuppliedChartFinalBoundary_of_rankWidth
    {Param R : Type*} [CommMonoid R]
    {Cnc : AoyagiNormalCrossingChartCertificate Param R}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell}
    (S : AoyagiDefinition3SourceData L ell H r C)
    (hr : ∀ s : ℕ, 1 ≤ s → s ≤ L + 1 → r ≤ H s)
    {lambda : ℚ} {poleOrder : ℕ}
    (hNC : Cnc.ExtractionHypothesis lambda poleOrder)
    (hFormula :
      ∀ {m : Fin (ell + 1) → ℤ}
        (data : AoyagiDefinition3CeilData ell m),
        m = aoyagiSelectedReducedWidths H r C →
        AoyagiTheorem2FiniteExponentFormulaHypothesis
          Cnc.exponentData L ell H r m data) :
    ∃ (m : Fin (ell + 1) → ℤ) (data : AoyagiDefinition3CeilData ell m),
      AoyagiTheorem2SuppliedChartFinalBoundary
          Cnc L ell H r C m data lambda poleOrder ∧
      (∀ j : Fin (ell + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (ell + 1), 0 ≤ m j) ∧
      (∀ i : Fin (ell + 1),
        (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j) ∧
      (∀ i : Fin (ell + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat ell m i) := by
  rcases S.exists_selectedReducedWidthCeilData_of_rankWidth hr with
    ⟨m, data, hm, hnat, hnonneg, hstrict, hupper, hNatNonneg⟩
  refine ⟨m, data, ?_, hnat, hnonneg, hstrict, hupper, hNatNonneg⟩
  exact
    { selectedWidths_eq_reduced := hm
      extractionHypothesis := hNC
      finiteExponentFormula := hFormula data hm }

/-- Chart-certificate version of
`exists_theorem2SuppliedFinalBoundary_of_L_eq_two_sourceData`. -/
theorem exists_theorem2SuppliedChartFinalBoundary_of_L_eq_two_sourceData
    {Param R : Type*} [CommMonoid R]
    {Cnc : AoyagiNormalCrossingChartCertificate Param R}
    {ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell}
    (S : AoyagiDefinition3SourceData 2 ell H r C)
    {lambda : ℚ} {poleOrder : ℕ}
    (hNC : Cnc.ExtractionHypothesis lambda poleOrder)
    (hFormula :
      ∀ {m : Fin (ell + 1) → ℤ}
        (data : AoyagiDefinition3CeilData ell m),
        m = aoyagiSelectedReducedWidths H r C →
        AoyagiTheorem2FiniteExponentFormulaHypothesis
          Cnc.exponentData 2 ell H r m data) :
    ∃ (m : Fin (ell + 1) → ℤ) (data : AoyagiDefinition3CeilData ell m),
      AoyagiTheorem2SuppliedChartFinalBoundary
          Cnc 2 ell H r C m data lambda poleOrder ∧
      (∀ j : Fin (ell + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (ell + 1), 0 ≤ m j) ∧
      (∀ i : Fin (ell + 1),
        (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j) ∧
      (∀ i : Fin (ell + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat ell m i) :=
  S.exists_theorem2SuppliedChartFinalBoundary_of_rankWidth
    S.sourceRangeRankWidth_of_L_eq_two_sourceData hNC hFormula

/-- Chart-certificate version of
`exists_theorem2SuppliedFinalBoundary_of_ell_eq_one_sourceData`. -/
theorem exists_theorem2SuppliedChartFinalBoundary_of_ell_eq_one_sourceData
    {Param R : Type*} [CommMonoid R]
    {Cnc : AoyagiNormalCrossingChartCertificate Param R}
    {L : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints 1}
    (S : AoyagiDefinition3SourceData L 1 H r C)
    {lambda : ℚ} {poleOrder : ℕ}
    (hNC : Cnc.ExtractionHypothesis lambda poleOrder)
    (hFormula :
      ∀ {m : Fin (1 + 1) → ℤ}
        (data : AoyagiDefinition3CeilData 1 m),
        m = aoyagiSelectedReducedWidths H r C →
        AoyagiTheorem2FiniteExponentFormulaHypothesis
          Cnc.exponentData L 1 H r m data) :
    ∃ (m : Fin (1 + 1) → ℤ) (data : AoyagiDefinition3CeilData 1 m),
      AoyagiTheorem2SuppliedChartFinalBoundary
          Cnc L 1 H r C m data lambda poleOrder ∧
      (∀ j : Fin (1 + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (1 + 1), 0 ≤ m j) ∧
      (∀ i : Fin (1 + 1),
        (1 : ℤ) * m i < ∑ j : Fin (1 + 1), m j) ∧
      (∀ i : Fin (1 + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat 1 m i) :=
  S.exists_theorem2SuppliedChartFinalBoundary_of_rankWidth
    S.sourceRangeRankWidth_of_ell_eq_one hNC hFormula

end AoyagiDefinition3SourceData

end Aoyagi
end DLN
end DLNFibre
