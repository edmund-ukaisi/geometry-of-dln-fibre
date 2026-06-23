import DLNFibre.DLN.Aoyagi.Lemma5Eq5TerminalOrderBridge
import DLNFibre.DLN.Aoyagi.Theorem2TerminalOrderEqualityBridge

/-!
# Theorem 2 Eq5 terminal-order bridge

This file packages the large supplied Eq5 endpoint-family payload and routes
its exact terminal-count consequence into the existing Theorem 2 exact-count
sockets.  It is only an A5-to-A6 finite handoff: Eq5 source-family
construction, global chart production, active-ratio lower bounds,
displayed-ratio chart counts, and analytic extraction remain explicit
hypotheses.
-/

open scoped BigOperators

namespace DLNFibre
namespace DLN
namespace Aoyagi

open AoyagiLemma5SuppliedNonbaseFamily

set_option linter.style.longLine false

/-- Payload form of the supplied Eq5 endpoint-family block-width cardinal
squeeze.

The fields are exactly the data consumed by
`terminalMinimumLabels_card_eq_theorem2OrderFormula_of_eq5EndpointFamily_branchCoordVal_blockWidth_cardSqueeze`.
This structure only makes the A6 handoff readable; it does not construct the
Eq5 family or prove source-backed Lemma 5 exactness. -/
structure AoyagiLemma5SuppliedEq5EndpointBlockWidthOrderPayload
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N : ℕ} {m : Fin (N + 2) → ℤ}
    (data : AoyagiDefinition3CeilData (N + 1) m)
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N data.aParam data.ceilWidth m t numerator leastValue) where
  cut : AoyagiSelectedCutpoints (N + 1)
  pOf : (Σ _ : ℕ, ℕ) → ℕ
  labelAlphaOf : (Σ _ : ℕ, ℕ) → ℕ
  layerWidth : (Σ _ : ℕ, ℕ) → ℕ → ℤ
  T : (Σ _ : ℕ, ℕ) → ℕ → ℤ
  strictBranches : ℕ → Finset β
  alphaOf : β → ℕ
  value : β → ℤ
  upper : ℕ → β
  lower : ℕ → β
  baseValue : ℕ → ℤ
  hsource : ∀ i : Fin (N + 2),
    ((N + 1 : ℕ) : ℤ) * m i < ∑ j : Fin (N + 2), m j
  hT : ∀ label ∈ TC.terminalMinimumLabels,
    AoyagiLemma5Eq5PiecewiseSourceVector
      (N + 1) data.aParam (pOf label) (labelAlphaOf label)
      data.ceilWidth m cut (layerWidth label) (T label)
  hlabelBlock : ∀ label ∈ TC.terminalMinimumLabels,
    cut.block (pOf label) label.1
  hlast : cut.point (N + 1) ≤ L + 1
  hactual :
    ∀ i : Fin (N + 1), ∀ r : ℕ,
      cut.point i.val ≤ r → r < cut.point (i.val + 1) →
        aoyagiSelectedWidthNat (N + 1) m i.val ≤ (width r : ℤ)
  hlabelFormula : ∀ label ∈ TC.terminalMinimumLabels,
    (label.2 : ℤ) =
      aoyagiHtildeUpperNat (N + 1) data.aParam data.ceilWidth m
          (pOf label) + 1 -
        (labelAlphaOf label : ℤ)
  hlabel_ne_base : ∀ label ∈ TC.terminalMinimumLabels,
    T label label.1 ≠ TC.family.baseValue (pOf label)
  hpAlpha_inj :
    Set.InjOn
      (fun label : Σ _ : ℕ, ℕ ↦
        (Sigma.mk (pOf label) (labelAlphaOf label) : Σ _ : ℕ, ℕ))
      ↑TC.terminalMinimumLabels
  baseValue_mem :
    ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) →
      baseValue j ∈
        aoyagiHtildeIntervalValueSetNat
          (N + 1) data.aParam data.ceilWidth m j
  halpha_image :
    ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) →
      (strictBranches j).image alphaOf =
        aoyagiLemma5Eq5AlphaDomain (N + 1) data.aParam j
  hvalue :
    ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 ((N + 1) - 1)) →
      ∀ b ∈ strictBranches j,
        value b =
          aoyagiHtildeUpperNat (N + 1) data.aParam data.ceilWidth m j -
            (alphaOf b : ℤ)
  hupper :
    ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) →
      value (upper j) =
        aoyagiHtildeUpperNat (N + 1) data.aParam data.ceilWidth m j
  hlower :
    ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) → j ≤ data.aParam →
      j ≤ (N + 1) - data.aParam →
        value (lower j) =
          aoyagiHtildeLowerNat (N + 1) data.aParam data.ceilWidth m j
  halpha_inj :
    ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 ((N + 1) - 1)) →
      Set.InjOn alphaOf ↑(strictBranches j)
  branchCoord : β → ℕ
  hstrictCoord :
    ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 ((N + 1) - 1)) →
      ∀ b ∈ strictBranches j, branchCoord b = j
  hupperCoord :
    ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) →
      branchCoord (upper j) = j
  hlowerCoord :
    ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) → j ≤ data.aParam →
      j ≤ (N + 1) - data.aParam → branchCoord (lower j) = j
  hfamily :
    TC.family.toAoyagiLemma5SuppliedNonbaseFamily =
      ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord
        (ell := N + 1) (a := data.aParam) (M := data.ceilWidth) (m := m)
        strictBranches alphaOf value upper lower baseValue data.aParam_le
        baseValue_mem halpha_image hvalue hupper hlower halpha_inj
        branchCoord hstrictCoord hupperCoord hlowerCoord
  hbranchS :
    ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
      TC.branchS (some b) = cut.point (branchCoord b) - 1
  hbranchK :
    ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
      TC.family.value b = (TC.branchK (some b) : ℤ) - 1
  hbaseLabel :
    TC.branchLabel none =
      ((Sigma.mk (cut.point (N + 1) - 1) 1) : Σ _ : ℕ, ℕ)

namespace AoyagiLemma5SuppliedEq5EndpointBlockWidthOrderPayload

/-- Extract the exact Theorem 2 terminal order count from the supplied Eq5
endpoint block-width payload. -/
theorem terminalMinimumLabels_card_eq_theorem2OrderFormula
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N : ℕ} {m : Fin (N + 2) → ℤ}
    {data : AoyagiDefinition3CeilData (N + 1) m}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    {TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N data.aParam data.ceilWidth m t numerator leastValue}
    (P : AoyagiLemma5SuppliedEq5EndpointBlockWidthOrderPayload data TC) :
    TC.terminalMinimumLabels.card = data.theorem2OrderFormula :=
  TC.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_eq5EndpointFamily_branchCoordVal_blockWidth_cardSqueeze
    data P.cut P.pOf P.labelAlphaOf P.layerWidth P.T P.strictBranches
    P.alphaOf P.value P.upper P.lower P.baseValue P.hsource P.hT
    P.hlabelBlock P.hlast P.hactual P.hlabelFormula P.hlabel_ne_base
    P.hpAlpha_inj P.baseValue_mem P.halpha_image P.hvalue P.hupper
    P.hlower P.halpha_inj P.branchCoord P.hstrictCoord P.hupperCoord
    P.hlowerCoord P.hfamily P.hbranchS P.hbranchK P.hbaseLabel

end AoyagiLemma5SuppliedEq5EndpointBlockWidthOrderPayload

namespace AoyagiLemma5SuppliedTerminalCandidateFamily

/-- Finite exponent formula boundary from active-ratio and displayed-ratio
chart-count certificates, with the exact terminal count supplied by an Eq5
endpoint block-width payload. -/
theorem
  theorem2FiniteExponentFormulaHypothesis_of_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload
    {β : Type*} [DecidableEq β]
    {D : AoyagiNormalCrossingExponentData}
    {L : ℕ} {width : ℕ → ℕ} {S J n : ℕ}
    {H : ℕ → ℕ} {r : ℕ}
    {m : Fin (n + 2) → ℤ}
    (data : AoyagiDefinition3CeilData (n + 1) m)
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC :
      AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J
        n data.aParam data.ceilWidth m t numerator leastValue)
    (P : AoyagiLemma5SuppliedEq5EndpointBlockWidthOrderPayload data TC)
    {p : Fin D.numCharts × Fin D.numCoords}
    (hp : p ∈ D.activePairs)
    (hratio :
      D.ratioAt p =
        aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data)
    (hleRatio : ∀ p' ∈ D.activePairs,
      aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data ≤
        D.ratioAt p')
    {c : Fin D.numCharts}
    (hchart :
      D.countInChartAtRatio
          (aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data) c =
        TC.terminalMinimumLabels.card)
    (hleChart : ∀ c' : Fin D.numCharts,
      D.countInChartAtRatio
          (aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data) c' ≤
        TC.terminalMinimumLabels.card) :
    AoyagiTheorem2FiniteExponentFormulaHypothesis D L (n + 1) H r m data :=
  TC.theorem2FiniteExponentFormulaHypothesis_of_activePair_ratioCount_terminalMinimumLabels_card_eq
    data hp hratio hleRatio hchart hleChart
    P.terminalMinimumLabels_card_eq_theorem2OrderFormula

/-- Supplied final boundary from active-ratio and displayed-ratio chart-count
certificates, with the exact terminal count supplied by an Eq5 endpoint
block-width payload. -/
theorem theorem2SuppliedFinalBoundary_of_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload
    {β : Type*} [DecidableEq β]
    {D : AoyagiNormalCrossingExponentData}
    {L : ℕ} {width : ℕ → ℕ} {S J n : ℕ}
    {H : ℕ → ℕ} {r : ℕ}
    {m : Fin (n + 2) → ℤ}
    (data : AoyagiDefinition3CeilData (n + 1) m)
    {lambda : ℚ} {poleOrder : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC :
      AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J
        n data.aParam data.ceilWidth m t numerator leastValue)
    (P : AoyagiLemma5SuppliedEq5EndpointBlockWidthOrderPayload data TC)
    (hselected : m = aoyagiSelectedReducedWidths H r P.cut)
    (hNC : AoyagiNormalCrossingExtractionHypothesis D lambda poleOrder)
    {p : Fin D.numCharts × Fin D.numCoords}
    (hp : p ∈ D.activePairs)
    (hratio :
      D.ratioAt p =
        aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data)
    (hleRatio : ∀ p' ∈ D.activePairs,
      aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data ≤
        D.ratioAt p')
    {c : Fin D.numCharts}
    (hchart :
      D.countInChartAtRatio
          (aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data) c =
        TC.terminalMinimumLabels.card)
    (hleChart : ∀ c' : Fin D.numCharts,
      D.countInChartAtRatio
          (aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data) c' ≤
        TC.terminalMinimumLabels.card) :
    AoyagiTheorem2SuppliedFinalBoundary D L (n + 1) H r P.cut m data
      lambda poleOrder :=
  TC.theorem2SuppliedFinalBoundary_of_activePair_ratioCount_terminalMinimumLabels_card_eq
    data hselected hNC hp hratio hleRatio hchart hleChart
    P.terminalMinimumLabels_card_eq_theorem2OrderFormula

/-- Chart-certificate final boundary from active-ratio and displayed-ratio
chart-count certificates, with the exact terminal count supplied by an Eq5
endpoint block-width payload. -/
theorem
  theorem2SuppliedChartFinalBoundary_of_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload
    {Param R : Type*} [CommMonoid R]
    {β : Type*} [DecidableEq β]
    {Cnc : AoyagiNormalCrossingChartCertificate Param R}
    {L : ℕ} {width : ℕ → ℕ} {S J n : ℕ}
    {H : ℕ → ℕ} {r : ℕ}
    {m : Fin (n + 2) → ℤ}
    (data : AoyagiDefinition3CeilData (n + 1) m)
    {lambda : ℚ} {poleOrder : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC :
      AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J
        n data.aParam data.ceilWidth m t numerator leastValue)
    (P : AoyagiLemma5SuppliedEq5EndpointBlockWidthOrderPayload data TC)
    (hselected : m = aoyagiSelectedReducedWidths H r P.cut)
    (hNC : Cnc.ExtractionHypothesis lambda poleOrder)
    {p : Fin Cnc.numCharts × Fin Cnc.numCoords}
    (hp : p ∈ Cnc.exponentData.activePairs)
    (hratio :
      Cnc.exponentData.ratioAt p =
        aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data)
    (hleRatio : ∀ p' ∈ Cnc.exponentData.activePairs,
      aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data ≤
        Cnc.exponentData.ratioAt p')
    {c : Fin Cnc.numCharts}
    (hchart :
      Cnc.exponentData.countInChartAtRatio
          (aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data) c =
        TC.terminalMinimumLabels.card)
    (hleChart : ∀ c' : Fin Cnc.numCharts,
      Cnc.exponentData.countInChartAtRatio
          (aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data) c' ≤
        TC.terminalMinimumLabels.card) :
    AoyagiTheorem2SuppliedChartFinalBoundary
      Cnc L (n + 1) H r P.cut m data lambda poleOrder :=
  TC.theorem2SuppliedChartFinalBoundary_of_activePair_ratioCount_terminalMinimumLabels_card_eq
    data hselected hNC hp hratio hleRatio hchart hleChart
    P.terminalMinimumLabels_card_eq_theorem2OrderFormula

/-- Pair-form chart-certificate consequence from active-ratio and
displayed-ratio chart-count certificates, with the exact terminal count
supplied by an Eq5 endpoint block-width payload. -/
theorem
  lambda_and_poleOrder_eq_of_chart_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload
    {Param R : Type*} [CommMonoid R]
    {β : Type*} [DecidableEq β]
    {Cnc : AoyagiNormalCrossingChartCertificate Param R}
    {L : ℕ} {width : ℕ → ℕ} {S J n : ℕ}
    {H : ℕ → ℕ} {r : ℕ}
    {m : Fin (n + 2) → ℤ}
    (data : AoyagiDefinition3CeilData (n + 1) m)
    {lambda : ℚ} {poleOrder : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC :
      AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J
        n data.aParam data.ceilWidth m t numerator leastValue)
    (P : AoyagiLemma5SuppliedEq5EndpointBlockWidthOrderPayload data TC)
    (hselected : m = aoyagiSelectedReducedWidths H r P.cut)
    (hNC : Cnc.ExtractionHypothesis lambda poleOrder)
    {p : Fin Cnc.numCharts × Fin Cnc.numCoords}
    (hp : p ∈ Cnc.exponentData.activePairs)
    (hratio :
      Cnc.exponentData.ratioAt p =
        aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data)
    (hleRatio : ∀ p' ∈ Cnc.exponentData.activePairs,
      aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data ≤
        Cnc.exponentData.ratioAt p')
    {c : Fin Cnc.numCharts}
    (hchart :
      Cnc.exponentData.countInChartAtRatio
          (aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data) c =
        TC.terminalMinimumLabels.card)
    (hleChart : ∀ c' : Fin Cnc.numCharts,
      Cnc.exponentData.countInChartAtRatio
          (aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data) c' ≤
        TC.terminalMinimumLabels.card) :
    lambda = aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data ∧
      poleOrder = data.theorem2OrderFormula := by
  let B :
      AoyagiTheorem2SuppliedChartFinalBoundary
        Cnc L (n + 1) H r P.cut m data lambda poleOrder :=
    TC.theorem2SuppliedChartFinalBoundary_of_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload
      data P hselected hNC hp hratio hleRatio hchart hleChart
  exact B.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula

end AoyagiLemma5SuppliedTerminalCandidateFamily

end Aoyagi
end DLN
end DLNFibre
