import DLNFibre.DLN.Aoyagi.RegularSuspensionInterface

/-!
# Theorem 2 final handoff through the supplied regular-suspension boundary

This file composes Definition 3 source-data provenance with the supplied
regular-suspension full-chart boundary.  The output final socket is for the
actual supplied full certificate `Cfull`, and the extraction hypothesis is
therefore also for `Cfull`.

It does not construct the full chart certificate, prove the abstract
source/ideal/coverage/Jacobian predicates, prove analytic ideal transport,
prove Aoyagi Lemma 1, prove regular-coordinate additivity, construct
normal-crossing charts, prove active-ratio or chart-count facts, or prove
pole order/RLCT beyond the explicitly supplied full-chart extraction
hypothesis.
-/

noncomputable section

namespace DLNFibre
namespace DLN
namespace Aoyagi

set_option linter.style.longLine false

universe uRed uFull u v

namespace AoyagiDefinition3SourceData

/-- Definition 3 source data plus source-range rank-width hypotheses produce
the chart-final Theorem 2 socket for a supplied full regular-suspension
certificate.

The rank-width hypothesis is used both for selected-width side facts and for
the endpoint bounds in the finite regular-variable shift.  The reduced finite
minimum/order obligations remain supplied, and extraction is required only for
the supplied full chart certificate carried by `Sreg`. -/
theorem exists_theorem2SuppliedChartFinalBoundary_of_rankWidth_suppliedRegularSuspension
    {ParamRed RRed ParamFull RFull : Type*}
    [CommMonoid RRed] [CommMonoid RFull]
    {Cred : AoyagiNormalCrossingChartCertificate.{uRed} ParamRed RRed}
    {Cfull : AoyagiNormalCrossingChartCertificate.{uFull} ParamFull RFull}
    {regularCount : ℕ}
    {RegularChartSource RegularIdealTransport RegularCoverage
      RegularJacobianCompatible :
        AoyagiNormalCrossingChartCertificate.{uRed} ParamRed RRed →
          AoyagiNormalCrossingChartCertificate.{uFull} ParamFull RFull →
            ℕ → Prop}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell}
    (S : AoyagiDefinition3SourceData L ell H r C)
    (hr : ∀ s : ℕ, 1 ≤ s → s ≤ L + 1 → r ≤ H s)
    {lambda : ℚ} {poleOrder : ℕ}
    (Sreg : AoyagiSuppliedRegularSuspensionCertificate
      Cred Cfull regularCount RegularChartSource RegularIdealTransport
      RegularCoverage RegularJacobianCompatible lambda poleOrder)
    (hcount :
      regularCount = aoyagiTheorem2RegularVariableCount L H r)
    (hminimum :
      ∀ {m : Fin (ell + 1) → ℤ}
        (data : AoyagiDefinition3CeilData ell m),
        m = aoyagiSelectedReducedWidths H r C →
          Cred.exponentData.exponentMinimum + aoyagiTheorem2RegularTerm L H r =
            aoyagiTheorem2Lambda_fromCeilData L ell H r m data)
    (horder :
      ∀ {m : Fin (ell + 1) → ℤ}
        (data : AoyagiDefinition3CeilData ell m),
        m = aoyagiSelectedReducedWidths H r C →
          Cred.exponentData.exponentOrder = data.theorem2OrderFormula) :
    ∃ (m : Fin (ell + 1) → ℤ) (data : AoyagiDefinition3CeilData ell m),
      AoyagiTheorem2SuppliedChartFinalBoundary
          Cfull L ell H r C m data lambda poleOrder ∧
      (∀ j : Fin (ell + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (ell + 1), 0 ≤ m j) ∧
      (∀ i : Fin (ell + 1),
        (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j) ∧
      (∀ i : Fin (ell + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat ell m i) := by
  rcases sourceRangeRankWidth_regularVariableEndpointBounds hr with
    ⟨hsource, htarget⟩
  exact
    S.exists_theorem2SuppliedChartFinalBoundary_of_rankWidth hr
      Sreg.extractionHypothesis
      (fun data hselected ↦
        Sreg.boundary.theorem2FiniteExponentFormulaHypothesis_of_regularVariableCount
          data hcount hsource htarget
          (hminimum data hselected) (horder data hselected))

/-- `L=2` source data removes the separate source-range rank-width input from
the supplied regular-suspension chart-final handoff.

The supplied full chart certificate, count equality, and reduced finite
minimum/order obligations remain explicit. -/
theorem exists_theorem2SuppliedChartFinalBoundary_of_L_eq_two_sourceData_suppliedRegularSuspension
    {ParamRed RRed ParamFull RFull : Type*}
    [CommMonoid RRed] [CommMonoid RFull]
    {Cred : AoyagiNormalCrossingChartCertificate.{uRed} ParamRed RRed}
    {Cfull : AoyagiNormalCrossingChartCertificate.{uFull} ParamFull RFull}
    {regularCount : ℕ}
    {RegularChartSource RegularIdealTransport RegularCoverage
      RegularJacobianCompatible :
        AoyagiNormalCrossingChartCertificate.{uRed} ParamRed RRed →
          AoyagiNormalCrossingChartCertificate.{uFull} ParamFull RFull →
            ℕ → Prop}
    {ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell}
    (S : AoyagiDefinition3SourceData 2 ell H r C)
    {lambda : ℚ} {poleOrder : ℕ}
    (Sreg : AoyagiSuppliedRegularSuspensionCertificate
      Cred Cfull regularCount RegularChartSource RegularIdealTransport
      RegularCoverage RegularJacobianCompatible lambda poleOrder)
    (hcount :
      regularCount = aoyagiTheorem2RegularVariableCount 2 H r)
    (hminimum :
      ∀ {m : Fin (ell + 1) → ℤ}
        (data : AoyagiDefinition3CeilData ell m),
        m = aoyagiSelectedReducedWidths H r C →
          Cred.exponentData.exponentMinimum + aoyagiTheorem2RegularTerm 2 H r =
            aoyagiTheorem2Lambda_fromCeilData 2 ell H r m data)
    (horder :
      ∀ {m : Fin (ell + 1) → ℤ}
        (data : AoyagiDefinition3CeilData ell m),
        m = aoyagiSelectedReducedWidths H r C →
          Cred.exponentData.exponentOrder = data.theorem2OrderFormula) :
    ∃ (m : Fin (ell + 1) → ℤ) (data : AoyagiDefinition3CeilData ell m),
      AoyagiTheorem2SuppliedChartFinalBoundary
          Cfull 2 ell H r C m data lambda poleOrder ∧
      (∀ j : Fin (ell + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (ell + 1), 0 ≤ m j) ∧
      (∀ i : Fin (ell + 1),
        (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j) ∧
      (∀ i : Fin (ell + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat ell m i) :=
  S.exists_theorem2SuppliedChartFinalBoundary_of_rankWidth_suppliedRegularSuspension
    S.sourceRangeRankWidth_of_L_eq_two_sourceData Sreg hcount hminimum horder

/-- `ell=1` source data removes the separate source-range rank-width input
from the supplied regular-suspension chart-final handoff.

The supplied full chart certificate, count equality, and reduced finite
minimum/order obligations remain explicit. -/
theorem exists_theorem2SuppliedChartFinalBoundary_of_ell_eq_one_sourceData_suppliedRegularSuspension
    {ParamRed RRed ParamFull RFull : Type*}
    [CommMonoid RRed] [CommMonoid RFull]
    {Cred : AoyagiNormalCrossingChartCertificate.{uRed} ParamRed RRed}
    {Cfull : AoyagiNormalCrossingChartCertificate.{uFull} ParamFull RFull}
    {regularCount : ℕ}
    {RegularChartSource RegularIdealTransport RegularCoverage
      RegularJacobianCompatible :
        AoyagiNormalCrossingChartCertificate.{uRed} ParamRed RRed →
          AoyagiNormalCrossingChartCertificate.{uFull} ParamFull RFull →
            ℕ → Prop}
    {L : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints 1}
    (S : AoyagiDefinition3SourceData L 1 H r C)
    {lambda : ℚ} {poleOrder : ℕ}
    (Sreg : AoyagiSuppliedRegularSuspensionCertificate
      Cred Cfull regularCount RegularChartSource RegularIdealTransport
      RegularCoverage RegularJacobianCompatible lambda poleOrder)
    (hcount :
      regularCount = aoyagiTheorem2RegularVariableCount L H r)
    (hminimum :
      ∀ {m : Fin (1 + 1) → ℤ}
        (data : AoyagiDefinition3CeilData 1 m),
        m = aoyagiSelectedReducedWidths H r C →
          Cred.exponentData.exponentMinimum + aoyagiTheorem2RegularTerm L H r =
            aoyagiTheorem2Lambda_fromCeilData L 1 H r m data)
    (horder :
      ∀ {m : Fin (1 + 1) → ℤ}
        (data : AoyagiDefinition3CeilData 1 m),
        m = aoyagiSelectedReducedWidths H r C →
          Cred.exponentData.exponentOrder = data.theorem2OrderFormula) :
    ∃ (m : Fin (1 + 1) → ℤ) (data : AoyagiDefinition3CeilData 1 m),
      AoyagiTheorem2SuppliedChartFinalBoundary
          Cfull L 1 H r C m data lambda poleOrder ∧
      (∀ j : Fin (1 + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (1 + 1), 0 ≤ m j) ∧
      (∀ i : Fin (1 + 1),
        (1 : ℤ) * m i < ∑ j : Fin (1 + 1), m j) ∧
      (∀ i : Fin (1 + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat 1 m i) :=
  S.exists_theorem2SuppliedChartFinalBoundary_of_rankWidth_suppliedRegularSuspension
    S.sourceRangeRankWidth_of_ell_eq_one Sreg hcount hminimum horder

section SourceRank

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
  {N : ℕ}
  (W : Fin (N + 1) → Type v) [∀ i, AddCommGroup (W i)]
  [∀ i, TopologicalSpace (W i)] [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, Module K (W i)]
  [∀ i, ContinuousSMul K (W i)] [∀ i, FiniteDimensional K (W i)]
  (B : ∀ i : Fin N, W i.succ →ₗ[K] W i.castSucc)

omit [CompleteSpace K] [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, ContinuousSMul K (W i)] in
/-- Source-rank-stratum version of
`exists_theorem2SuppliedChartFinalBoundary_of_rankWidth_suppliedRegularSuspension`.

The source-rank hypotheses are used only to derive the source-range rank-width
hypothesis; the proof then delegates to the rank-width theorem. -/
theorem exists_theorem2SuppliedChartFinalBoundary_of_sourceRankStratum_suppliedRegularSuspension
    {ParamRed RRed ParamFull RFull : Type*}
    [CommMonoid RRed] [CommMonoid RFull]
    {Cred : AoyagiNormalCrossingChartCertificate.{uRed} ParamRed RRed}
    {Cfull : AoyagiNormalCrossingChartCertificate.{uFull} ParamFull RFull}
    {regularCount : ℕ}
    {RegularChartSource RegularIdealTransport RegularCoverage
      RegularJacobianCompatible :
        AoyagiNormalCrossingChartCertificate.{uRed} ParamRed RRed →
          AoyagiNormalCrossingChartCertificate.{uFull} ParamFull RFull →
            ℕ → Prop}
    {α : Type*}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {ell : ℕ} {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ} {x : α}
    {C : AoyagiSelectedCutpoints ell}
    (S : AoyagiDefinition3SourceData N ell H r C)
    (hx : x ∈ paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge)
    (hH : ∀ k : Fin (N + 1),
      H (k.val + 1) = Module.finrank K (W k))
    {lambda : ℚ} {poleOrder : ℕ}
    (Sreg : AoyagiSuppliedRegularSuspensionCertificate
      Cred Cfull regularCount RegularChartSource RegularIdealTransport
      RegularCoverage RegularJacobianCompatible lambda poleOrder)
    (hcount :
      regularCount = aoyagiTheorem2RegularVariableCount N H r)
    (hminimum :
      ∀ {m : Fin (ell + 1) → ℤ}
        (data : AoyagiDefinition3CeilData ell m),
        m = aoyagiSelectedReducedWidths H r C →
          Cred.exponentData.exponentMinimum + aoyagiTheorem2RegularTerm N H r =
            aoyagiTheorem2Lambda_fromCeilData N ell H r m data)
    (horder :
      ∀ {m : Fin (ell + 1) → ℤ}
        (data : AoyagiDefinition3CeilData ell m),
        m = aoyagiSelectedReducedWidths H r C →
          Cred.exponentData.exponentOrder = data.theorem2OrderFormula) :
    ∃ (m : Fin (ell + 1) → ℤ) (data : AoyagiDefinition3CeilData ell m),
      AoyagiTheorem2SuppliedChartFinalBoundary
          Cfull N ell H r C m data lambda poleOrder ∧
      (∀ j : Fin (ell + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (ell + 1), 0 ≤ m j) ∧
      (∀ i : Fin (ell + 1),
        (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j) ∧
      (∀ i : Fin (ell + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat ell m i) :=
  S.exists_theorem2SuppliedChartFinalBoundary_of_rankWidth_suppliedRegularSuspension
    (paperEndpointFixedBaseSourceRankStratum_sourceRangeRankWidth W B hx hH)
    Sreg hcount hminimum horder

end SourceRank

end AoyagiDefinition3SourceData

end Aoyagi
end DLN
end DLNFibre
