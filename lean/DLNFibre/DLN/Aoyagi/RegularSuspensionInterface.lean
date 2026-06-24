import DLNFibre.DLN.Aoyagi.ProductReductionEntryIdealBoundary
import DLNFibre.DLN.Aoyagi.RegularVariableShift
import DLNFibre.DLN.Aoyagi.Theorem2FinalAssembly

/-!
# Supplied regular-suspension boundary for Aoyagi's p. 13 regular variables

This file packages a conservative interface for the regular-variable step
after Aoyagi Theorem 3.  The full regular-suspension chart certificate remains
supplied; this file only records the finite exponent equality it must have and
projects that equality into the existing Theorem 2 chart-final socket.

It does not construct the full chart from the reduced chart, prove chart
coverage, prove analytic ideal transport, prove Aoyagi Lemma 1, prove
regular-coordinate additivity, or extract an RLCT except through the explicit
extraction hypothesis for the supplied full certificate.
-/

namespace DLNFibre
namespace DLN
namespace Aoyagi

set_option linter.style.longLine false

universe uRed uFull u v

/-- The A2 canonical product-difference local source certificate, viewed as
the source predicate for a later supplied regular-suspension chart.

This predicate deliberately ignores the chart certificates and regular count:
it records only the elementary p. 13 source-side product-difference package
produced near the base chain.  Ideal transport, coverage, Jacobian
compatibility, the full chart certificate, and extraction remain separate
obligations in `AoyagiSuppliedRegularSuspensionBoundary`. -/
def AoyagiCanonicalProductDifferenceRegularChartSource
    {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
    {N : ℕ}
    (W : Fin (N + 1) → Type v) [∀ i, AddCommGroup (W i)]
    [∀ i, TopologicalSpace (W i)] [∀ i, IsTopologicalAddGroup (W i)]
    [∀ i, T2Space (W i)] [∀ i, Module K (W i)]
    [∀ i, ContinuousSMul K (W i)] [∀ i, FiniteDimensional K (W i)]
    (B : ∀ i : Fin N, W i.succ →ₗ[K] W i.castSucc)
    {α : Type*} [TopologicalSpace α]
    (x₀ : α)
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (r : ℕ) (rEdge : Fin N → ℕ)
    {ParamRed RRed ParamFull RFull : Type*}
    [CommMonoid RRed] [CommMonoid RFull]
    (_Cred : AoyagiNormalCrossingChartCertificate.{uRed} ParamRed RRed)
    (_Cfull : AoyagiNormalCrossingChartCertificate.{uFull} ParamFull RFull)
    (_regularCount : ℕ) : Prop :=
  PaperEndpointCanonicalProductDifferenceLocalSourceCertificate W B x₀ Cedge r rEdge

/-- Supplied boundary data for a regular-suspension chart.

The reduced and full chart certificates may have different parameter spaces
and coefficient monoids.  The only formal connection made here is the finite
exponent equality; the source, ideal-transport, coverage, and Jacobian
compatibility predicates are abstract supplied obligations for a later
analytic construction. -/
structure AoyagiSuppliedRegularSuspensionBoundary
    {ParamRed RRed ParamFull RFull : Type*}
    [CommMonoid RRed] [CommMonoid RFull]
    (Cred : AoyagiNormalCrossingChartCertificate.{uRed} ParamRed RRed)
    (Cfull : AoyagiNormalCrossingChartCertificate.{uFull} ParamFull RFull)
    (regularCount : ℕ)
    (RegularChartSource RegularIdealTransport RegularCoverage
      RegularJacobianCompatible :
        AoyagiNormalCrossingChartCertificate.{uRed} ParamRed RRed →
          AoyagiNormalCrossingChartCertificate.{uFull} ParamFull RFull →
            ℕ → Prop) : Prop where
  regular_chart_source :
    RegularChartSource Cred Cfull regularCount
  regular_ideal_transport :
    RegularIdealTransport Cred Cfull regularCount
  regular_coverage :
    RegularCoverage Cred Cfull regularCount
  regular_jacobian_compatible :
    RegularJacobianCompatible Cred Cfull regularCount
  exponentData_eq_shift :
    Cfull.exponentData =
      Cred.exponentData.jacobianPriorLossShift regularCount

namespace AoyagiSuppliedRegularSuspensionBoundary

variable {ParamRed RRed ParamFull RFull : Type*}
variable [CommMonoid RRed] [CommMonoid RFull]
variable {Cred : AoyagiNormalCrossingChartCertificate.{uRed} ParamRed RRed}
variable {Cfull : AoyagiNormalCrossingChartCertificate.{uFull} ParamFull RFull}
variable {regularCount : ℕ}
variable {RegularChartSource RegularIdealTransport RegularCoverage
  RegularJacobianCompatible :
    AoyagiNormalCrossingChartCertificate.{uRed} ParamRed RRed →
      AoyagiNormalCrossingChartCertificate.{uFull} ParamFull RFull →
        ℕ → Prop}

/-- Build a supplied regular-suspension boundary when the source predicate is
the A2 canonical product-difference local source certificate.

Only the `regular_chart_source` field is discharged here.  The analytic
ideal-transport, coverage, Jacobian-compatibility, full certificate, and finite
exponent-shift equality remain supplied exactly as in the general boundary. -/
theorem of_canonicalProductDifferenceRegularChartSource
    {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
    {N : ℕ}
    (W : Fin (N + 1) → Type v) [∀ i, AddCommGroup (W i)]
    [∀ i, TopologicalSpace (W i)] [∀ i, IsTopologicalAddGroup (W i)]
    [∀ i, T2Space (W i)] [∀ i, Module K (W i)]
    [∀ i, ContinuousSMul K (W i)] [∀ i, FiniteDimensional K (W i)]
    (B : ∀ i : Fin N, W i.succ →ₗ[K] W i.castSucc)
    {α : Type*} [TopologicalSpace α]
    {x₀ : α}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ}
    (hsource :
      PaperEndpointCanonicalProductDifferenceLocalSourceCertificate
        W B x₀ Cedge r rEdge)
    (hideal :
      RegularIdealTransport Cred Cfull regularCount)
    (hcoverage :
      RegularCoverage Cred Cfull regularCount)
    (hjacobian :
      RegularJacobianCompatible Cred Cfull regularCount)
    (hexponent :
      Cfull.exponentData =
        Cred.exponentData.jacobianPriorLossShift regularCount) :
    AoyagiSuppliedRegularSuspensionBoundary Cred Cfull regularCount
      (AoyagiCanonicalProductDifferenceRegularChartSource
        W B x₀ Cedge r rEdge)
      RegularIdealTransport RegularCoverage
      RegularJacobianCompatible where
  regular_chart_source := hsource
  regular_ideal_transport := hideal
  regular_coverage := hcoverage
  regular_jacobian_compatible := hjacobian
  exponentData_eq_shift := hexponent

/-- The supplied full certificate's finite minimum is the reduced minimum
shifted by half of the supplied regular count. -/
theorem full_exponentMinimum_eq_reduced_add_half_regularCount
    (B : AoyagiSuppliedRegularSuspensionBoundary Cred Cfull regularCount
      RegularChartSource RegularIdealTransport RegularCoverage
      RegularJacobianCompatible) :
    Cfull.exponentData.exponentMinimum =
      Cred.exponentData.exponentMinimum + (regularCount : ℚ) / 2 := by
  rw [B.exponentData_eq_shift]
  exact Cred.exponentData.exponentMinimum_jacobianPriorLossShift regularCount

/-- The supplied full certificate's finite order is the reduced finite order. -/
theorem full_exponentOrder_eq_reduced
    (B : AoyagiSuppliedRegularSuspensionBoundary Cred Cfull regularCount
      RegularChartSource RegularIdealTransport RegularCoverage
      RegularJacobianCompatible) :
    Cfull.exponentData.exponentOrder =
      Cred.exponentData.exponentOrder := by
  rw [B.exponentData_eq_shift]
  exact Cred.exponentData.exponentOrder_jacobianPriorLossShift regularCount

/-- When the supplied regular count is Aoyagi's p. 13 block-entry count, the
full finite minimum is the reduced finite minimum plus Aoyagi's displayed
regular term. -/
theorem full_exponentMinimum_eq_reduced_add_regularTerm
    (B : AoyagiSuppliedRegularSuspensionBoundary Cred Cfull regularCount
      RegularChartSource RegularIdealTransport RegularCoverage
      RegularJacobianCompatible)
    {L : ℕ} {H : ℕ → ℕ} {r : ℕ}
    (hcount :
      regularCount = aoyagiTheorem2RegularVariableCount L H r)
    (hsource : r ≤ H 1) (htarget : r ≤ H (L + 1)) :
    Cfull.exponentData.exponentMinimum =
      Cred.exponentData.exponentMinimum + aoyagiTheorem2RegularTerm L H r := by
  calc
    Cfull.exponentData.exponentMinimum =
        Cred.exponentData.exponentMinimum + (regularCount : ℚ) / 2 :=
      B.full_exponentMinimum_eq_reduced_add_half_regularCount
    _ = Cred.exponentData.exponentMinimum +
        aoyagiTheorem2RegularTerm L H r := by
      rw [hcount,
        ← aoyagiTheorem2RegularTerm_eq_half_regularVariableCount
          L H hsource htarget]

/-- The full certificate satisfies the Theorem 2 finite exponent formula once
the reduced certificate has the minimum plus regular-term equality and the
same finite order. -/
theorem theorem2FiniteExponentFormulaHypothesis_of_regularVariableCount
    (B : AoyagiSuppliedRegularSuspensionBoundary Cred Cfull regularCount
      RegularChartSource RegularIdealTransport RegularCoverage
      RegularJacobianCompatible)
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m)
    (hcount :
      regularCount = aoyagiTheorem2RegularVariableCount L H r)
    (hsource : r ≤ H 1) (htarget : r ≤ H (L + 1))
    (hmin :
      Cred.exponentData.exponentMinimum + aoyagiTheorem2RegularTerm L H r =
        aoyagiTheorem2Lambda_fromCeilData L ell H r m data)
    (horder :
      Cred.exponentData.exponentOrder = data.theorem2OrderFormula) :
    AoyagiTheorem2FiniteExponentFormulaHypothesis
      Cfull.exponentData L ell H r m data := by
  rw [B.exponentData_eq_shift, hcount]
  exact
    AoyagiTheorem2FiniteExponentFormulaHypothesis.of_regularVariableCountShift
      data hsource htarget hmin horder

end AoyagiSuppliedRegularSuspensionBoundary

/-- Supplied regular-suspension boundary together with extraction for the
actual full chart certificate. -/
structure AoyagiSuppliedRegularSuspensionCertificate
    {ParamRed RRed ParamFull RFull : Type*}
    [CommMonoid RRed] [CommMonoid RFull]
    (Cred : AoyagiNormalCrossingChartCertificate.{uRed} ParamRed RRed)
    (Cfull : AoyagiNormalCrossingChartCertificate.{uFull} ParamFull RFull)
    (regularCount : ℕ)
    (RegularChartSource RegularIdealTransport RegularCoverage
      RegularJacobianCompatible :
        AoyagiNormalCrossingChartCertificate.{uRed} ParamRed RRed →
          AoyagiNormalCrossingChartCertificate.{uFull} ParamFull RFull →
            ℕ → Prop)
    (lambda : ℚ) (poleOrder : ℕ) : Prop where
  boundary :
    AoyagiSuppliedRegularSuspensionBoundary Cred Cfull regularCount
      RegularChartSource RegularIdealTransport RegularCoverage
      RegularJacobianCompatible
  extractionHypothesis :
    Cfull.ExtractionHypothesis lambda poleOrder

namespace AoyagiSuppliedRegularSuspensionCertificate

variable {ParamRed RRed ParamFull RFull : Type*}
variable [CommMonoid RRed] [CommMonoid RFull]
variable {Cred : AoyagiNormalCrossingChartCertificate.{uRed} ParamRed RRed}
variable {Cfull : AoyagiNormalCrossingChartCertificate.{uFull} ParamFull RFull}
variable {regularCount : ℕ}
variable {RegularChartSource RegularIdealTransport RegularCoverage
  RegularJacobianCompatible :
    AoyagiNormalCrossingChartCertificate.{uRed} ParamRed RRed →
      AoyagiNormalCrossingChartCertificate.{uFull} ParamFull RFull →
        ℕ → Prop}

/-- Build the existing chart-final Theorem 2 boundary for the supplied full
regular-suspension certificate.

The extraction hypothesis is for `Cfull` itself.  The reduced certificate is
used only through the supplied finite exponent equality and the reduced
minimum/order equalities. -/
theorem theorem2SuppliedChartFinalBoundary_of_regularVariableCount
    {lambda : ℚ} {poleOrder : ℕ}
    (S : AoyagiSuppliedRegularSuspensionCertificate Cred Cfull regularCount
      RegularChartSource RegularIdealTransport RegularCoverage
      RegularJacobianCompatible lambda poleOrder)
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {cuts : AoyagiSelectedCutpoints ell} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m)
    (hselected : m = aoyagiSelectedReducedWidths H r cuts)
    (hcount :
      regularCount = aoyagiTheorem2RegularVariableCount L H r)
    (hsource : r ≤ H 1) (htarget : r ≤ H (L + 1))
    (hmin :
      Cred.exponentData.exponentMinimum + aoyagiTheorem2RegularTerm L H r =
        aoyagiTheorem2Lambda_fromCeilData L ell H r m data)
    (horder :
      Cred.exponentData.exponentOrder = data.theorem2OrderFormula) :
    AoyagiTheorem2SuppliedChartFinalBoundary
      Cfull L ell H r cuts m data lambda poleOrder where
  selectedWidths_eq_reduced := hselected
  extractionHypothesis := S.extractionHypothesis
  finiteExponentFormula :=
    S.boundary.theorem2FiniteExponentFormulaHypothesis_of_regularVariableCount
      data hcount hsource htarget hmin horder

end AoyagiSuppliedRegularSuspensionCertificate

end Aoyagi
end DLN
end DLNFibre
