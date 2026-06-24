import DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates
import DLNFibre.DLN.Aoyagi.RegularSuspensionInterface

/-!
# Source-side algebra for supplied regular suspension

This file strengthens the source predicate used by the supplied
regular-suspension boundary with the already-proved scalar
regular-coordinate/residual ideal split.  It remains source-side algebraic
bookkeeping: the full regular-suspension chart, ideal transport, coverage,
Jacobian compatibility, exponent shift, normal crossings, and extraction remain
supplied elsewhere.
-/

namespace DLNFibre
namespace DLN
namespace Aoyagi

set_option linter.style.longLine false

universe uRed uFull u v

/-- The A2 canonical product-difference local source certificate strengthened by
the named scalar regular-coordinate/residual ideal neighborhood.

The reduced and full chart certificates and the regular count are parameters
only so this predicate has the same shape as a regular-suspension source
obligation. -/
def AoyagiCanonicalProductDifferenceRegularCoordinateIdealSource
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
  ∃ U₀ : Submodule K (reverseVertex W 0),
    ∃ hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)),
      PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate
        W B U₀ hU₀ x₀ Cedge r rEdge ∧
        PaperEndpointFixedBaseRegularCoordinateIdealSourceNeighborhood
          W B U₀ hU₀ x₀ Cedge r rEdge

set_option linter.unusedSectionVars false in
/-- A canonical product-difference local source certificate gives the stronger
regular-coordinate/residual ideal source predicate. -/
theorem aoyagiCanonicalProductDifferenceRegularCoordinateIdealSource_of_localSourceCertificate
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
    {ParamRed RRed ParamFull RFull : Type*}
    [CommMonoid RRed] [CommMonoid RFull]
    {Cred : AoyagiNormalCrossingChartCertificate.{uRed} ParamRed RRed}
    {Cfull : AoyagiNormalCrossingChartCertificate.{uFull} ParamFull RFull}
    {regularCount : ℕ}
    (hsource :
      PaperEndpointCanonicalProductDifferenceLocalSourceCertificate
        W B x₀ Cedge r rEdge) :
    AoyagiCanonicalProductDifferenceRegularCoordinateIdealSource
      W B x₀ Cedge r rEdge Cred Cfull regularCount := by
  rcases hsource with ⟨U₀, hU₀, cert⟩
  exact ⟨U₀, hU₀, cert, cert.regularCoordinateIdealSourceNeighborhood⟩

set_option linter.unusedSectionVars false in
/-- A continuous reversed-edge family based at `B`, together with supplied
base product and edge ranks, gives the canonical product-difference
regular-coordinate ideal source predicate. -/
theorem exists_aoyagiCanonicalProductDifferenceRegularCoordinateIdealSource
    {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
    {N : ℕ}
    (W : Fin (N + 1) → Type v) [∀ i, AddCommGroup (W i)]
    [∀ i, TopologicalSpace (W i)] [∀ i, IsTopologicalAddGroup (W i)]
    [∀ i, T2Space (W i)] [∀ i, Module K (W i)]
    [∀ i, ContinuousSMul K (W i)] [∀ i, FiniteDimensional K (W i)]
    (B : ∀ i : Fin N, W i.succ →ₗ[K] W i.castSucc)
    {α : Type*} [TopologicalSpace α]
    {x₀ : α}
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (r : ℕ) (rEdge : Fin N → ℕ)
    {ParamRed RRed ParamFull RFull : Type*}
    [CommMonoid RRed] [CommMonoid RFull]
    {Cred : AoyagiNormalCrossingChartCertificate.{uRed} ParamRed RRed}
    {Cfull : AoyagiNormalCrossingChartCertificate.{uFull} ParamFull RFull}
    {regularCount : ℕ}
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p))
    (hprod :
      Module.finrank K (LinearMap.range (paperTotalMap W B)) = r)
    (hedge :
      ∀ p : Fin N,
        Module.finrank K (LinearMap.range (reverseEdge W B p)) = rEdge p)
    (hle : ∀ p : Fin N, r ≤ rEdge p) :
    AoyagiCanonicalProductDifferenceRegularCoordinateIdealSource
      W B x₀ Cedge r rEdge Cred Cfull regularCount := by
  exact
    aoyagiCanonicalProductDifferenceRegularCoordinateIdealSource_of_localSourceCertificate
      W B
      (exists_paperEndpointCanonicalProductDifferenceLocalSourceCertificate
        W B Cedge r rEdge hCedge hbase hprod hedge hle)

set_option linter.unusedSectionVars false in
/-- A continuous reversed-edge family based at `B`, together with supplied
base product and edge ranks, gives the canonical product-difference
regular-coordinate ideal source predicate.  The inequalities `r ≤ rEdge p`
are derived from the base product factorization through each edge. -/
theorem exists_aoyagiCanonicalProductDifferenceRegularCoordinateIdealSource_of_rank_eq
    {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
    {N : ℕ}
    (W : Fin (N + 1) → Type v) [∀ i, AddCommGroup (W i)]
    [∀ i, TopologicalSpace (W i)] [∀ i, IsTopologicalAddGroup (W i)]
    [∀ i, T2Space (W i)] [∀ i, Module K (W i)]
    [∀ i, ContinuousSMul K (W i)] [∀ i, FiniteDimensional K (W i)]
    (B : ∀ i : Fin N, W i.succ →ₗ[K] W i.castSucc)
    {α : Type*} [TopologicalSpace α]
    {x₀ : α}
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (r : ℕ) (rEdge : Fin N → ℕ)
    {ParamRed RRed ParamFull RFull : Type*}
    [CommMonoid RRed] [CommMonoid RFull]
    {Cred : AoyagiNormalCrossingChartCertificate.{uRed} ParamRed RRed}
    {Cfull : AoyagiNormalCrossingChartCertificate.{uFull} ParamFull RFull}
    {regularCount : ℕ}
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p))
    (hprod :
      Module.finrank K (LinearMap.range (paperTotalMap W B)) = r)
    (hedge :
      ∀ p : Fin N,
        Module.finrank K (LinearMap.range (reverseEdge W B p)) = rEdge p) :
    AoyagiCanonicalProductDifferenceRegularCoordinateIdealSource
      W B x₀ Cedge r rEdge Cred Cfull regularCount := by
  exact
    aoyagiCanonicalProductDifferenceRegularCoordinateIdealSource_of_localSourceCertificate
      W B
      (exists_paperEndpointCanonicalProductDifferenceLocalSourceCertificate_of_rank_eq
        W B Cedge r rEdge hCedge hbase hprod hedge)

namespace AoyagiSuppliedRegularSuspensionBoundary

variable {ParamRed RRed ParamFull RFull : Type*}
variable [CommMonoid RRed] [CommMonoid RFull]
variable {Cred : AoyagiNormalCrossingChartCertificate.{uRed} ParamRed RRed}
variable {Cfull : AoyagiNormalCrossingChartCertificate.{uFull} ParamFull RFull}
variable {regularCount : ℕ}
variable {RegularIdealTransport RegularCoverage RegularJacobianCompatible :
  AoyagiNormalCrossingChartCertificate.{uRed} ParamRed RRed →
    AoyagiNormalCrossingChartCertificate.{uFull} ParamFull RFull →
      ℕ → Prop}

set_option linter.unusedSectionVars false in
/-- Build a supplied regular-suspension boundary whose source field records the
canonical source certificate together with the regular-coordinate/residual ideal
neighborhood.

Only the `regular_chart_source` field is discharged here.  The ideal transport,
coverage, Jacobian compatibility, full chart certificate, and exponent shift
remain supplied. -/
theorem of_canonicalProductDifferenceRegularCoordinateIdealSource
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
      (AoyagiCanonicalProductDifferenceRegularCoordinateIdealSource
        W B x₀ Cedge r rEdge)
      RegularIdealTransport RegularCoverage RegularJacobianCompatible where
  regular_chart_source :=
    aoyagiCanonicalProductDifferenceRegularCoordinateIdealSource_of_localSourceCertificate
      W B hsource
  regular_ideal_transport := hideal
  regular_coverage := hcoverage
  regular_jacobian_compatible := hjacobian
  exponentData_eq_shift := hexponent

end AoyagiSuppliedRegularSuspensionBoundary

end Aoyagi
end DLN
end DLNFibre
