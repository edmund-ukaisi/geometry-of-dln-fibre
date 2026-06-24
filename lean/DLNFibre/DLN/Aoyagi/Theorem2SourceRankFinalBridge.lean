import DLNFibre.DLN.Aoyagi.Definition3RankWidthBridge
import DLNFibre.DLN.Aoyagi.Theorem2FinalAssembly

/-!
# Source-rank-stratum handoff to Aoyagi Theorem 2 final boundaries

This file composes the source-rank-stratum rank-width bridge with the existing
Definition 3 source-data final-boundary handoffs.

It only replaces the repeated explicit hypothesis `∀ s, r ≤ H s` on the source
layer range by the A2 source-rank stratum plus the explicit convention
`H(k+1)=finrank(W k)`.  It does not construct selected cutpoints, prove
Definition 3 source data, construct normal-crossing charts, prove finite
exponent formulas, or invoke the normal-crossing extraction theorem.
-/

noncomputable section

namespace DLNFibre
namespace DLN
namespace Aoyagi

universe u v

section SourceRankFinal

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
  {N : ℕ}
  (W : Fin (N + 1) → Type v) [∀ i, AddCommGroup (W i)]
  [∀ i, TopologicalSpace (W i)] [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, Module K (W i)]
  [∀ i, ContinuousSMul K (W i)] [∀ i, FiniteDimensional K (W i)]
  (B : ∀ i : Fin N, W i.succ →ₗ[K] W i.castSucc)

namespace AoyagiDefinition3SourceData

omit [CompleteSpace K] [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, ContinuousSMul K (W i)] in
/-- Definition 3 source data plus an A2 source-rank stratum membership produce
the selected-width family and ceiling datum needed by the supplied final
Theorem 2 boundary.

The source-rank stratum is used only to discharge the source-range rank-width
hypothesis for `L = N`; selected cutpoints, source data, A0 extraction, and the
finite exponent formula hypothesis remain supplied. -/
theorem exists_theorem2SuppliedFinalBoundary_of_sourceRankStratum
    {α : Type*}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {D : AoyagiNormalCrossingExponentData}
    {ell : ℕ} {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ} {x : α}
    {C : AoyagiSelectedCutpoints ell}
    (S : AoyagiDefinition3SourceData N ell H r C)
    (hx : x ∈ paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge)
    (hH : ∀ k : Fin (N + 1),
      H (k.val + 1) = Module.finrank K (W k))
    {lambda : ℚ} {poleOrder : ℕ}
    (hNC : AoyagiNormalCrossingExtractionHypothesis D lambda poleOrder)
    (hFormula :
      ∀ {m : Fin (ell + 1) → ℤ}
        (data : AoyagiDefinition3CeilData ell m),
        m = aoyagiSelectedReducedWidths H r C →
        AoyagiTheorem2FiniteExponentFormulaHypothesis D N ell H r m data) :
    ∃ (m : Fin (ell + 1) → ℤ) (data : AoyagiDefinition3CeilData ell m),
      AoyagiTheorem2SuppliedFinalBoundary
          D N ell H r C m data lambda poleOrder ∧
      (∀ j : Fin (ell + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (ell + 1), 0 ≤ m j) ∧
      (∀ i : Fin (ell + 1),
        (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j) ∧
      (∀ i : Fin (ell + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat ell m i) :=
  S.exists_theorem2SuppliedFinalBoundary_of_rankWidth
    (paperEndpointFixedBaseSourceRankStratum_sourceRangeRankWidth W B hx hH)
    hNC hFormula

omit [CompleteSpace K] [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, ContinuousSMul K (W i)] in
/-- Chart-certificate version of
`exists_theorem2SuppliedFinalBoundary_of_sourceRankStratum`.

The chart certificate and extraction hypothesis remain supplied.  This theorem
only routes A2 source-rank-stratum rank-width provenance into the existing
chart-final socket. -/
theorem exists_theorem2SuppliedChartFinalBoundary_of_sourceRankStratum
    {Param R : Type*} [CommMonoid R]
    {α : Type*}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {Cnc : AoyagiNormalCrossingChartCertificate Param R}
    {ell : ℕ} {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ} {x : α}
    {C : AoyagiSelectedCutpoints ell}
    (S : AoyagiDefinition3SourceData N ell H r C)
    (hx : x ∈ paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge)
    (hH : ∀ k : Fin (N + 1),
      H (k.val + 1) = Module.finrank K (W k))
    {lambda : ℚ} {poleOrder : ℕ}
    (hNC : Cnc.ExtractionHypothesis lambda poleOrder)
    (hFormula :
      ∀ {m : Fin (ell + 1) → ℤ}
        (data : AoyagiDefinition3CeilData ell m),
        m = aoyagiSelectedReducedWidths H r C →
        AoyagiTheorem2FiniteExponentFormulaHypothesis
          Cnc.exponentData N ell H r m data) :
    ∃ (m : Fin (ell + 1) → ℤ) (data : AoyagiDefinition3CeilData ell m),
      AoyagiTheorem2SuppliedChartFinalBoundary
          Cnc N ell H r C m data lambda poleOrder ∧
      (∀ j : Fin (ell + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (ell + 1), 0 ≤ m j) ∧
      (∀ i : Fin (ell + 1),
        (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j) ∧
      (∀ i : Fin (ell + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat ell m i) :=
  S.exists_theorem2SuppliedChartFinalBoundary_of_rankWidth
    (paperEndpointFixedBaseSourceRankStratum_sourceRangeRankWidth W B hx hH)
    hNC hFormula

end AoyagiDefinition3SourceData

end SourceRankFinal

end Aoyagi
end DLN
end DLNFibre
