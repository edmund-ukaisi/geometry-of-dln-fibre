import DLNFibre.DLN.Aoyagi.Theorem2RankWidthRegularShiftBridge

/-!
# Source-rank handoff for the regular-variable shifted Theorem 2 socket

This file composes the A2 source-rank-stratum rank-width bridge, Definition 3
source-data provenance, and the finite regular-variable shift.  It keeps the
reduced finite minimum/order obligations explicit.

It does not construct regular-suspension charts, transport analytic ideals,
prove Aoyagi Lemma 1, construct normal-crossing charts, prove active-ratio or
chart-count bounds, or prove pole order/RLCT beyond the explicitly supplied
normal-crossing extraction hypothesis.
-/

noncomputable section

namespace DLNFibre
namespace DLN
namespace Aoyagi

set_option linter.style.longLine false

universe u v

section SourceRankRegularShift

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
the final-boundary socket for a finite exponent datum shifted by Aoyagi's
regular block-entry count.

The source-rank stratum is used only to discharge source-range rank-width and
the endpoint rank-width bounds in the finite regular-variable shift.  The
reduced finite minimum/order obligations remain supplied. -/
theorem exists_theorem2SuppliedFinalBoundary_of_sourceRankStratum_regularVariableCountShift
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
    (hNC :
      AoyagiNormalCrossingExtractionHypothesis
        (D.jacobianPriorLossShift
          (aoyagiTheorem2RegularVariableCount N H r))
        lambda poleOrder)
    (hminimum :
      ∀ {m : Fin (ell + 1) → ℤ}
        (data : AoyagiDefinition3CeilData ell m),
        m = aoyagiSelectedReducedWidths H r C →
          D.exponentMinimum + aoyagiTheorem2RegularTerm N H r =
            aoyagiTheorem2Lambda_fromCeilData N ell H r m data)
    (horder :
      ∀ {m : Fin (ell + 1) → ℤ}
        (data : AoyagiDefinition3CeilData ell m),
        m = aoyagiSelectedReducedWidths H r C →
          D.exponentOrder = data.theorem2OrderFormula) :
    ∃ (m : Fin (ell + 1) → ℤ) (data : AoyagiDefinition3CeilData ell m),
      AoyagiTheorem2SuppliedFinalBoundary
          (D.jacobianPriorLossShift
            (aoyagiTheorem2RegularVariableCount N H r))
          N ell H r C m data lambda poleOrder ∧
      (∀ j : Fin (ell + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (ell + 1), 0 ≤ m j) ∧
      (∀ i : Fin (ell + 1),
        (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j) ∧
      (∀ i : Fin (ell + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat ell m i) :=
  S.exists_theorem2SuppliedFinalBoundary_of_rankWidth_regularVariableCountShift
    (paperEndpointFixedBaseSourceRankStratum_sourceRangeRankWidth W B hx hH)
    hNC hminimum horder

omit [CompleteSpace K] [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, ContinuousSMul K (W i)] in
/-- Chart-certificate version of
`exists_theorem2SuppliedFinalBoundary_of_sourceRankStratum_regularVariableCountShift`.

The shifted chart certificate and its extraction hypothesis remain supplied;
this theorem only composes source-rank provenance and finite exponent-array
arithmetic. -/
theorem exists_theorem2SuppliedChartFinalBoundary_of_sourceRankStratum_regularVariableCountShift
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
    (hNC :
      (Cnc.jacobianPriorLossShift
        (aoyagiTheorem2RegularVariableCount N H r)).ExtractionHypothesis
        lambda poleOrder)
    (hminimum :
      ∀ {m : Fin (ell + 1) → ℤ}
        (data : AoyagiDefinition3CeilData ell m),
        m = aoyagiSelectedReducedWidths H r C →
          Cnc.exponentData.exponentMinimum + aoyagiTheorem2RegularTerm N H r =
            aoyagiTheorem2Lambda_fromCeilData N ell H r m data)
    (horder :
      ∀ {m : Fin (ell + 1) → ℤ}
        (data : AoyagiDefinition3CeilData ell m),
        m = aoyagiSelectedReducedWidths H r C →
          Cnc.exponentData.exponentOrder = data.theorem2OrderFormula) :
    ∃ (m : Fin (ell + 1) → ℤ) (data : AoyagiDefinition3CeilData ell m),
      AoyagiTheorem2SuppliedChartFinalBoundary
          (Cnc.jacobianPriorLossShift
            (aoyagiTheorem2RegularVariableCount N H r))
          N ell H r C m data lambda poleOrder ∧
      (∀ j : Fin (ell + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (ell + 1), 0 ≤ m j) ∧
      (∀ i : Fin (ell + 1),
        (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j) ∧
      (∀ i : Fin (ell + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat ell m i) :=
  S.exists_theorem2SuppliedChartFinalBoundary_of_rankWidth_regularVariableCountShift
    (paperEndpointFixedBaseSourceRankStratum_sourceRangeRankWidth W B hx hH)
    hNC hminimum horder

end AoyagiDefinition3SourceData

end SourceRankRegularShift

end Aoyagi
end DLN
end DLNFibre
