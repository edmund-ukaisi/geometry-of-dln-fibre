import DLNFibre.DLN.Aoyagi.Definition3RankWidthBridge
import DLNFibre.DLN.Aoyagi.Theorem2Eq5TerminalOrderBridge

/-!
# Source-rank-stratum handoff to the Eq5 terminal-order Theorem 2 sockets

This file composes the A2 source-rank-stratum rank-width bridge with the
existing Definition 3 source-data Eq5 terminal-order handoffs.

It only removes the repeated explicit source-range rank-width hypothesis for
`L = N`.  The Eq5 endpoint payload, active-ratio data, chart-count data,
normal-crossing extraction boundary, and finite formula consequences remain
explicit supplied hypotheses.
-/

noncomputable section

namespace DLNFibre
namespace DLN
namespace Aoyagi

set_option linter.style.longLine false

universe u v

section SourceRankEq5

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
the final-boundary socket after invoking the supplied Eq5 terminal-order
payload for the produced selected widths and ceiling datum.

The source-rank stratum is used only to discharge the source-range rank-width
hypothesis for `L = N`.  The Eq5 payload and all active-ratio/chart-count
obligations remain supplied. -/
theorem
  exists_theorem2SuppliedFinalBoundary_of_sourceRankStratum_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload
    {α : Type*}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {β : Type*} [DecidableEq β]
    {D : AoyagiNormalCrossingExponentData}
    {width : ℕ → ℕ} {Sfinal Jfinal n : ℕ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ} {x : α}
    {C : AoyagiSelectedCutpoints (n + 1)}
    (Ssrc : AoyagiDefinition3SourceData N (n + 1) H r C)
    (hx : x ∈ paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge)
    (hH : ∀ k : Fin (N + 1),
      H (k.val + 1) = Module.finrank K (W k))
    {lambda : ℚ} {poleOrder : ℕ}
    (hNC : AoyagiNormalCrossingExtractionHypothesis D lambda poleOrder)
    (hPayload :
      ∀ {m : Fin (n + 2) → ℤ}
        (data : AoyagiDefinition3CeilData (n + 1) m),
        m = aoyagiSelectedReducedWidths H r C →
          ∃ (t : ℕ → ℕ → ℕ → ℤ)
            (numerator leastValue : ℕ → ℕ → ℤ)
            (TC :
              AoyagiLemma5SuppliedTerminalCandidateFamily β N width
                Sfinal Jfinal n data.aParam data.ceilWidth m t numerator
                leastValue)
            (P : AoyagiLemma5SuppliedEq5EndpointBlockWidthOrderPayload data TC),
            P.cut = C ∧
              ∃ p : Fin D.numCharts × Fin D.numCoords,
                p ∈ D.activePairs ∧
                  D.ratioAt p =
                    aoyagiTheorem2Lambda_fromCeilData N (n + 1) H r m data ∧
                  (∀ p' ∈ D.activePairs,
                    aoyagiTheorem2Lambda_fromCeilData N (n + 1) H r m data ≤
                      D.ratioAt p') ∧
                  ∃ c : Fin D.numCharts,
                    D.countInChartAtRatio
                        (aoyagiTheorem2Lambda_fromCeilData N (n + 1) H r m data) c =
                      TC.terminalMinimumLabels.card ∧
                    ∀ c' : Fin D.numCharts,
                      D.countInChartAtRatio
                          (aoyagiTheorem2Lambda_fromCeilData N (n + 1) H r m data) c' ≤
                        TC.terminalMinimumLabels.card) :
    ∃ (m : Fin (n + 2) → ℤ)
      (data : AoyagiDefinition3CeilData (n + 1) m),
      AoyagiTheorem2SuppliedFinalBoundary
          D N (n + 1) H r C m data lambda poleOrder ∧
      (∀ j : Fin (n + 2), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (n + 2), 0 ≤ m j) ∧
      (∀ i : Fin (n + 2),
        ((n + 1 : ℕ) : ℤ) * m i < ∑ j : Fin (n + 2), m j) ∧
      (∀ i : Fin (n + 2), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat (n + 1) m i) :=
  Ssrc.exists_theorem2SuppliedFinalBoundary_of_rankWidth_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload
    (paperEndpointFixedBaseSourceRankStratum_sourceRangeRankWidth W B hx hH)
    hNC hPayload

omit [CompleteSpace K] [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, ContinuousSMul K (W i)] in
/-- Chart-certificate version of
`exists_theorem2SuppliedFinalBoundary_of_sourceRankStratum_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload`.

This is only a source-rank-stratum rank-width handoff into the existing
chart-final Eq5 wrapper. -/
theorem
  exists_theorem2SuppliedChartFinalBoundary_of_sourceRankStratum_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload
    {Param R : Type*} [CommMonoid R]
    {α : Type*}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {β : Type*} [DecidableEq β]
    {Cnc : AoyagiNormalCrossingChartCertificate Param R}
    {width : ℕ → ℕ} {Sfinal Jfinal n : ℕ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ} {x : α}
    {C : AoyagiSelectedCutpoints (n + 1)}
    (Ssrc : AoyagiDefinition3SourceData N (n + 1) H r C)
    (hx : x ∈ paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge)
    (hH : ∀ k : Fin (N + 1),
      H (k.val + 1) = Module.finrank K (W k))
    {lambda : ℚ} {poleOrder : ℕ}
    (hNC : Cnc.ExtractionHypothesis lambda poleOrder)
    (hPayload :
      ∀ {m : Fin (n + 2) → ℤ}
        (data : AoyagiDefinition3CeilData (n + 1) m),
        m = aoyagiSelectedReducedWidths H r C →
          ∃ (t : ℕ → ℕ → ℕ → ℤ)
            (numerator leastValue : ℕ → ℕ → ℤ)
            (TC :
              AoyagiLemma5SuppliedTerminalCandidateFamily β N width
                Sfinal Jfinal n data.aParam data.ceilWidth m t numerator
                leastValue)
            (P : AoyagiLemma5SuppliedEq5EndpointBlockWidthOrderPayload data TC),
            P.cut = C ∧
              ∃ p : Fin Cnc.numCharts × Fin Cnc.numCoords,
                p ∈ Cnc.exponentData.activePairs ∧
                  Cnc.exponentData.ratioAt p =
                    aoyagiTheorem2Lambda_fromCeilData N (n + 1) H r m data ∧
                  (∀ p' ∈ Cnc.exponentData.activePairs,
                    aoyagiTheorem2Lambda_fromCeilData N (n + 1) H r m data ≤
                      Cnc.exponentData.ratioAt p') ∧
                  ∃ c : Fin Cnc.numCharts,
                    Cnc.exponentData.countInChartAtRatio
                        (aoyagiTheorem2Lambda_fromCeilData N (n + 1) H r m data) c =
                      TC.terminalMinimumLabels.card ∧
                    ∀ c' : Fin Cnc.numCharts,
                      Cnc.exponentData.countInChartAtRatio
                          (aoyagiTheorem2Lambda_fromCeilData N (n + 1) H r m data) c' ≤
                        TC.terminalMinimumLabels.card) :
    ∃ (m : Fin (n + 2) → ℤ)
      (data : AoyagiDefinition3CeilData (n + 1) m),
      AoyagiTheorem2SuppliedChartFinalBoundary
          Cnc N (n + 1) H r C m data lambda poleOrder ∧
      (∀ j : Fin (n + 2), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (n + 2), 0 ≤ m j) ∧
      (∀ i : Fin (n + 2),
        ((n + 1 : ℕ) : ℤ) * m i < ∑ j : Fin (n + 2), m j) ∧
      (∀ i : Fin (n + 2), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat (n + 1) m i) :=
  Ssrc.exists_theorem2SuppliedChartFinalBoundary_of_rankWidth_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload
    (paperEndpointFixedBaseSourceRankStratum_sourceRangeRankWidth W B hx hH)
    hNC hPayload

end AoyagiDefinition3SourceData

end SourceRankEq5

end Aoyagi
end DLN
end DLNFibre
