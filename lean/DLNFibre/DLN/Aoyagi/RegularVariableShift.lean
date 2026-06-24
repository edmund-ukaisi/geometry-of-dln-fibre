import DLNFibre.DLN.Aoyagi.Definition3RankWidthBridge
import DLNFibre.DLN.Aoyagi.Theorem2FiniteExponentBridge

/-!
# Regular-variable finite shift for Aoyagi Theorem 2

This file connects Aoyagi's post-Theorem-3 regular block-entry count to the
existing finite normal-crossing Jacobian/prior exponent shift.  It is only
finite certificate arithmetic: no regular-suspension chart construction,
analytic ideal transport, regular-coordinate additivity theorem, pole-order
theorem, or RLCT theorem is proved here.
-/

namespace DLNFibre
namespace DLN
namespace Aoyagi

set_option linter.style.longLine false

universe u v

/-- Source-range rank-width hypotheses supply the two endpoint bounds used by
Aoyagi's regular-variable finite shift. -/
theorem sourceRangeRankWidth_regularVariableEndpointBounds
    {L : ℕ} {H : ℕ → ℕ} {r : ℕ}
    (hr : ∀ s : ℕ, 1 ≤ s → s ≤ L + 1 → r ≤ H s) :
    r ≤ H 1 ∧ r ≤ H (L + 1) := by
  constructor
  · exact hr 1 (by omega) (by omega)
  · exact hr (L + 1) (by omega) (by omega)

section SourceRankEndpointBounds

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
  {N : ℕ}
  (W : Fin (N + 1) → Type v) [∀ i, AddCommGroup (W i)]
  [∀ i, TopologicalSpace (W i)] [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, Module K (W i)]
  [∀ i, ContinuousSMul K (W i)] [∀ i, FiniteDimensional K (W i)]
  (B : ∀ i : Fin N, W i.succ →ₗ[K] W i.castSucc)

omit [CompleteSpace K] [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, ContinuousSMul K (W i)] in
/-- A2 source-rank-stratum membership supplies the two endpoint rank-width
bounds used by the regular-variable finite shift. -/
theorem paperEndpointFixedBaseSourceRankStratum_regularVariableEndpointBounds
    {α : Type*}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ} {x : α} {H : ℕ → ℕ}
    (hx : x ∈ paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge)
    (hH : ∀ k : Fin (N + 1),
      H (k.val + 1) = Module.finrank K (W k)) :
    r ≤ H 1 ∧ r ≤ H (N + 1) := by
  have hrange :=
    paperEndpointFixedBaseSourceRankStratum_sourceRangeRankWidth W B hx hH
  constructor
  · exact hrange 1 (by omega) (by omega)
  · exact hrange (N + 1) (by omega) (by omega)

end SourceRankEndpointBounds

namespace AoyagiNormalCrossingExponentData

/-- Shifting Jacobian/prior exponents by Aoyagi's regular block-entry count
shifts the finite minimum by the displayed regular term. -/
theorem exponentMinimum_jacobianPriorLossShift_regularVariableCount
    (D : AoyagiNormalCrossingExponentData)
    (L : ℕ) (H : ℕ → ℕ) {r : ℕ}
    (hsource : r ≤ H 1) (htarget : r ≤ H (L + 1)) :
    (D.jacobianPriorLossShift
        (aoyagiTheorem2RegularVariableCount L H r)).exponentMinimum =
      D.exponentMinimum + aoyagiTheorem2RegularTerm L H r := by
  rw [D.exponentMinimum_jacobianPriorLossShift]
  rw [aoyagiTheorem2RegularTerm_eq_half_regularVariableCount
    L H hsource htarget]

/-- Shifting by Aoyagi's regular block-entry count preserves the finite order. -/
theorem exponentOrder_jacobianPriorLossShift_regularVariableCount
    (D : AoyagiNormalCrossingExponentData)
    (L : ℕ) (H : ℕ → ℕ) (r : ℕ) :
    (D.jacobianPriorLossShift
        (aoyagiTheorem2RegularVariableCount L H r)).exponentOrder =
      D.exponentOrder :=
  D.exponentOrder_jacobianPriorLossShift
    (aoyagiTheorem2RegularVariableCount L H r)

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
/-- Source-rank-stratum version of the regular-variable finite-minimum shift. -/
theorem exponentMinimum_jacobianPriorLossShift_regularVariableCount_of_sourceRankStratum
    (D : AoyagiNormalCrossingExponentData)
    {α : Type*}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ} {x : α}
    (hx : x ∈ paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge)
    (hH : ∀ k : Fin (N + 1),
      H (k.val + 1) = Module.finrank K (W k)) :
    (D.jacobianPriorLossShift
        (aoyagiTheorem2RegularVariableCount N H r)).exponentMinimum =
      D.exponentMinimum + aoyagiTheorem2RegularTerm N H r := by
  rcases paperEndpointFixedBaseSourceRankStratum_regularVariableEndpointBounds
      W B hx hH with
    ⟨hsource, htarget⟩
  exact
    D.exponentMinimum_jacobianPriorLossShift_regularVariableCount
      N H hsource htarget

end SourceRank

end AoyagiNormalCrossingExponentData

namespace AoyagiNormalCrossingChartCertificate

variable {Param R : Type*} [CommMonoid R]

/-- Chart-certificate projection of the finite regular-variable count shift. -/
theorem exponentData_exponentMinimum_jacobianPriorLossShift_regularVariableCount
    (C : AoyagiNormalCrossingChartCertificate Param R)
    (L : ℕ) (H : ℕ → ℕ) {r : ℕ}
    (hsource : r ≤ H 1) (htarget : r ≤ H (L + 1)) :
    (C.jacobianPriorLossShift
        (aoyagiTheorem2RegularVariableCount L H r)).exponentData.exponentMinimum =
      C.exponentData.exponentMinimum + aoyagiTheorem2RegularTerm L H r := by
  rw [C.exponentData_jacobianPriorLossShift]
  exact
    C.exponentData.exponentMinimum_jacobianPriorLossShift_regularVariableCount
      L H hsource htarget

/-- Chart-certificate projection: the finite order is unchanged by the
regular-variable count shift. -/
theorem exponentData_exponentOrder_jacobianPriorLossShift_regularVariableCount
    (C : AoyagiNormalCrossingChartCertificate Param R)
    (L : ℕ) (H : ℕ → ℕ) (r : ℕ) :
    (C.jacobianPriorLossShift
        (aoyagiTheorem2RegularVariableCount L H r)).exponentData.exponentOrder =
      C.exponentData.exponentOrder := by
  rw [C.exponentData_jacobianPriorLossShift]
  exact
    C.exponentData.exponentOrder_jacobianPriorLossShift_regularVariableCount
      L H r

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
/-- Chart-certificate projection of the source-rank-stratum regular-variable
finite-minimum shift. -/
theorem exponentData_exponentMinimum_jacobianPriorLossShift_regularVariableCount_of_sourceRankStratum
    (C : AoyagiNormalCrossingChartCertificate Param R)
    {α : Type*}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ} {x : α}
    (hx : x ∈ paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge)
    (hH : ∀ k : Fin (N + 1),
      H (k.val + 1) = Module.finrank K (W k)) :
    (C.jacobianPriorLossShift
        (aoyagiTheorem2RegularVariableCount N H r)).exponentData.exponentMinimum =
      C.exponentData.exponentMinimum + aoyagiTheorem2RegularTerm N H r := by
  rcases paperEndpointFixedBaseSourceRankStratum_regularVariableEndpointBounds
      W B hx hH with
    ⟨hsource, htarget⟩
  exact
    C.exponentData_exponentMinimum_jacobianPriorLossShift_regularVariableCount
      N H hsource htarget

end SourceRank

end AoyagiNormalCrossingChartCertificate

namespace AoyagiTheorem2FiniteExponentFormulaHypothesis

/-- Build the Theorem 2 finite formula boundary after shifting by the
post-Theorem-3 regular block-entry count.

The reduced minimum equality remains supplied in the form saying that the
reduced finite minimum plus Aoyagi's regular term equals the displayed final
lambda formula.  This is only finite exponent-array arithmetic; it does not
construct the regular-suspension chart or prove analytic additivity. -/
theorem of_regularVariableCountShift
    {D : AoyagiNormalCrossingExponentData}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m)
    (hsource : r ≤ H 1) (htarget : r ≤ H (L + 1))
    (hmin :
      D.exponentMinimum + aoyagiTheorem2RegularTerm L H r =
        aoyagiTheorem2Lambda_fromCeilData L ell H r m data)
    (horder : D.exponentOrder = data.theorem2OrderFormula) :
    AoyagiTheorem2FiniteExponentFormulaHypothesis
      (D.jacobianPriorLossShift
        (aoyagiTheorem2RegularVariableCount L H r))
      L ell H r m data where
  exponentMinimum_eq_theorem2Lambda_fromCeilData := by
    rw [D.exponentMinimum_jacobianPriorLossShift_regularVariableCount
      L H hsource htarget]
    exact hmin
  exponentOrder_eq_theorem2OrderFormula := by
    rw [D.exponentOrder_jacobianPriorLossShift_regularVariableCount]
    exact horder

/-- Chart-certificate version of `of_regularVariableCountShift`, using the
projected exponent data of a supplied chart certificate. -/
theorem of_chart_regularVariableCountShift
    {Param R : Type*} [CommMonoid R]
    {C : AoyagiNormalCrossingChartCertificate Param R}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m)
    (hsource : r ≤ H 1) (htarget : r ≤ H (L + 1))
    (hmin :
      C.exponentData.exponentMinimum + aoyagiTheorem2RegularTerm L H r =
        aoyagiTheorem2Lambda_fromCeilData L ell H r m data)
    (horder : C.exponentData.exponentOrder = data.theorem2OrderFormula) :
    AoyagiTheorem2FiniteExponentFormulaHypothesis
      (C.jacobianPriorLossShift
        (aoyagiTheorem2RegularVariableCount L H r)).exponentData
      L ell H r m data := by
  rw [C.exponentData_jacobianPriorLossShift]
  exact of_regularVariableCountShift data hsource htarget hmin horder

/-- Rank-width version of `of_regularVariableCountShift`.

The finite regular-variable shift only needs the endpoint bounds projected
from the source-range rank-width hypothesis. -/
theorem of_regularVariableCountShift_rankWidth
    {D : AoyagiNormalCrossingExponentData}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m)
    (hr : ∀ s : ℕ, 1 ≤ s → s ≤ L + 1 → r ≤ H s)
    (hmin :
      D.exponentMinimum + aoyagiTheorem2RegularTerm L H r =
        aoyagiTheorem2Lambda_fromCeilData L ell H r m data)
    (horder : D.exponentOrder = data.theorem2OrderFormula) :
    AoyagiTheorem2FiniteExponentFormulaHypothesis
      (D.jacobianPriorLossShift
        (aoyagiTheorem2RegularVariableCount L H r))
      L ell H r m data := by
  rcases sourceRangeRankWidth_regularVariableEndpointBounds hr with
    ⟨hsource, htarget⟩
  exact of_regularVariableCountShift data hsource htarget hmin horder

/-- Chart-certificate rank-width version of `of_chart_regularVariableCountShift`. -/
theorem of_chart_regularVariableCountShift_rankWidth
    {Param R : Type*} [CommMonoid R]
    {C : AoyagiNormalCrossingChartCertificate Param R}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m)
    (hr : ∀ s : ℕ, 1 ≤ s → s ≤ L + 1 → r ≤ H s)
    (hmin :
      C.exponentData.exponentMinimum + aoyagiTheorem2RegularTerm L H r =
        aoyagiTheorem2Lambda_fromCeilData L ell H r m data)
    (horder : C.exponentData.exponentOrder = data.theorem2OrderFormula) :
    AoyagiTheorem2FiniteExponentFormulaHypothesis
      (C.jacobianPriorLossShift
        (aoyagiTheorem2RegularVariableCount L H r)).exponentData
      L ell H r m data := by
  rcases sourceRangeRankWidth_regularVariableEndpointBounds hr with
    ⟨hsource, htarget⟩
  exact of_chart_regularVariableCountShift data hsource htarget hmin horder

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
/-- Source-rank-stratum version of `of_regularVariableCountShift`.

The stratum membership is used only to supply the endpoint rank-width bounds
`r <= H 1` and `r <= H (N+1)`. -/
theorem of_regularVariableCountShift_sourceRankStratum
    {D : AoyagiNormalCrossingExponentData}
    {α : Type*}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {ell : ℕ} {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ} {x : α}
    {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m)
    (hx : x ∈ paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge)
    (hH : ∀ k : Fin (N + 1),
      H (k.val + 1) = Module.finrank K (W k))
    (hmin :
      D.exponentMinimum + aoyagiTheorem2RegularTerm N H r =
        aoyagiTheorem2Lambda_fromCeilData N ell H r m data)
    (horder : D.exponentOrder = data.theorem2OrderFormula) :
    AoyagiTheorem2FiniteExponentFormulaHypothesis
      (D.jacobianPriorLossShift
        (aoyagiTheorem2RegularVariableCount N H r))
      N ell H r m data := by
  exact
    of_regularVariableCountShift_rankWidth data
      (paperEndpointFixedBaseSourceRankStratum_sourceRangeRankWidth W B hx hH)
      hmin horder

omit [CompleteSpace K] [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, ContinuousSMul K (W i)] in
/-- Chart-certificate source-rank-stratum version of
`of_chart_regularVariableCountShift`. -/
theorem of_chart_regularVariableCountShift_sourceRankStratum
    {Param R : Type*} [CommMonoid R]
    {C : AoyagiNormalCrossingChartCertificate Param R}
    {α : Type*}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {ell : ℕ} {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ} {x : α}
    {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m)
    (hx : x ∈ paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge)
    (hH : ∀ k : Fin (N + 1),
      H (k.val + 1) = Module.finrank K (W k))
    (hmin :
      C.exponentData.exponentMinimum + aoyagiTheorem2RegularTerm N H r =
        aoyagiTheorem2Lambda_fromCeilData N ell H r m data)
    (horder : C.exponentData.exponentOrder = data.theorem2OrderFormula) :
    AoyagiTheorem2FiniteExponentFormulaHypothesis
      (C.jacobianPriorLossShift
        (aoyagiTheorem2RegularVariableCount N H r)).exponentData
      N ell H r m data := by
  exact
    of_chart_regularVariableCountShift_rankWidth data
      (paperEndpointFixedBaseSourceRankStratum_sourceRangeRankWidth W B hx hH)
      hmin horder

end SourceRank

end AoyagiTheorem2FiniteExponentFormulaHypothesis

end Aoyagi
end DLN
end DLNFibre
