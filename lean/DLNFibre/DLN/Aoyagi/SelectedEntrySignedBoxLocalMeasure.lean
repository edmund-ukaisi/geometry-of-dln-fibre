import DLNFibre.DLN.Aoyagi.SelectedEntrySignedBoxMeasure

/-!
# Local-source finite-integral handoff for selected-entry signed boxes

This file plugs the elementary selected-entry monomial-unit calculation into
the local-source signed-box finite-integral socket.  The chart map,
pushforward identity, source set, residual-coordinate identification, and
regular-fiber loss/density bounds remain explicit hypotheses.

It does not construct an analytic chart, prove source coverage, prove the
weighted pushforward identity, identify the original source density, produce
normal crossings, or extract an RLCT.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace DLNFibre
namespace DLN
namespace Aoyagi

set_option linter.style.longLine false in
set_option linter.unusedFintypeInType false in
/-- Finite cover handoff for lower integrals over product measures.

If a base set `s` is covered by finitely many base sets `t i`, and the
nonnegative integrand has finite lower integral over every restricted product
measure `(μ.restrict (t i)).prod ν`, then it has finite lower integral over
`(μ.restrict s).prod ν`.

This is only measure bookkeeping.  It does not assert any source-chart
coverage; callers must provide the cover `hsub`. -/
theorem lintegral_prod_restrict_lt_top_of_subset_iUnion_finite
    {α β κ : Type*} [Fintype κ] [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {s : Set α} {t : κ → Set α}
    [SFinite μ] [SFinite ν]
    {f : α × β → ℝ≥0∞}
    (hsub : s ⊆ ⋃ i, t i)
    (hfinite :
      ∀ i : κ,
        (∫⁻ z : α × β, f z ∂ (μ.restrict (t i)).prod ν) < ∞) :
    (∫⁻ z : α × β, f z ∂ (μ.restrict s).prod ν) < ∞ := by
  classical
  have hsub_prod :
      s ×ˢ (Set.univ : Set β) ⊆
        ⋃ i : κ, t i ×ˢ (Set.univ : Set β) := by
    rintro ⟨x, y⟩ hx
    rcases Set.mem_iUnion.mp (hsub hx.1) with ⟨i, hxi⟩
    exact Set.mem_iUnion.mpr ⟨i, ⟨hxi, Set.mem_univ y⟩⟩
  have hmeasure_le :
      (μ.restrict s).prod ν ≤
        (μ.prod ν).restrict (⋃ i : κ, t i ×ˢ (Set.univ : Set β)) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    exact Measure.restrict_mono hsub_prod le_rfl
  have hleft_le :
      (∫⁻ z : α × β, f z ∂ (μ.restrict s).prod ν) ≤
        ∫⁻ z : α × β, f z ∂
          (μ.prod ν).restrict (⋃ i : κ, t i ×ˢ (Set.univ : Set β)) :=
    lintegral_mono' hmeasure_le (le_refl f)
  have hcover_le :
      (∫⁻ z : α × β, f z ∂
          (μ.prod ν).restrict (⋃ i : κ, t i ×ˢ (Set.univ : Set β))) ≤
        ∑' i : κ,
          ∫⁻ z : α × β, f z ∂
            (μ.prod ν).restrict (t i ×ˢ (Set.univ : Set β)) := by
    simpa only using
      (lintegral_iUnion_le
        (μ := μ.prod ν) (s := fun i : κ => t i ×ˢ (Set.univ : Set β)) f)
  have hsum_finite :
      (∑' i : κ,
          ∫⁻ z : α × β, f z ∂
            (μ.prod ν).restrict (t i ×ˢ (Set.univ : Set β))) < ∞ := by
    rw [tsum_fintype]
    exact ENNReal.sum_lt_top.mpr (fun i _hi => by
      rw [← Measure.restrict_prod_eq_prod_univ]
      exact hfinite i)
  exact hleft_le.trans_lt (hcover_le.trans_lt hsum_finite)

namespace PaperEndpointFixedBaseRegularCoordinateSourceData

universe v

variable {N : ℕ}
  (W : Fin (N + 1) → Type v) [∀ i, AddCommGroup (W i)]
  [∀ i, TopologicalSpace (W i)] [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, Module ℝ (W i)]
  [∀ i, ContinuousSMul ℝ (W i)]
  (B : ∀ i : Fin N, W i.succ →ₗ[ℝ] W i.castSucc)

set_option linter.style.longLine false in
set_option linter.unusedSectionVars false in
/-- Local-source selected-entry signed-box finite-integral handoff.

The theorem discharges the monomial-unit residual and formal Jacobian-density
data for a center-indexed selected-entry chart.  The source chart,
weighted-pushforward identity, residual-coordinate identification, and
regular-fiber loss/density estimates are still supplied. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_selectedEntryCenter_signedBox_withDensity_edgeMatrix
    [∀ j, FiniteDimensional ℝ (W j)]
    {α ι : Type*} [DecidableEq ι]
    [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {center : Finset ι} (pivot : center) {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    {source : Set α} {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {sourceChart : (center → ℝ) → α}
    {loss density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t Rreg creg Creg : ℝ}
    {Rres : center → ℝ}
    (hRreg : 0 < Rreg) (hcreg : 0 < creg) (hCreg : 0 ≤ Creg) (ht : 0 < t)
    (hsource_meas : MeasurableSet source)
    (hEdgeMatrix :
      Measurable (fun x : α ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) W B U₀ hU₀
          (fun p : Fin N ↦
            (Cedge x p : reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ))))
    (hsourceChart : AEMeasurable sourceChart
      (Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hmap :
      μ.restrict source =
        Measure.map sourceChart
          ((Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))).withDensity
            (fun y : center → ℝ =>
              ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivot y))))
    (hRres : ∀ i, 0 < Rres i)
    (hcrit_pivot :
      2 * t < ((center.erase pivot.1).card : ℝ) + 1)
    (hresidual_eq :
      ∀ y : center → ℝ,
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge (sourceChart y)) =
        SelectedEntrySignedBox.CenterCoord.residual pivot y)
    (hloss :
      ∀ᶠ x in nhdsWithin x₀ source,
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg →
            creg * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u))
    (hdensity_nonneg :
      ∀ᶠ x in nhdsWithin x₀ source,
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg →
            0 ≤ density (x, u))
    (hdensity_le :
      ∀ᶠ x in nhdsWithin x₀ source,
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg →
            density (x, u) ≤ Creg) :
    ∃ U : Set α, IsOpen U ∧ x₀ ∈ U ∧
      (∫⁻ z : α × EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)),
        ENNReal.ofReal
          ((Metric.ball
            (0 : EuclideanSpace ℝ
              (AoyagiRegularBlockCoordinateIndex
                (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg).indicator
            (fun u =>
              (loss (z.1, u)) ^
                (-(t + (aoyagiTheorem2RegularVariableCount N H r : ℝ) / 2)) *
                density (z.1, u)) z.2) ∂
          (μ.restrict (U ∩ source)).prod ν) < ∞ := by
  classical
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  have hcrit :
      ∀ i : center,
        2 * t * (SelectedEntrySignedBox.CenterCoord.lossExp pivot i : ℝ) <
          (SelectedEntrySignedBox.CenterCoord.densityExp pivot i : ℝ) + 1 := by
    intro i
    by_cases hi : i = pivot
    · subst i
      simpa [SelectedEntrySignedBox.CenterCoord.lossExp,
        SelectedEntrySignedBox.CenterCoord.densityExp, mul_assoc] using hcrit_pivot
    · simp [SelectedEntrySignedBox.CenterCoord.lossExp,
        SelectedEntrySignedBox.CenterCoord.densityExp, hi]
  have hres_eq :
      ∀ᵐ y : center → ℝ
        ∂Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
        aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge (sourceChart y)) =
          SelectedEntrySignedBox.CenterCoord.residualUnit pivot y *
            ∏ i, |y i| ^
              (2 * (SelectedEntrySignedBox.CenterCoord.lossExp pivot i : ℝ)) :=
    Filter.Eventually.of_forall fun y => by
      rw [hresidual_eq y]
      exact SelectedEntrySignedBox.CenterCoord.residual_eq_unit_mul_abs_monomial pivot y
  have hsourceDensity_eq :
      ∀ᵐ y : center → ℝ
        ∂Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
        SelectedEntrySignedBox.CenterCoord.sourceDensity pivot y =
          SelectedEntrySignedBox.CenterCoord.densityUnit pivot y *
            ∏ i, |y i| ^
              (SelectedEntrySignedBox.CenterCoord.densityExp pivot i : ℝ) :=
    Filter.Eventually.of_forall fun y =>
      SelectedEntrySignedBox.CenterCoord.sourceDensity_eq_unit_mul_abs_monomial pivot y
  have hresUnit_lower :
      ∀ᵐ y : center → ℝ
        ∂Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
        1 ≤ SelectedEntrySignedBox.CenterCoord.residualUnit pivot y :=
    Filter.Eventually.of_forall fun y =>
      SelectedEntrySignedBox.CenterCoord.one_le_residualUnit pivot y
  have hdensityUnit_nonneg :
      ∀ᵐ y : center → ℝ
        ∂Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
        0 ≤ SelectedEntrySignedBox.CenterCoord.densityUnit pivot y :=
    Filter.Eventually.of_forall fun y =>
      SelectedEntrySignedBox.CenterCoord.densityUnit_nonneg pivot y
  have hdensityUnit_le :
      ∀ᵐ y : center → ℝ
        ∂Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
        SelectedEntrySignedBox.CenterCoord.densityUnit pivot y ≤ 1 :=
    Filter.Eventually.of_forall fun y =>
      SelectedEntrySignedBox.CenterCoord.densityUnit_le_one pivot y
  simpa [ρ] using
    exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_residualSource_signedBox_withDensity_monomialUnits_edgeMatrix
      (W := W) (B := B) sourceData
      (source := source) (μ := μ) (ν := ν)
      (sourceChart := sourceChart)
      (sourceDensity := SelectedEntrySignedBox.CenterCoord.sourceDensity pivot)
      (residualUnit := SelectedEntrySignedBox.CenterCoord.residualUnit pivot)
      (densityUnit := SelectedEntrySignedBox.CenterCoord.densityUnit pivot)
      (loss := loss) (density := density)
      (t := t) (Rreg := Rreg) (creg := creg) (Creg := Creg)
      (cres := 1) (Cres := 1) (Rres := Rres)
      (hres := SelectedEntrySignedBox.CenterCoord.densityExp pivot)
      (kres := SelectedEntrySignedBox.CenterCoord.lossExp pivot)
      hRreg hcreg hCreg ht hsource_meas hEdgeMatrix hsourceChart hmap
      (by norm_num) (by norm_num) hRres hcrit
      (SelectedEntrySignedBox.CenterCoord.densityUnit_aemeasurable pivot Rres)
      hres_eq hsourceDensity_eq hresUnit_lower
      hdensityUnit_nonneg hdensityUnit_le
      (by simpa [ρ] using hloss)
      (by simpa [ρ] using hdensity_nonneg)
      (by simpa [ρ] using hdensity_le)

set_option linter.style.longLine false in
set_option linter.unusedSectionVars false in
/-- Selected-entry signed-box finite-integral handoff on the concrete finite
chart image.

This specializes the local-source selected-entry handoff to
`source = chartMap pivot '' signedBoxSet Rres`, `sourceChart = chartMap pivot`,
and `μ = volume`.  The selected-entry signed-box pushforward and chart-image
measurability are discharged by the finite chart theorem in
`SelectedEntrySignedBoxMeasure.lean`.  This still does not identify this finite
chart image with an original DLN source neighborhood. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_chartMap_selectedEntryCenter_signedBox_withDensity_edgeMatrix
    [∀ j, FiniteDimensional ℝ (W j)]
    {ι : Type*} [DecidableEq ι]
    {center : Finset ι} (pivot : center) {x₀ : center → ℝ}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : (center → ℝ) → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {loss density :
      (center → ℝ) × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t Rreg creg Creg : ℝ}
    {Rres : center → ℝ}
    (hRreg : 0 < Rreg) (hcreg : 0 < creg) (hCreg : 0 ≤ Creg) (ht : 0 < t)
    (hEdgeMatrix :
      Measurable (fun x : center → ℝ ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) W B U₀ hU₀
          (fun p : Fin N ↦
            (Cedge x p : reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ))))
    (hRres : ∀ i, 0 < Rres i)
    (hcrit_pivot :
      2 * t < ((center.erase pivot.1).card : ℝ) + 1)
    (hresidual_eq :
      ∀ y : center → ℝ,
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge
              (SelectedEntrySignedBox.CenterCoord.chartMap pivot y)) =
        SelectedEntrySignedBox.CenterCoord.residual pivot y)
    (hloss :
      ∀ᶠ x in nhdsWithin x₀
          (SelectedEntrySignedBox.CenterCoord.chartMap pivot ''
            SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg →
            creg * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u))
    (hdensity_nonneg :
      ∀ᶠ x in nhdsWithin x₀
          (SelectedEntrySignedBox.CenterCoord.chartMap pivot ''
            SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg →
            0 ≤ density (x, u))
    (hdensity_le :
      ∀ᶠ x in nhdsWithin x₀
          (SelectedEntrySignedBox.CenterCoord.chartMap pivot ''
            SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg →
            density (x, u) ≤ Creg) :
    ∃ U : Set (center → ℝ), IsOpen U ∧ x₀ ∈ U ∧
      (∫⁻ z : (center → ℝ) × EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)),
        ENNReal.ofReal
          ((Metric.ball
            (0 : EuclideanSpace ℝ
              (AoyagiRegularBlockCoordinateIndex
                (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg).indicator
            (fun u =>
              (loss (z.1, u)) ^
                (-(t + (aoyagiTheorem2RegularVariableCount N H r : ℝ) / 2)) *
                density (z.1, u)) z.2) ∂
          ((volume : Measure (center → ℝ)).restrict
            (U ∩
              (SelectedEntrySignedBox.CenterCoord.chartMap pivot ''
                SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres))).prod ν) < ∞ := by
  exact
    exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_selectedEntryCenter_signedBox_withDensity_edgeMatrix
      (W := W) (B := B) (pivot := pivot) sourceData
      (source :=
        SelectedEntrySignedBox.CenterCoord.chartMap pivot ''
          SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres)
      (μ := (volume : Measure (center → ℝ))) (ν := ν)
      (sourceChart := SelectedEntrySignedBox.CenterCoord.chartMap pivot)
      (loss := loss) (density := density)
      (t := t) (Rreg := Rreg) (creg := creg) (Creg := Creg) (Rres := Rres)
      hRreg hcreg hCreg ht
      (SelectedEntrySignedBox.CenterCoord.measurableSet_chartMap_image_signedBoxSet pivot Rres)
      hEdgeMatrix
      (SelectedEntrySignedBox.CenterCoord.aemeasurable_chartMap pivot Rres)
      (SelectedEntrySignedBox.CenterCoord.map_chartMap_signedBoxMeasure_withDensity_sourceDensity_eq_restrict_image
        pivot Rres).symm
      hRres hcrit_pivot hresidual_eq hloss hdensity_nonneg hdensity_le

set_option linter.style.longLine false in
set_option linter.unusedSectionVars false in
/-- Finite selected-entry sector-cover finite-integral assembly.

The per-pivot selected-entry chart-image finite-integral theorem is applied to
every pivot, then the finite sector cover of a smaller signed box by all
selected-entry chart images is used to obtain a finite integral over that
smaller box.

This is still a finite coordinate-cover statement.  It does not identify the
signed box with an Aoyagi source-rank stratum, construct an analytic source
chart, prove source-measure transport from original coordinates, or extract an
RLCT. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_selectedEntryCenter_signedBox_finiteCover_withDensity_edgeMatrix
    [∀ j, FiniteDimensional ℝ (W j)]
    {ι : Type*} [DecidableEq ι]
    {center : Finset ι} [Nonempty center]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : (center → ℝ) → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ (0 : center → ℝ) Cedge H r rEdge)
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {loss density :
      (center → ℝ) × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t Rreg creg Creg : ℝ}
    {Rres Sres : center → ℝ}
    (hRreg : 0 < Rreg) (hcreg : 0 < creg) (hCreg : 0 ≤ Creg) (ht : 0 < t)
    (hEdgeMatrix :
      Measurable (fun x : center → ℝ ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) W B U₀ hU₀
          (fun p : Fin N ↦
            (Cedge x p : reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ))))
    (hSres_le_Rres : ∀ i, Sres i ≤ Rres i)
    (hRres_one : ∀ i, 1 < Rres i)
    (hcrit_pivot :
      ∀ pivot : center, 2 * t < ((center.erase pivot.1).card : ℝ) + 1)
    (hresidual_eq :
      ∀ pivot : center,
        ∀ y : center → ℝ,
          aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge
                (SelectedEntrySignedBox.CenterCoord.chartMap pivot y)) =
          SelectedEntrySignedBox.CenterCoord.residual pivot y)
    (hloss :
      ∀ pivot : center,
        ∀ᶠ x in nhdsWithin (0 : center → ℝ)
            (SelectedEntrySignedBox.CenterCoord.chartMap pivot ''
              SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres),
          ∀ u : EuclideanSpace ℝ
              (AoyagiRegularBlockCoordinateIndex
                (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0)),
            u ∈ Metric.ball
                (0 : EuclideanSpace ℝ
                  (AoyagiRegularBlockCoordinateIndex
                    (Fin (Module.finrank ℝ U₀))
                    (throughSubspaceEndpointComplementIndex
                      (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                    (throughSubspaceEndpointComplementIndex
                      (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg →
              creg * (aoyagiCoordinateSquareSum
                  (paperEndpointFixedBaseResidualBlockCoordinateMap
                    (K := ℝ) W B U₀ hU₀ Cedge x) +
                aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u))
    (hdensity_nonneg :
      ∀ pivot : center,
        ∀ᶠ x in nhdsWithin (0 : center → ℝ)
            (SelectedEntrySignedBox.CenterCoord.chartMap pivot ''
              SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres),
          ∀ u : EuclideanSpace ℝ
              (AoyagiRegularBlockCoordinateIndex
                (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0)),
            u ∈ Metric.ball
                (0 : EuclideanSpace ℝ
                  (AoyagiRegularBlockCoordinateIndex
                    (Fin (Module.finrank ℝ U₀))
                    (throughSubspaceEndpointComplementIndex
                      (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                    (throughSubspaceEndpointComplementIndex
                      (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg →
              0 ≤ density (x, u))
    (hdensity_le :
      ∀ pivot : center,
        ∀ᶠ x in nhdsWithin (0 : center → ℝ)
            (SelectedEntrySignedBox.CenterCoord.chartMap pivot ''
              SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres),
          ∀ u : EuclideanSpace ℝ
              (AoyagiRegularBlockCoordinateIndex
                (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0)),
            u ∈ Metric.ball
                (0 : EuclideanSpace ℝ
                  (AoyagiRegularBlockCoordinateIndex
                    (Fin (Module.finrank ℝ U₀))
                    (throughSubspaceEndpointComplementIndex
                      (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                    (throughSubspaceEndpointComplementIndex
                      (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg →
              density (x, u) ≤ Creg) :
    ∃ U : Set (center → ℝ), IsOpen U ∧ (0 : center → ℝ) ∈ U ∧
      (∫⁻ z : (center → ℝ) × EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)),
        ENNReal.ofReal
          ((Metric.ball
            (0 : EuclideanSpace ℝ
              (AoyagiRegularBlockCoordinateIndex
                (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg).indicator
            (fun u =>
              (loss (z.1, u)) ^
                (-(t + (aoyagiTheorem2RegularVariableCount N H r : ℝ) / 2)) *
                density (z.1, u)) z.2) ∂
          ((volume : Measure (center → ℝ)).restrict
            (U ∩ SelectedEntrySignedBox.CenterCoord.signedBoxSet Sres)).prod ν) < ∞ := by
  classical
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  let chartImage : center → Set (center → ℝ) := fun pivot =>
    SelectedEntrySignedBox.CenterCoord.chartMap pivot ''
      SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres
  have hRres_pos : ∀ i, 0 < Rres i := fun i =>
    zero_lt_one.trans (hRres_one i)
  have hchart :
      ∀ pivot : center,
        ∃ U : Set (center → ℝ), IsOpen U ∧ (0 : center → ℝ) ∈ U ∧
          (∫⁻ z : (center → ℝ) × EuclideanSpace ℝ ρ,
            ENNReal.ofReal
              ((Metric.ball (0 : EuclideanSpace ℝ ρ) Rreg).indicator
                (fun u =>
                  (loss (z.1, u)) ^
                    (-(t + (aoyagiTheorem2RegularVariableCount N H r : ℝ) / 2)) *
                    density (z.1, u)) z.2) ∂
              ((volume : Measure (center → ℝ)).restrict
                (U ∩ chartImage pivot)).prod ν) < ∞ := by
    intro pivot
    rcases
        exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_chartMap_selectedEntryCenter_signedBox_withDensity_edgeMatrix
          (W := W) (B := B) (pivot := pivot) (x₀ := (0 : center → ℝ))
          sourceData (ν := ν) (loss := loss) (density := density)
          (t := t) (Rreg := Rreg) (creg := creg) (Creg := Creg)
          (Rres := Rres) hRreg hcreg hCreg ht hEdgeMatrix hRres_pos
          (hcrit_pivot pivot) (hresidual_eq pivot)
          (by simpa [chartImage] using hloss pivot)
          (by simpa [chartImage] using hdensity_nonneg pivot)
          (by simpa [chartImage] using hdensity_le pivot) with
      ⟨U, hUopen, h0U, hfinite⟩
    exact ⟨U, hUopen, h0U, by simpa [ρ, chartImage] using hfinite⟩
  choose U hUopen h0U hfinite using hchart
  let Uall : Set (center → ℝ) := ⋂ pivot : center, U pivot
  have hUall_open : IsOpen Uall := by
    dsimp [Uall]
    exact isOpen_iInter_of_finite hUopen
  have h0Uall : (0 : center → ℝ) ∈ Uall := by
    dsimp [Uall]
    exact Set.mem_iInter.mpr h0U
  let integrand :
      (center → ℝ) × EuclideanSpace ℝ ρ → ℝ≥0∞ :=
    fun z =>
      ENNReal.ofReal
        ((Metric.ball (0 : EuclideanSpace ℝ ρ) Rreg).indicator
          (fun u =>
            (loss (z.1, u)) ^
              (-(t + (aoyagiTheorem2RegularVariableCount N H r : ℝ) / 2)) *
              density (z.1, u)) z.2)
  have hcover :
      Uall ∩ SelectedEntrySignedBox.CenterCoord.signedBoxSet Sres ⊆
        ⋃ pivot : center, U pivot ∩ chartImage pivot := by
    intro x hx
    have hxchart :
        x ∈ ⋃ pivot : center, chartImage pivot :=
      SelectedEntrySignedBox.CenterCoord.signedBoxSet_subset_iUnion_chartMap_image_signedBoxSet_of_one_lt
        (R := Rres) (S := Sres) hSres_le_Rres hRres_one hx.2
    rcases Set.mem_iUnion.mp hxchart with ⟨pivot, hxpivot⟩
    refine Set.mem_iUnion.mpr ⟨pivot, ?_⟩
    exact ⟨Set.mem_iInter.mp hx.1 pivot, hxpivot⟩
  have hfinite_all :
      (∫⁻ z : (center → ℝ) × EuclideanSpace ℝ ρ, integrand z ∂
          ((volume : Measure (center → ℝ)).restrict
            (Uall ∩ SelectedEntrySignedBox.CenterCoord.signedBoxSet Sres)).prod ν) < ∞ :=
    lintegral_prod_restrict_lt_top_of_subset_iUnion_finite
      (μ := (volume : Measure (center → ℝ))) (ν := ν)
      (s := Uall ∩ SelectedEntrySignedBox.CenterCoord.signedBoxSet Sres)
      (t := fun pivot : center => U pivot ∩ chartImage pivot)
      (f := integrand) hcover hfinite
  exact ⟨Uall, hUall_open, h0Uall, by simpa [ρ, integrand] using hfinite_all⟩

end PaperEndpointFixedBaseRegularCoordinateSourceData

end Aoyagi
end DLN
end DLNFibre
