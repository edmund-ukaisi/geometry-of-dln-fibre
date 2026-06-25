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

end PaperEndpointFixedBaseRegularCoordinateSourceData

end Aoyagi
end DLN
end DLNFibre
