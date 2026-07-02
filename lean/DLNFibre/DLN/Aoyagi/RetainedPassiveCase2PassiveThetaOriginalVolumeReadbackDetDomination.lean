import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaOriginalVolumeReadback
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaRawImageHandoff

/-!
# Case 2 passive-theta original-volume readback from determinant domination

This file composes the same-shrink raw/source package with the original-volume
readback bridge.  The determinant-side reverse domination and source-density
lower bound remain explicit hypotheses.

It does not prove determinant-chart Haar transport, exact raw-Haar
pushforward, raw-Haar normalization, source-image coverage, source-rank
coverage, original source-prior transport, normal crossings, pole order, or
RLCT extraction.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DLNFibre
namespace DLN
namespace Aoyagi

open ChartLocalSuffixState
open ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData

namespace PaperEndpointFixedBaseRegularCoordinateSourceData

universe v

/-- A pointwise lower bound on the image of a restricted set gives the
corresponding a.e. lower bound after restricting any measure to that set. -/
theorem ae_restrict_comp_lower_of_forall_image_lower
    {α β : Type*} [MeasurableSpace α] {μ : Measure α} {V : Set α}
    {f : α → β} {g : β → ℝ≥0∞} {ε : ℝ≥0∞}
    (hV : MeasurableSet V) (h : ∀ y ∈ f '' V, ε ≤ g y) :
    ∀ᵐ x ∂ μ.restrict V, ε ≤ g (f x) := by
  filter_upwards [ae_restrict_mem hV] with x hx
  exact h (f x) ⟨x, hx, rfl⟩

/-- A pointwise upper bound on a measurable restricted set gives the
corresponding a.e. upper bound after restricting any measure to that set. -/
theorem ae_restrict_upper_of_forall_mem
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    {f : α → ℝ} {K : ℝ}
    (hs : MeasurableSet s) (h : ∀ x ∈ s, f x ≤ K) :
    ∀ᵐ x ∂ μ.restrict s, f x ≤ K := by
  filter_upwards [ae_restrict_mem hs] with x hx
  exact h x hx

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This composes several large Case 2 local-measure packages through nested `let` binders.
/-- Same-shrink original-volume readback domination from determinant-chart
reverse domination and a lower source-density bound.

The theorem first chooses a readback bridge shrink, then chooses a smaller
same-shrink raw/source package inside it.  The returned `V` is the smaller
shrink.  The determinant-side domination and source-density lower bound are
still hypotheses on this returned `V`. -/
theorem exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta.PassiveFields
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      Measure.pi
        (fun i : Case2PassiveTheta.Center n S J =>
          volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      signedBox.withDensity
        (fun y : Case2PassiveTheta.Center n S J → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let passiveSource :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveMeasure.prod weightedBox
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let rawMap :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
    let jacobianDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveSource.withDensity jacobianDensity
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily →
        Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ eNext e
    let sourceDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ chartPiece : Set EdgeFamily,
                ∀ {Cdet ε : ℝ≥0∞},
                  MeasurableSet chartPiece →
                    chartPiece ⊆ sourceChart '' V →
                      rawHaar.restrict rawDetChart ≤
                        Cdet • Measure.map Y (passiveSource.restrict V) →
                        Cdet < ∞ →
                          (∀ᵐ z ∂baseJ.restrict V, ε ≤ sourceDensity z) →
                            ε ≠ 0 →
                              ε ≠ ∞ →
                                let c :=
                                  ((Measure.map
                                    (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                                      W₂ B₂ U₀)
                                    rawHaar).addHaarScalarFactor (originalTupleVolume d))
                                let D := Cdet * ε⁻¹
                                AEMeasurable readback (originalVolume.restrict chartPiece) ∧
                                  Measure.map readback (originalVolume.restrict chartPiece) ≤
                                    ((((c⁻¹ : NNReal) : ℝ≥0∞) * D) •
                                      coordinateSourceMeasure.restrict G) := by
  intro center pivotNext signedBox weightedBox passiveSource RawTuple EdgeFamily
    Y rawMap jacobianDensity baseJ sourceChart readback sourceDensity
    coordinateSourceMeasure rawDetChart rawSourceSet p13SourceSet d originalVolume
  rcases
      (by
        simpa [rawMap, rawSourceSet, p13SourceSet, d, originalVolume] using
          exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_restrict_rawSource_le_smul_case2PassiveTheta_rawMap
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ G hGopen hz₀G) with
    ⟨Vrb, hVrbopen, hz₀Vrb, hVrbG, _hleft_rb, _hinj_rb, _hcont_rb,
      _himage_rb, _hp13_rb, hreadback_bridge⟩
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource,
          RawTuple, Y, jacobianDensity, baseJ, EdgeFamily, sourceChart,
          sourceDensity, coordinateSourceMeasure, rawMap, rawDetChart,
          rawSourceSet, p13SourceSet] using
          exists_open_subset_case2PassiveTheta_sourceChart_rawMap_coordinateSourceMeasure_reverse_domination_package_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceImageDensity passiveMeasure Rres Vrb
            hVrbopen hz₀Vrb) with
    ⟨V, hVopen, hz₀V, hV_vrb, hleftV, hsource_injV, hsource_contOnV,
      hsource_imageV, himage_p13V, _hraw_memV, _hrawMap_aemeas,
      _hmeasure_maps, hraw_dom_package⟩
  have hVG : V ⊆ G := fun z hz ↦ hVrbG (hV_vrb hz)
  have hleftV' : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleftV z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext hz
  have himage_p13V' : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    simpa [sourceChart, p13SourceSet, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13V (sourceChart z) z.A1passive z.F2 z.A3passive
        z.Ctop z.F3 z.yNext hzV rfl
  refine ⟨V, hVopen, hz₀V, hVG, hleftV', hsource_injV, hsource_contOnV,
    hsource_imageV, himage_p13V', ?_⟩
  intro rawHaar _instRawHaar chartPiece Cdet ε hchartPiece hchartPiece_sub_image
    hdet_dom hCdet hsource_lower hε_ne_zero hε_ne_top c D
  rcases (hraw_dom_package rawHaar hdet_dom hCdet hsource_lower hε_ne_zero
    hε_ne_top) with
    ⟨_hD, hraw_dom⟩
  have hchartPiece_sub_vrb : chartPiece ⊆ sourceChart '' Vrb := by
    intro E hE
    rcases hchartPiece_sub_image hE with ⟨z, hzV, rfl⟩
    exact ⟨z, hV_vrb hzV, rfl⟩
  have hrestrict_vrb :
      (coordinateSourceMeasure.restrict V).restrict Vrb =
        coordinateSourceMeasure.restrict V := by
    exact Measure.restrict_eq_self_of_ae_mem
      ((ae_restrict_mem hVopen.measurableSet).mono (fun _ hzV ↦ hV_vrb hzV))
  have hraw_dom_bridge :
      rawHaar.restrict rawSourceSet ≤
        D • Measure.map rawMap ((coordinateSourceMeasure.restrict V).restrict Vrb) := by
    simpa [RawTuple, rawMap, rawSourceSet, coordinateSourceMeasure, D, hrestrict_vrb] using
      hraw_dom
  have hreadback_volume :
      AEMeasurable readback (originalVolume.restrict chartPiece) ∧
        Measure.map readback (originalVolume.restrict chartPiece) ≤
          ((((c⁻¹ : NNReal) : ℝ≥0∞) * D) •
            (coordinateSourceMeasure.restrict V).restrict G) := by
    simpa [rawMap, rawSourceSet, d, originalVolume, c, D] using
      hreadback_bridge (coordinateSourceMeasure.restrict V) rawHaar chartPiece
        (D := D) hchartPiece hchartPiece_sub_vrb hraw_dom_bridge
  have hrestrict_G :
      (coordinateSourceMeasure.restrict V).restrict G =
        coordinateSourceMeasure.restrict V := by
    exact Measure.restrict_eq_self_of_ae_mem
      ((ae_restrict_mem hVopen.measurableSet).mono (fun _ hzV ↦ hVG hzV))
  have hV_le_G :
      coordinateSourceMeasure.restrict V ≤
        (1 : ℝ≥0∞) • coordinateSourceMeasure.restrict G := by
    simpa using (Measure.restrict_mono hVG le_rfl)
  have hmap_le_G :
      Measure.map readback (originalVolume.restrict chartPiece) ≤
        (((c⁻¹ : NNReal) : ℝ≥0∞) * D) • coordinateSourceMeasure.restrict G := by
    have hstep :
        Measure.map readback (originalVolume.restrict chartPiece) ≤
          ((((c⁻¹ : NNReal) : ℝ≥0∞) * D) * (1 : ℝ≥0∞)) •
            coordinateSourceMeasure.restrict G :=
      measure_le_smul_of_le_smul_of_le_smul
        (by simpa [hrestrict_G] using hreadback_volume.2) hV_le_G
    simpa [mul_one] using hstep
  exact ⟨hreadback_volume.1, hmap_le_G⟩

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This measure-level wrapper keeps the determinant and density inputs explicit.
/-- Original edge-family priors are dominated on the full local source-chart
image by the chart-produced coordinate source measure.

The determinant-side reverse domination, the lower bound for `sourceDensity`,
and the local upper bound for the original-prior density remain explicit
hypotheses.  This theorem does not prove determinant-chart Haar transport,
exact raw-Haar pushforward, raw-Haar normalization, source-image coverage,
source-rank coverage, normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyPrior_restrict_sourceChart_image_le_smul_sourceImageReference_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower_priorDensity_upper
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta.PassiveFields
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      Measure.pi
        (fun i : Case2PassiveTheta.Center n S J =>
          volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      signedBox.withDensity
        (fun y : Case2PassiveTheta.Center n S J → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let passiveSource :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveMeasure.prod weightedBox
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let rawMap :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
    let jacobianDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveSource.withDensity jacobianDensity
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily →
        Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ eNext e
    let sourceDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ {Cdet ε : ℝ≥0∞},
                  rawHaar.restrict rawDetChart ≤
                    Cdet • Measure.map Y (passiveSource.restrict V) →
                    Cdet < ∞ →
                      (∀ᵐ z ∂baseJ.restrict V, ε ≤ sourceDensity z) →
                        ε ≠ 0 →
                          ε ≠ ∞ →
                            ∀ {density : EdgeFamily → ℝ} {Kprior : ℝ},
                              (∀ᵐ E ∂originalVolume.restrict
                                (sourceChart '' V), density E ≤ Kprior) →
                                let cHaar :=
                                  ((Measure.map
                                    (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                                      W₂ B₂ U₀)
                                    rawHaar).addHaarScalarFactor (originalTupleVolume d))
                                let Ddet := Cdet * ε⁻¹
                                let Dvol := ((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet
                                let Cprior := ENNReal.ofReal Kprior * Dvol
                                Cprior < ∞ ∧
                                  (originalEdgeFamilyPrior (V := reverseVertex W₂)
                                    (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                    density).restrict (sourceChart '' V) ≤
                                      Cprior •
                                        (Measure.map sourceChart
                                          (coordinateSourceMeasure.restrict V)).restrict
                                            (sourceChart '' V) := by
  intro center pivotNext signedBox weightedBox passiveSource RawTuple EdgeFamily
    Y rawMap jacobianDensity baseJ sourceChart readback sourceDensity
    coordinateSourceMeasure rawDetChart rawSourceSet p13SourceSet d originalVolume
  rcases
      (by
        simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawSourceSet,
          p13SourceSet, d, originalVolume] using
          exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceReference_of_restrict_rawSource_le_smul_case2PassiveTheta_rawMap
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ G hGopen hz₀G) with
    ⟨Vvol, hVvolopen, hz₀Vvol, hVvolG, hvolume_bridge⟩
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource,
          RawTuple, Y, jacobianDensity, baseJ, EdgeFamily, sourceChart,
          sourceDensity, coordinateSourceMeasure, rawMap, rawDetChart,
          rawSourceSet, p13SourceSet] using
          exists_open_subset_case2PassiveTheta_sourceChart_rawMap_coordinateSourceMeasure_reverse_domination_package_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceImageDensity passiveMeasure Rres Vvol
            hVvolopen hz₀Vvol) with
    ⟨V, hVopen, hz₀V, hV_vvol, hleftV, hsource_injV, hsource_contOnV,
      hsource_imageV, himage_p13V, _hraw_memV, _hrawMap_aemeas,
      _hmeasure_maps, hraw_dom_package⟩
  have hVG : V ⊆ G := fun z hz ↦ hVvolG (hV_vvol hz)
  have hleftV' : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleftV z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext hz
  have himage_p13V' : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    simpa [sourceChart, p13SourceSet, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13V (sourceChart z) z.A1passive z.F2 z.A3passive
        z.Ctop z.F3 z.yNext hzV rfl
  refine ⟨V, hVopen, hz₀V, hVG, hleftV', hsource_injV, hsource_contOnV,
    hsource_imageV, himage_p13V', ?_⟩
  intro rawHaar _instRawHaar Cdet ε hdet_dom hCdet hsource_lower
    hε_ne_zero hε_ne_top density Kprior hdensity cHaar Ddet Dvol Cprior
  rcases (hraw_dom_package rawHaar hdet_dom hCdet hsource_lower hε_ne_zero
    hε_ne_top) with
    ⟨hDdet, hraw_dom⟩
  have hrestrict_vvol :
      (coordinateSourceMeasure.restrict V).restrict Vvol =
        coordinateSourceMeasure.restrict V :=
    restrict_restrict_eq_self_of_subset hVopen.measurableSet hV_vvol
  have hraw_dom_bridge :
      rawHaar.restrict rawSourceSet ≤
        Ddet • Measure.map rawMap ((coordinateSourceMeasure.restrict V).restrict Vvol) := by
    simpa [RawTuple, rawMap, rawSourceSet, coordinateSourceMeasure, Ddet,
      hrestrict_vvol] using hraw_dom
  have himage_sub_p13 : sourceChart '' V ⊆ p13SourceSet := by
    intro E hE
    exact himage_p13V' E hE
  have hvolume_dom :
      originalVolume.restrict (sourceChart '' V) ≤
        Dvol • Measure.map sourceChart (coordinateSourceMeasure.restrict V) := by
    simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawSourceSet,
      p13SourceSet, d, originalVolume, Ddet, Dvol, cHaar, hrestrict_vvol] using
      hvolume_bridge (coordinateSourceMeasure.restrict V) rawHaar
        (sourceChart '' V) (D := Ddet) hsource_imageV himage_sub_p13
        hraw_dom_bridge
  have hvolume_dom_image :
      originalVolume.restrict (sourceChart '' V) ≤
        Dvol •
          (Measure.map sourceChart (coordinateSourceMeasure.restrict V)).restrict
            (sourceChart '' V) :=
    restrict_le_smul_restrict_of_le_smul_of_subset
      (μ := originalVolume)
      (η := Measure.map sourceChart (coordinateSourceMeasure.restrict V))
      (s := sourceChart '' V) (t := sourceChart '' V) (c := Dvol)
      hsource_imageV (fun _ h ↦ h) hvolume_dom
  have hprior_dom :
      (originalEdgeFamilyPrior (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
        density).restrict (sourceChart '' V) ≤
          Cprior •
            (Measure.map sourceChart (coordinateSourceMeasure.restrict V)).restrict
              (sourceChart '' V) := by
    simpa [originalEdgeFamilyPrior, originalVolume, Cprior] using
      restrict_withDensity_ofReal_le_smul_of_restrict_le_smul_of_ae_le
        (μ := originalVolume)
        (ν := (Measure.map sourceChart
          (coordinateSourceMeasure.restrict V)).restrict (sourceChart '' V))
        (density := density) (s := sourceChart '' V) (K := Kprior)
        (c := Dvol) hsource_imageV hvolume_dom_image hdensity
  have hDdet' : Ddet < ∞ := by
    simpa [Ddet] using hDdet
  have hDvol : Dvol < ∞ := by
    dsimp [Dvol]
    exact ENNReal.mul_lt_top (by simp) hDdet'
  have hCprior : Cprior < ∞ := by
    dsimp [Cprior]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hDvol
  exact ⟨hCprior, hprior_dom⟩

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This wrapper replaces two a.e. density sockets by pointwise bounds on the returned image.
/-- Full source-image prior domination using pointwise bounds on the returned
source-chart image.

The pointwise source-image lower bound and prior-density upper bound are only
stronger sufficient hypotheses for the existing a.e. density sockets.  This
theorem does not prove determinant-chart Haar transport, exact raw-Haar
pushforward, raw-Haar normalization, source-image coverage, source-rank
coverage, normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyPrior_restrict_sourceChart_image_le_smul_sourceImageReference_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceImageDensity_image_lower_priorDensity_image_upper
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta.PassiveFields
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      Measure.pi
        (fun i : Case2PassiveTheta.Center n S J =>
          volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      signedBox.withDensity
        (fun y : Case2PassiveTheta.Center n S J → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let passiveSource :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveMeasure.prod weightedBox
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let rawMap :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
    let jacobianDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveSource.withDensity jacobianDensity
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily →
        Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ eNext e
    let sourceDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ {Cdet ε : ℝ≥0∞},
                  rawHaar.restrict rawDetChart ≤
                    Cdet • Measure.map Y (passiveSource.restrict V) →
                    Cdet < ∞ →
                      (∀ E ∈ sourceChart '' V, ε ≤ sourceImageDensity E) →
                        ε ≠ 0 →
                          ε ≠ ∞ →
                            ∀ {density : EdgeFamily → ℝ} {Kprior : ℝ},
                              (∀ E ∈ sourceChart '' V, density E ≤ Kprior) →
                                let cHaar :=
                                  ((Measure.map
                                    (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                                      W₂ B₂ U₀)
                                    rawHaar).addHaarScalarFactor (originalTupleVolume d))
                                let Ddet := Cdet * ε⁻¹
                                let Dvol := ((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet
                                let Cprior := ENNReal.ofReal Kprior * Dvol
                                Cprior < ∞ ∧
                                  (originalEdgeFamilyPrior (V := reverseVertex W₂)
                                    (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                    density).restrict (sourceChart '' V) ≤
                                      Cprior •
                                        (Measure.map sourceChart
                                          (coordinateSourceMeasure.restrict V)).restrict
                                            (sourceChart '' V) := by
  intro center pivotNext signedBox weightedBox passiveSource RawTuple EdgeFamily
    Y rawMap jacobianDensity baseJ sourceChart readback sourceDensity
    coordinateSourceMeasure rawDetChart rawSourceSet p13SourceSet d originalVolume
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource,
          RawTuple, EdgeFamily, Y, rawMap, jacobianDensity, baseJ,
          sourceChart, readback, sourceDensity, coordinateSourceMeasure,
          rawDetChart, rawSourceSet, p13SourceSet, d, originalVolume] using
          exists_open_subset_originalEdgeFamilyPrior_restrict_sourceChart_image_le_smul_sourceImageReference_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower_priorDensity_upper
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceImageDensity passiveMeasure Rres G hGopen hz₀G) with
    ⟨V, hVopen, hz₀V, hVG, hleftV, hsource_injV, hsource_contOnV,
      hsource_imageV, himage_p13V, hprior_package⟩
  have hleftV' : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleftV z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext hz
  have himage_p13V' : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    simpa [sourceChart, p13SourceSet, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13V (sourceChart z) z.A1passive z.F2 z.A3passive
        z.Ctop z.F3 z.yNext hzV rfl
  refine ⟨V, hVopen, hz₀V, hVG, hleftV', hsource_injV, hsource_contOnV,
    hsource_imageV, himage_p13V', ?_⟩
  intro rawHaar _instRawHaar Cdet ε hdet_dom hCdet hsource_image_lower
    hε_ne_zero hε_ne_top density Kprior hprior_image_upper cHaar Ddet Dvol Cprior
  have hsource_lower :
      ∀ᵐ z ∂baseJ.restrict V, ε ≤ sourceDensity z := by
    simpa [sourceDensity] using
      ae_restrict_comp_lower_of_forall_image_lower
        (μ := baseJ) (V := V) (f := sourceChart)
        (g := sourceImageDensity) (ε := ε)
        hVopen.measurableSet hsource_image_lower
  have hprior_upper :
      ∀ᵐ E ∂originalVolume.restrict (sourceChart '' V),
        density E ≤ Kprior :=
    ae_restrict_upper_of_forall_mem
      (μ := originalVolume) (s := sourceChart '' V)
      (f := density) (K := Kprior) hsource_imageV hprior_image_upper
  simpa [cHaar, Ddet, Dvol, Cprior] using
    hprior_package rawHaar hdet_dom hCdet hsource_lower hε_ne_zero
      hε_ne_top (density := density) (Kprior := Kprior) hprior_upper

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This wrapper inherits returned-image bounds from the caller's larger input image.
/-- Full source-image prior domination using pointwise bounds on the input
source-chart image.

The returned shrink `V` is contained in the input neighborhood `G`, so bounds
on `sourceChart '' G` restrict to the returned image `sourceChart '' V`.  This
theorem does not prove determinant-chart Haar transport, exact raw-Haar
pushforward, raw-Haar normalization, source-image coverage, source-rank
coverage, normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyPrior_restrict_sourceChart_image_le_smul_sourceImageReference_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceImageDensity_input_image_lower_priorDensity_input_image_upper
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta.PassiveFields
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      Measure.pi
        (fun i : Case2PassiveTheta.Center n S J =>
          volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      signedBox.withDensity
        (fun y : Case2PassiveTheta.Center n S J → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let passiveSource :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveMeasure.prod weightedBox
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let rawMap :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
    let jacobianDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveSource.withDensity jacobianDensity
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily →
        Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ eNext e
    let sourceDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ {Cdet ε : ℝ≥0∞},
                  rawHaar.restrict rawDetChart ≤
                    Cdet • Measure.map Y (passiveSource.restrict V) →
                    Cdet < ∞ →
                      (∀ E ∈ sourceChart '' G, ε ≤ sourceImageDensity E) →
                        ε ≠ 0 →
                          ε ≠ ∞ →
                            ∀ {density : EdgeFamily → ℝ} {Kprior : ℝ},
                              (∀ E ∈ sourceChart '' G, density E ≤ Kprior) →
                                let cHaar :=
                                  ((Measure.map
                                    (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                                      W₂ B₂ U₀)
                                    rawHaar).addHaarScalarFactor (originalTupleVolume d))
                                let Ddet := Cdet * ε⁻¹
                                let Dvol := ((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet
                                let Cprior := ENNReal.ofReal Kprior * Dvol
                                Cprior < ∞ ∧
                                  (originalEdgeFamilyPrior (V := reverseVertex W₂)
                                    (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                    density).restrict (sourceChart '' V) ≤
                                      Cprior •
                                        (Measure.map sourceChart
                                          (coordinateSourceMeasure.restrict V)).restrict
                                            (sourceChart '' V) := by
  intro center pivotNext signedBox weightedBox passiveSource RawTuple EdgeFamily
    Y rawMap jacobianDensity baseJ sourceChart readback sourceDensity
    coordinateSourceMeasure rawDetChart rawSourceSet p13SourceSet d originalVolume
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource,
          RawTuple, EdgeFamily, Y, rawMap, jacobianDensity, baseJ,
          sourceChart, readback, sourceDensity, coordinateSourceMeasure,
          rawDetChart, rawSourceSet, p13SourceSet, d, originalVolume] using
          exists_open_subset_originalEdgeFamilyPrior_restrict_sourceChart_image_le_smul_sourceImageReference_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceImageDensity_image_lower_priorDensity_image_upper
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceImageDensity passiveMeasure Rres G hGopen hz₀G) with
    ⟨V, hVopen, hz₀V, hVG, hleftV, hsource_injV, hsource_contOnV,
      hsource_imageV, himage_p13V, hprior_package⟩
  have hleftV' : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleftV z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext hz
  have himage_p13V' : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    simpa [sourceChart, p13SourceSet, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13V (sourceChart z) z.A1passive z.F2 z.A3passive
        z.Ctop z.F3 z.yNext hzV rfl
  refine ⟨V, hVopen, hz₀V, hVG, hleftV', hsource_injV, hsource_contOnV,
    hsource_imageV, himage_p13V', ?_⟩
  intro rawHaar _instRawHaar Cdet ε hdet_dom hCdet hsource_input_lower
    hε_ne_zero hε_ne_top density Kprior hprior_input_upper cHaar Ddet Dvol Cprior
  have hsource_image_lower :
      ∀ E ∈ sourceChart '' V, ε ≤ sourceImageDensity E := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    exact hsource_input_lower (sourceChart z) ⟨z, hVG hzV, rfl⟩
  have hprior_image_upper :
      ∀ E ∈ sourceChart '' V, density E ≤ Kprior := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    exact hprior_input_upper (sourceChart z) ⟨z, hVG hzV, rfl⟩
  have hsource_image_lower' :
      ∀ E a a_1 a_2 a_3 b b_1,
        ((a, a_1, a_2, a_3, b), b_1) ∈ V →
          sourceChart ((a, a_1, a_2, a_3, b), b_1) = E →
            ε ≤ sourceImageDensity E := by
    intro E a a_1 a_2 a_3 b b_1 hzV hEq
    exact hsource_image_lower E ⟨((a, a_1, a_2, a_3, b), b_1), hzV, hEq⟩
  have hprior_image_upper' :
      ∀ E a a_1 a_2 a_3 b b_1,
        ((a, a_1, a_2, a_3, b), b_1) ∈ V →
          sourceChart ((a, a_1, a_2, a_3, b), b_1) = E →
            density E ≤ Kprior := by
    intro E a a_1 a_2 a_3 b b_1 hzV hEq
    exact hprior_image_upper E ⟨((a, a_1, a_2, a_3, b), b_1), hzV, hEq⟩
  simpa [cHaar, Ddet, Dvol, Cprior] using
    hprior_package rawHaar hdet_dom hCdet hsource_image_lower' hε_ne_zero
      hε_ne_top (density := density) (Kprior := Kprior) hprior_image_upper'

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This final wrapper elaborates the direct finite-integral socket plus the same-shrink bridge.
/-- Original edge-family priors feed into the Case 2 finite-integral socket
from determinant-chart reverse domination and a lower source-density bound.

This is the determinant-side analogue of the raw-source domination wrapper:
for chart pieces inside the actual source-chart image, determinant domination
plus a same-shrink lower bound for the source density supplies the
original-volume readback domination required by the direct finite-integral
front end.

The determinant-side domination and source-density lower bound remain
chart-piece hypotheses.  This theorem does not prove determinant-chart Haar
transport, raw-order Haar transport, original source-prior transport,
source-image coverage, source-rank coverage, normal crossings, pole order, or
RLCT extraction. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_originalVolume_readback_invHaar_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta.PassiveFields
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀)
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin 2 → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W₂ B₂ U₀ hU₀
        ((fun p : Fin 2 ↦
          LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)) :
          ∀ p : Fin 2,
            reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)
        (fun E :
            (∀ p : Fin 2,
              reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ↦ E)
        H r rEdge)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hpassive_lt_top : passiveMeasure Set.univ < ∞)
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ))
    [m.IsAddHaarMeasure]
    {ν :
      Measure
        (EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)))}
    [ν.IsAddHaarMeasure] [SFinite ν]
    {loss :
      (∀ p : Fin 2,
        reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ×
        EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)) → ℝ}
    {t R c : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (hR : 0 < R) (hc : 0 < c) (ht : 0 < t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      Measure.pi
        (fun i : Case2PassiveTheta.Center n S J =>
          volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      signedBox.withDensity
        (fun y : Case2PassiveTheta.Center n S J → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let passiveSource := passiveMeasure.prod weightedBox
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let jacobianDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ := passiveSource.withDensity jacobianDensity
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily →
        Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ eNext e
    let sourceDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let base : EdgeFamily :=
      fun p : Fin 2 ↦ LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)
    let ρreg :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
    let rawDetChart :
        Set (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ) :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let p13SourceChart :
        TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ →
          EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    let cHaar :=
      ((Measure.map
          (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
            W₂ B₂ U₀)
          m).addHaarScalarFactor (originalTupleVolume d))
    (∀ᶠ x in nhdsWithin base sourceStratum,
      ∀ u : EuclideanSpace ℝ ρreg,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
          c * (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) x) +
            aoyagiCoordinateSquareSum (fun i ↦ u i)) ≤ loss (x, u)) →
    ∃ W :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen W ∧ z₀ ∈ W ∧
        let sourceImageBase : Measure EdgeFamily :=
          Measure.map sourceChart (baseJ.restrict W)
        let sourceImageMeasure : Measure EdgeFamily :=
          sourceImageBase.withDensity sourceImageDensity
        AEMeasurable sourceChart (baseJ.restrict W) →
          AEMeasurable sourceImageDensity sourceImageBase →
            ∀ {Csrc : ℝ≥0∞},
              (∀ᵐ E ∂ sourceImageBase, sourceImageDensity E ≤ Csrc) →
                Csrc < ∞ →
                  ∃ U : Set EdgeFamily, IsOpen U ∧ base ∈ U ∧
                    ∃ V : Set
                      (Case2PassiveTheta
                        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
                      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ W ∧
                        (∀ z ∈ V, readback (sourceChart z) = z) ∧
                        Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
                        MeasurableSet (sourceChart '' V) ∧
                        (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                    let sourceLocal : Set EdgeFamily := U ∩ sourceStratum
                    MeasurableSet sourceLocal ∧
                      ∀ {chartPiece : Set EdgeFamily},
                        MeasurableSet chartPiece →
                          chartPiece ⊆ sourceLocal →
                            chartPiece ⊆ sourceChart '' V →
                              ∀ {Cdet ε : ℝ≥0∞},
                                m.restrict rawDetChart ≤
                                  Cdet • Measure.map Y (passiveSource.restrict V) →
                                  Cdet < ∞ →
                                    (∀ᵐ z ∂baseJ.restrict V,
                                      ε ≤ sourceDensity z) →
                                      ε ≠ 0 →
                                        ε ≠ ∞ →
                                          ∀ {density : EdgeFamily → ℝ}
                                            {Kprior : ℝ},
                                            (∀ᵐ E ∂(originalEdgeFamilyVolume
                                              (V := reverseVertex W₂)
                                              (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)).restrict
                                                chartPiece,
                                                density E ≤ Kprior) →
                                                    (∫⁻ z : EdgeFamily × EuclideanSpace ℝ ρreg,
                                                      ENNReal.ofReal
                                                        ((Metric.ball
                                                          (0 : EuclideanSpace ℝ ρreg) R).indicator
                                                          (fun u ↦
                                                            (loss (z.1, u)) ^
                                                              (-(t +
                                                                (aoyagiTheorem2RegularVariableCount
                                                                    2 H r : ℝ) /
                                                                  2))) z.2) ∂
                                                      ((originalEdgeFamilyPrior (V := reverseVertex W₂)
                                                        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                                        density).restrict chartPiece).prod ν) <
                                                        ∞ := by
  intro center pivotNext signedBox weightedBox passiveSource Y jacobianDensity
    baseJ EdgeFamily sourceChart readback sourceDensity coordinateSourceMeasure
    base ρreg sourceStratum rawDetChart p13SourceSet p13SourceChart d
    originalVolume cHaar hloss
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource, Y,
          jacobianDensity, baseJ, EdgeFamily, sourceChart, readback,
          sourceDensity, coordinateSourceMeasure, base, ρreg, sourceStratum,
          rawDetChart, p13SourceChart, d, cHaar] using
          exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_originalVolume_readback_le_smul_coordinateSourceMeasure_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
            (ν := ν) (loss := loss) (t := t) (R := R) (c := c)
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceData sourceImageDensity passiveMeasure
            hpassive_lt_top m Rres hR hc ht hRres hcrit hloss) with
    ⟨W, hWopen, hz₀W, hsocket⟩
  refine ⟨W, hWopen, hz₀W, ?_⟩
  intro sourceImageBase sourceImageMeasure hsourceChart hsourceImageDensity
    Csrc hsourceImageDensity_le hCsrc
  have hsourceChart' :
      AEMeasurable
        (case2PassiveThetaEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e)
        (((passiveMeasure.prod weightedBox).withDensity jacobianDensity).restrict W) := by
    simpa [sourceChart, baseJ, passiveSource] using hsourceChart
  have hsourceImageDensity' :
      AEMeasurable sourceImageDensity
        (Measure.map
          (case2PassiveThetaEndpointSourceChart
            W₂ B₂ n hS hcont hnext hU₀ eNext e)
          (((passiveMeasure.prod weightedBox).withDensity jacobianDensity).restrict W)) := by
    simpa [sourceImageBase, sourceChart, baseJ, passiveSource] using
      hsourceImageDensity
  rcases
      hsocket hsourceChart' hsourceImageDensity'
        (Csrc := Csrc) hsourceImageDensity_le hCsrc with
    ⟨U, hUopen, hbaseU, hfinite⟩
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource, Y,
          jacobianDensity, baseJ, EdgeFamily, sourceChart, readback,
          sourceDensity, coordinateSourceMeasure, rawDetChart, p13SourceSet,
          d, originalVolume] using
          exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceImageDensity passiveMeasure Rres W
            hWopen hz₀W) with
    ⟨V, hVopen, hz₀V, hVW, hleft, hsource_inj, hsource_contOn,
      hsource_image, himage_p13, hreadback_bridge⟩
  have hleftV : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext hz
  have himage_p13V : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hz, rfl⟩
    simpa [sourceChart, p13SourceSet, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13 (sourceChart z) z.A1passive z.F2 z.A3passive z.Ctop
        z.F3 z.yNext hz rfl
  refine ⟨U, hUopen, hbaseU, V, hVopen, hz₀V, hVW, hleftV,
    hsource_inj, hsource_contOn, hsource_image, himage_p13V, ?_⟩
  dsimp only at hfinite ⊢
  refine ⟨hfinite.1, ?_⟩
  intro chartPiece hchartPiece_meas hchartPiece_sub_local hchartPiece_sub_image
    Cdet ε hdet_dom hCdet hsource_lower hε_ne_zero hε_ne_top density
    Kprior hdensity
  let Ddet : ℝ≥0∞ := Cdet * ε⁻¹
  let Dvol : ℝ≥0∞ := (((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet)
  have hpiece_U : chartPiece ⊆ U := fun E hE ↦
    (hchartPiece_sub_local hE).1
  have hpiece_sourceStratum : chartPiece ⊆ sourceStratum := fun E hE ↦
    (hchartPiece_sub_local hE).2
  have hpiece_p13 : chartPiece ⊆ p13SourceSet := fun E hE ↦
    himage_p13V E (hchartPiece_sub_image hE)
  have hright : ∀ E ∈ chartPiece, readback E ∈ W ∧ sourceChart (readback E) = E := by
    intro E hE
    rcases hchartPiece_sub_image hE with ⟨z, hzV, rfl⟩
    constructor
    · rw [hleftV z hzV]
      exact hVW hzV
    · rw [hleftV z hzV]
  have hreadback_volume :
      AEMeasurable readback (originalVolume.restrict chartPiece) ∧
        Measure.map readback (originalVolume.restrict chartPiece) ≤
          Dvol • coordinateSourceMeasure.restrict W := by
    simpa [rawDetChart, d, originalVolume, cHaar, Ddet, Dvol] using
      hreadback_bridge m chartPiece (Cdet := Cdet) (ε := ε)
        hchartPiece_meas hchartPiece_sub_image hdet_dom hCdet
        hsource_lower hε_ne_zero hε_ne_top
  have hDdet : Ddet < ∞ := by
    dsimp [Ddet]
    exact ENNReal.mul_lt_top hCdet
      (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hε_ne_zero))
  have hDvol : Dvol < ∞ := by
    dsimp [Dvol]
    exact ENNReal.mul_lt_top (by simp) hDdet
  simpa [originalVolume, Dvol] using
    hfinite.2 hchartPiece_meas hpiece_U hpiece_sourceStratum
      (by simpa [p13SourceSet] using hpiece_p13)
      (by simpa [sourceChart, readback] using hright)
      (density := density) (Kprior := Kprior) hdensity
      (Csource := Dvol)
      (by simpa [EdgeFamily, readback, originalVolume] using hreadback_volume.1)
      (by simpa [EdgeFamily, readback, originalVolume] using hreadback_volume.2)
      hDvol

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This corollary replays the large determinant-domination finite-integral wrapper through dependent lets.
/-- Canonical-chart-piece version of the determinant-domination finite-integral wrapper.

The chart piece is fixed to `(U ∩ sourceStratum) ∩ sourceChart '' V`, the natural
p.13 local piece produced by the source neighborhood and the same-shrink
passive-theta chart image.  The determinant-side domination and source-density
lower bound remain explicit hypotheses. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_sourceLocal_inter_sourceChart_image_originalVolume_readback_invHaar_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta.PassiveFields
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀)
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin 2 → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W₂ B₂ U₀ hU₀
        ((fun p : Fin 2 ↦
          LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)) :
          ∀ p : Fin 2,
            reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)
        (fun E :
            (∀ p : Fin 2,
              reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ↦ E)
        H r rEdge)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hpassive_lt_top : passiveMeasure Set.univ < ∞)
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ))
    [m.IsAddHaarMeasure]
    {ν :
      Measure
        (EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)))}
    [ν.IsAddHaarMeasure] [SFinite ν]
    {loss :
      (∀ p : Fin 2,
        reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ×
        EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)) → ℝ}
    {t R c : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (hR : 0 < R) (hc : 0 < c) (ht : 0 < t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      Measure.pi
        (fun i : Case2PassiveTheta.Center n S J =>
          volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      signedBox.withDensity
        (fun y : Case2PassiveTheta.Center n S J → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let passiveSource := passiveMeasure.prod weightedBox
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let jacobianDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ := passiveSource.withDensity jacobianDensity
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily →
        Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ eNext e
    let sourceDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let base : EdgeFamily :=
      fun p : Fin 2 ↦ LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)
    let ρreg :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
    let rawDetChart :
        Set (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ) :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let p13SourceChart :
        TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ →
          EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    let cHaar :=
      ((Measure.map
          (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
            W₂ B₂ U₀)
          m).addHaarScalarFactor (originalTupleVolume d))
    (∀ᶠ x in nhdsWithin base sourceStratum,
      ∀ u : EuclideanSpace ℝ ρreg,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
          c * (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) x) +
            aoyagiCoordinateSquareSum (fun i ↦ u i)) ≤ loss (x, u)) →
    ∃ W :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen W ∧ z₀ ∈ W ∧
        let sourceImageBase : Measure EdgeFamily :=
          Measure.map sourceChart (baseJ.restrict W)
        let sourceImageMeasure : Measure EdgeFamily :=
          sourceImageBase.withDensity sourceImageDensity
        AEMeasurable sourceChart (baseJ.restrict W) →
          AEMeasurable sourceImageDensity sourceImageBase →
            ∀ {Csrc : ℝ≥0∞},
              (∀ᵐ E ∂ sourceImageBase, sourceImageDensity E ≤ Csrc) →
                Csrc < ∞ →
                  ∃ U : Set EdgeFamily, IsOpen U ∧ base ∈ U ∧
                    ∃ V : Set
                      (Case2PassiveTheta
                        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
                      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ W ∧
                        (∀ z ∈ V, readback (sourceChart z) = z) ∧
                        Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
                        MeasurableSet (sourceChart '' V) ∧
                        (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                    let sourceLocal : Set EdgeFamily := U ∩ sourceStratum
                    let chartPiece : Set EdgeFamily := sourceLocal ∩ sourceChart '' V
                    MeasurableSet sourceLocal ∧ MeasurableSet chartPiece ∧
                      ∀ {Cdet ε : ℝ≥0∞},
                        m.restrict rawDetChart ≤
                          Cdet • Measure.map Y (passiveSource.restrict V) →
                          Cdet < ∞ →
                            (∀ᵐ z ∂baseJ.restrict V, ε ≤ sourceDensity z) →
                              ε ≠ 0 →
                                ε ≠ ∞ →
                                  ∀ {density : EdgeFamily → ℝ} {Kprior : ℝ},
                                    (∀ᵐ E ∂(originalEdgeFamilyVolume
                                      (V := reverseVertex W₂)
                                      (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)).restrict
                                        chartPiece,
                                        density E ≤ Kprior) →
                                            (∫⁻ z : EdgeFamily × EuclideanSpace ℝ ρreg,
                                              ENNReal.ofReal
                                                ((Metric.ball
                                                  (0 : EuclideanSpace ℝ ρreg) R).indicator
                                                  (fun u ↦
                                                    (loss (z.1, u)) ^
                                                      (-(t +
                                                        (aoyagiTheorem2RegularVariableCount
                                                            2 H r : ℝ) /
                                                          2))) z.2) ∂
                                              ((originalEdgeFamilyPrior (V := reverseVertex W₂)
                                                (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                                density).restrict chartPiece).prod ν) <
                                                ∞ := by
  intro center pivotNext signedBox weightedBox passiveSource Y jacobianDensity
    baseJ EdgeFamily sourceChart readback sourceDensity coordinateSourceMeasure
    base ρreg sourceStratum rawDetChart p13SourceSet p13SourceChart d
    originalVolume cHaar hloss
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource, Y,
          jacobianDensity, baseJ, EdgeFamily, sourceChart, readback,
          sourceDensity, coordinateSourceMeasure, base, ρreg, sourceStratum,
          rawDetChart, p13SourceChart, d, cHaar] using
          exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_originalVolume_readback_invHaar_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
            (ν := ν) (loss := loss) (t := t) (R := R) (c := c)
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceData sourceImageDensity passiveMeasure
            hpassive_lt_top m Rres hR hc ht hRres hcrit hloss) with
    ⟨W, hWopen, hz₀W, hsocket⟩
  refine ⟨W, hWopen, hz₀W, ?_⟩
  intro sourceImageBase sourceImageMeasure hsourceChart hsourceImageDensity
    Csrc hsourceImageDensity_le hCsrc
  have hsourceChart' :
      AEMeasurable
        (case2PassiveThetaEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e)
        (((passiveMeasure.prod weightedBox).withDensity jacobianDensity).restrict W) := by
    simpa [sourceChart, baseJ, passiveSource] using hsourceChart
  have hsourceImageDensity' :
      AEMeasurable sourceImageDensity
        (Measure.map
          (case2PassiveThetaEndpointSourceChart
            W₂ B₂ n hS hcont hnext hU₀ eNext e)
          (((passiveMeasure.prod weightedBox).withDensity jacobianDensity).restrict W)) := by
    simpa [sourceImageBase, sourceChart, baseJ, passiveSource] using
      hsourceImageDensity
  rcases hsocket hsourceChart' hsourceImageDensity'
      (Csrc := Csrc) hsourceImageDensity_le hCsrc with
    ⟨U, hUopen, hbaseU, V, hVopen, hz₀V, hVW, hleft, hsource_inj,
      hsource_contOn, hsource_image, himage_p13, hfinite⟩
  have hleftV : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext hz
  have himage_p13V : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hz, rfl⟩
    simpa [sourceChart, p13SourceSet, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13 (sourceChart z) z.A1passive z.F2 z.A3passive z.Ctop
        z.F3 z.yNext hz rfl
  refine ⟨U, hUopen, hbaseU, V, hVopen, hz₀V, hVW, hleftV, hsource_inj,
    hsource_contOn, hsource_image, himage_p13V, ?_⟩
  dsimp only at ⊢
  have hchartPiece_meas :
      MeasurableSet ((U ∩ sourceStratum) ∩ sourceChart '' V) :=
    by simpa using hfinite.1.inter hsource_image
  refine ⟨by simpa using hfinite.1, hchartPiece_meas, ?_⟩
  intro Cdet ε hdet_dom hCdet hsource_lower hε_ne_zero hε_ne_top
    density Kprior hdensity
  have hpiece_U : ((U ∩ sourceStratum) ∩ sourceChart '' V) ⊆ U := fun E hE ↦
    hE.1.1
  have hpiece_sourceStratum :
      ((U ∩ sourceStratum) ∩ sourceChart '' V) ⊆ sourceStratum := fun E hE ↦
    hE.1.2
  have hpiece_image :
      ((U ∩ sourceStratum) ∩ sourceChart '' V) ⊆ sourceChart '' V := fun E hE ↦
    hE.2
  simpa [EdgeFamily, ρreg, neg_add, add_comm, add_left_comm, add_assoc] using
    hfinite.2 hchartPiece_meas
      hpiece_U hpiece_sourceStratum hpiece_image
      (Cdet := Cdet) (ε := ε) hdet_dom hCdet hsource_lower
      hε_ne_zero hε_ne_top (density := density) (Kprior := Kprior) hdensity

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This wrapper replays the canonical determinant theorem and converts an image lower bound to an a.e. bound.
/-- Canonical-chart-piece determinant wrapper using a source-image lower bound.

The source-density lower bound is stated pointwise on the returned image
`sourceChart '' V`; support of `baseJ.restrict V` converts this to the a.e.
lower bound needed by the determinant-domination wrapper. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_sourceLocal_inter_sourceChart_image_originalVolume_readback_invHaar_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceImageDensity_image_lower_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta.PassiveFields
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀)
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin 2 → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W₂ B₂ U₀ hU₀
        ((fun p : Fin 2 ↦
          LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)) :
          ∀ p : Fin 2,
            reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)
        (fun E :
            (∀ p : Fin 2,
              reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ↦ E)
        H r rEdge)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hpassive_lt_top : passiveMeasure Set.univ < ∞)
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ))
    [m.IsAddHaarMeasure]
    {ν :
      Measure
        (EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)))}
    [ν.IsAddHaarMeasure] [SFinite ν]
    {loss :
      (∀ p : Fin 2,
        reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ×
        EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)) → ℝ}
    {t R c : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (hR : 0 < R) (hc : 0 < c) (ht : 0 < t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      Measure.pi
        (fun i : Case2PassiveTheta.Center n S J =>
          volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      signedBox.withDensity
        (fun y : Case2PassiveTheta.Center n S J → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let passiveSource := passiveMeasure.prod weightedBox
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let jacobianDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ := passiveSource.withDensity jacobianDensity
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily →
        Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ eNext e
    let sourceDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let base : EdgeFamily :=
      fun p : Fin 2 ↦ LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)
    let ρreg :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
    let rawDetChart :
        Set (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ) :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let p13SourceChart :
        TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ →
          EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    let cHaar :=
      ((Measure.map
          (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
            W₂ B₂ U₀)
          m).addHaarScalarFactor (originalTupleVolume d))
    (∀ᶠ x in nhdsWithin base sourceStratum,
      ∀ u : EuclideanSpace ℝ ρreg,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
          c * (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) x) +
            aoyagiCoordinateSquareSum (fun i ↦ u i)) ≤ loss (x, u)) →
    ∃ W :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen W ∧ z₀ ∈ W ∧
        let sourceImageBase : Measure EdgeFamily :=
          Measure.map sourceChart (baseJ.restrict W)
        let sourceImageMeasure : Measure EdgeFamily :=
          sourceImageBase.withDensity sourceImageDensity
        AEMeasurable sourceChart (baseJ.restrict W) →
          AEMeasurable sourceImageDensity sourceImageBase →
            ∀ {Csrc : ℝ≥0∞},
              (∀ᵐ E ∂ sourceImageBase, sourceImageDensity E ≤ Csrc) →
                Csrc < ∞ →
                  ∃ U : Set EdgeFamily, IsOpen U ∧ base ∈ U ∧
                    ∃ V : Set
                      (Case2PassiveTheta
                        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
                      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ W ∧
                        (∀ z ∈ V, readback (sourceChart z) = z) ∧
                        Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
                        MeasurableSet (sourceChart '' V) ∧
                        (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                    let sourceLocal : Set EdgeFamily := U ∩ sourceStratum
                    let chartPiece : Set EdgeFamily := sourceLocal ∩ sourceChart '' V
                    MeasurableSet sourceLocal ∧ MeasurableSet chartPiece ∧
                      ∀ {Cdet ε : ℝ≥0∞},
                        m.restrict rawDetChart ≤
                          Cdet • Measure.map Y (passiveSource.restrict V) →
                          Cdet < ∞ →
                            (∀ E ∈ sourceChart '' V, ε ≤ sourceImageDensity E) →
                              ε ≠ 0 →
                                ε ≠ ∞ →
                                  ∀ {density : EdgeFamily → ℝ} {Kprior : ℝ},
                                    (∀ᵐ E ∂(originalEdgeFamilyVolume
                                      (V := reverseVertex W₂)
                                      (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)).restrict
                                        chartPiece,
                                        density E ≤ Kprior) →
                                            (∫⁻ z : EdgeFamily × EuclideanSpace ℝ ρreg,
                                              ENNReal.ofReal
                                                ((Metric.ball
                                                  (0 : EuclideanSpace ℝ ρreg) R).indicator
                                                  (fun u ↦
                                                    (loss (z.1, u)) ^
                                                      (-(t +
                                                        (aoyagiTheorem2RegularVariableCount
                                                            2 H r : ℝ) /
                                                          2))) z.2) ∂
                                              ((originalEdgeFamilyPrior (V := reverseVertex W₂)
                                                (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                                density).restrict chartPiece).prod ν) <
                                                ∞ := by
  intro center pivotNext signedBox weightedBox passiveSource Y jacobianDensity
    baseJ EdgeFamily sourceChart readback sourceDensity coordinateSourceMeasure
    base ρreg sourceStratum rawDetChart p13SourceSet p13SourceChart d
    originalVolume cHaar hloss
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource, Y,
          jacobianDensity, baseJ, EdgeFamily, sourceChart, readback,
          sourceDensity, coordinateSourceMeasure, base, ρreg, sourceStratum,
          rawDetChart, p13SourceChart, d, cHaar] using
          exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_sourceLocal_inter_sourceChart_image_originalVolume_readback_invHaar_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
            (ν := ν) (loss := loss) (t := t) (R := R) (c := c)
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceData sourceImageDensity passiveMeasure
            hpassive_lt_top m Rres hR hc ht hRres hcrit hloss) with
    ⟨W, hWopen, hz₀W, hsocket⟩
  refine ⟨W, hWopen, hz₀W, ?_⟩
  intro sourceImageBase sourceImageMeasure hsourceChart hsourceImageDensity
    Csrc hsourceImageDensity_le hCsrc
  have hsourceChart' :
      AEMeasurable
        (case2PassiveThetaEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e)
        (((passiveMeasure.prod weightedBox).withDensity jacobianDensity).restrict W) := by
    simpa [sourceChart, baseJ, passiveSource] using hsourceChart
  have hsourceImageDensity' :
      AEMeasurable sourceImageDensity
        (Measure.map
          (case2PassiveThetaEndpointSourceChart
            W₂ B₂ n hS hcont hnext hU₀ eNext e)
          (((passiveMeasure.prod weightedBox).withDensity jacobianDensity).restrict W)) := by
    simpa [sourceImageBase, sourceChart, baseJ, passiveSource] using
      hsourceImageDensity
  rcases hsocket hsourceChart' hsourceImageDensity'
      (Csrc := Csrc) hsourceImageDensity_le hCsrc with
    ⟨U, hUopen, hbaseU, V, hVopen, hz₀V, hVW, hleft, hsource_inj,
      hsource_contOn, hsource_image, himage_p13, hfinite⟩
  have hleftV : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext hz
  have himage_p13V : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hz, rfl⟩
    simpa [sourceChart, p13SourceSet, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13 (sourceChart z) z.A1passive z.F2 z.A3passive z.Ctop
        z.F3 z.yNext hz rfl
  refine ⟨U, hUopen, hbaseU, V, hVopen, hz₀V, hVW, hleftV, hsource_inj,
    hsource_contOn, hsource_image, himage_p13V, ?_⟩
  dsimp only at hfinite ⊢
  refine ⟨hfinite.1, hfinite.2.1, ?_⟩
  intro Cdet ε hdet_dom hCdet hsource_image_lower hε_ne_zero hε_ne_top
    density Kprior hdensity
  have hsource_lower :
      ∀ᵐ z ∂baseJ.restrict V, ε ≤ sourceDensity z := by
    simpa [sourceDensity] using
      ae_restrict_comp_lower_of_forall_image_lower
        (μ := baseJ) (V := V) (f := sourceChart)
        (g := sourceImageDensity) (ε := ε)
        hVopen.measurableSet hsource_image_lower
  simpa [EdgeFamily, ρreg, sourceStratum, sourceChart, neg_add,
    add_comm, add_left_comm, add_assoc] using
    hfinite.2.2 hdet_dom hCdet hsource_lower hε_ne_zero hε_ne_top
      (density := density) (Kprior := Kprior) hdensity

end PaperEndpointFixedBaseRegularCoordinateSourceData
end Aoyagi
end DLN
end DLNFibre
