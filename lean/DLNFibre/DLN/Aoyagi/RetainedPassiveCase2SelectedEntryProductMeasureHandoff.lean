import DLNFibre.DLN.Aoyagi.RegularSuspensionProductMeasureHandoff
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure

/-!
# Case 2 selected-entry product-coordinate measure handoff

This file specializes the reduced p.13 product-coordinate source-reference
domination handoff to the endpoint-transported Case 2 selected-entry source
chart, using value coordinates on the fixed nonzero-pivot locus.

The theorem still assumes the weighted product-chart identity and density
bound.  It proves the selected-entry source measurability, continuity,
determinant-chart, and residual readback inputs needed by the generic product
handoff.  It does not identify an external/original prior, prove ambient raw
Haar transport, construct normal crossings, compute pole order, or extract
RLCT.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DLNFibre
namespace DLN
namespace Aoyagi

namespace PaperEndpointFixedBaseRegularCoordinateSourceData

universe v

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Product-coordinate formal-product/source-reference domination for the
endpoint-transported Case 2 selected-entry source chart in value coordinates.

The source is the punctured value-coordinate set
`{value | value pivotNext ≠ 0}`.  The source chart first applies the fixed
selected-entry inverse `preimageOfPivotNeZero pivotNext` and then the existing
endpoint-transported retained-passive p.13 source chart. -/
theorem exists_pos_radius_le_case2EndpointTransport_selectedEntryValue_productCoordinate_formalProductMeasure_restrict_le_smul_sourceReference_of_sourceChart_withDensity
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    {Rmax : ℝ} (hRmax : 0 < Rmax) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      ⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
          n hS hnext⟩
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        (center → ℝ) →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun yNext ↦
        (case2PostPivotSelectedEntryRetainedPassiveData
          (ρ := Fin (Module.finrank ℝ U₀))
          n hS hcont hnext yNext eNext).endpointTransport e
    let sourceChart : (center → ℝ) → EdgeFamily :=
      fun value ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
          W₂ B₂ U₀ hU₀
          (retainedData
            (SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero
              pivotNext value))
    let source : Set (center → ℝ) :=
      {value | value pivotNext ≠ 0}
    ∃ R : ℝ, 0 < R ∧ R ≤ Rmax ∧
      let ρ := Fin (Module.finrank ℝ U₀)
      let κ := throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
      let Coord :=
        AoyagiRegularBlockCoordinateIndex ρ (κ (Fin.last 2)) (κ 0)
      let CedgeProd :=
        paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
          W₂ B₂ U₀ hU₀ sourceChart
      let domain := source ×ˢ Metric.ball (0 : EuclideanSpace ℝ Coord) R
      ∀ (thetaReference : Measure ((center → ℝ) × EuclideanSpace ℝ Coord))
          (formalProductMeasure : Measure EdgeFamily)
          (chartPiece : Set EdgeFamily) (density : EdgeFamily → ℝ≥0∞)
          (c : ℝ≥0∞),
        MeasurableSet chartPiece →
          AEMeasurable density
            (Measure.map CedgeProd (thetaReference.restrict domain)) →
          formalProductMeasure.restrict chartPiece =
            (Measure.map CedgeProd
              ((thetaReference.withDensity
                (fun z ↦ density (CedgeProd z))).restrict
                domain)).restrict chartPiece →
          (∀ᵐ E ∂(Measure.map CedgeProd
              (thetaReference.restrict domain)).restrict chartPiece,
            density E ≤ c) →
          formalProductMeasure.restrict chartPiece ≤
            c • Measure.map CedgeProd (thetaReference.restrict domain) := by
  intro center pivotNext EdgeFamily retainedData sourceChart source
  let residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0) ≃ center :=
    case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
      n S (J + 1) (e (Fin.last 2)).symm ((e 0).symm.trans eNext)
  let baseReadback :
      (AoyagiResidualBlockCoordinateIndex
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0) → ℝ) →
        center → ℝ :=
    fun coord i ↦ coord (residualCoordEquiv.symm i)
  have hsource : MeasurableSet source := by
    simpa [source] using
      SelectedEntrySignedBox.CenterCoord.measurableSet_pivot_ne_zero pivotNext
  have hsourceChart_direct :
      Continuous
        (fun yNext : center → ℝ ↦
          paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
            W₂ B₂ U₀ hU₀ (retainedData yNext)) := by
    simpa [center, EdgeFamily, retainedData] using
      continuous_retainedPassiveP13SourceEdgeFamilyOfData_of_case2EndpointTransport
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
  have hCedgeBase :
      ∀ value ∈ source, ContinuousAt sourceChart value := by
    intro value hvalue
    have hpre :
        ContinuousAt
          (SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero pivotNext)
          value :=
      SelectedEntrySignedBox.CenterCoord.continuousAt_preimageOfPivotNeZero
        pivotNext (by simpa [source] using hvalue)
    simpa [sourceChart] using
      hsourceChart_direct.continuousAt.comp hpre
  have hchart :
      ∀ value ∈ source, ∀ (p : Fin 2)
          (hpj : p.succ ≤ (Fin.last 2 : Fin 3)),
        identityCornerDetChart
          (ChartLocalSuffixState.transformedEdge
            (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
              (fun q : Fin 2 ↦
                (sourceChart value q :
                  reverseVertex W₂ q.castSucc →ₗ[ℝ] reverseVertex W₂ q.succ))) p
            (ChartLocalSuffixState.suffixState
              (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
                (fun q : Fin 2 ↦
                  (sourceChart value q :
                    reverseVertex W₂ q.castSucc →ₗ[ℝ] reverseVertex W₂ q.succ)))
              (Fin.last 2) p.succ hpj)) := by
    intro value _hvalue p hpj
    have hpre :
        sourceChart value ∈
          paperEndpointFixedBaseRetainedPassiveP13LocalSource
            W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) := by
      have hlocal :=
        (retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData
          W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e).1
          (SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero
            pivotNext value)
      simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart] using
        hlocal
    have hrecursive :
        ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceRecursiveDetChart
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
            (fun q : Fin 2 ↦
              (sourceChart value q :
                reverseVertex W₂ q.castSucc →ₗ[ℝ] reverseVertex W₂ q.succ))) := by
      simpa [paperEndpointFixedBaseRetainedPassiveP13LocalSource] using hpre
    exact hrecursive p hpj
  have hbaseReadback :
      ∀ value ∈ source,
        baseReadback
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ sourceChart value) =
          value := by
    intro value hvalue
    funext i
    have hresidual_id :
        paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀
            (fun E : EdgeFamily ↦ E) (sourceChart value) =
          paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ sourceChart value :=
      paperEndpointFixedBaseResidualBlockCoordinateMap_congr_point
        (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀
        (Cedge := fun E : EdgeFamily ↦ E) (Cedge' := sourceChart)
        (x := sourceChart value) (y := value) rfl
    have hcoord :=
      paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_value_of_case2EndpointTransport_sourceEdgeFamilyOfData_preimageOfPivotNeZero
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        value (by simpa [source] using hvalue) (residualCoordEquiv.symm i)
    calc
      baseReadback
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ sourceChart value) i =
          paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ sourceChart value
            (residualCoordEquiv.symm i) := by
            rfl
      _ =
          paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
            (sourceChart value) (residualCoordEquiv.symm i) := by
            rw [← congrFun hresidual_id (residualCoordEquiv.symm i)]
      _ = value (residualCoordEquiv (residualCoordEquiv.symm i)) := by
            simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart,
              residualCoordEquiv] using hcoord
      _ = value i := by
            exact congrArg value (residualCoordEquiv.apply_symm_apply i)
  rcases
      exists_pos_radius_le_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_formalProductMeasure_restrict_le_smul_sourceReference_of_sourceChart_withDensity_of_residualReadback
        (M := 0) W₂ B₂ U₀ hU₀ sourceChart (source := source) (Rmax := Rmax)
        hsource hRmax hCedgeBase hchart baseReadback hbaseReadback with
    ⟨R, hR, hRle, hbridge⟩
  refine ⟨R, hR, hRle, ?_⟩
  intro ρ κ Coord CedgeProd domain
  simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart, source,
    residualCoordEquiv, baseReadback, ρ, κ, Coord, CedgeProd, domain] using
    hbridge

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Selected-entry weighted source pushforward through the endpoint-transported
Case 2 p.13 product-coordinate chart.

For a selected-entry source box and the small regular-coordinate ball returned
by the p.13 chart/readback package, pushing the weighted selected-entry source
measure through `(y,u) ↦ CedgeProd (chartMap pivotNext y,u)` agrees with
pushing the value-coordinate reference measure through `CedgeProd`.

This is only the selected-entry source/reference identity for the reduced
p.13 product chart.  It does not identify formal-product Haar, determinant/raw
Haar, or the original prior. -/
theorem exists_pos_radius_le_case2EndpointTransport_selectedEntryValue_productCoordinate_map_selectedEntrySource_eq_map_valueReference
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    {Rmax : ℝ} (hRmax : 0 < Rmax) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      ⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
          n hS hnext⟩
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        (center → ℝ) →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun yNext ↦
        (case2PostPivotSelectedEntryRetainedPassiveData
          (ρ := Fin (Module.finrank ℝ U₀))
          n hS hcont hnext yNext eNext).endpointTransport e
    let sourceChart : (center → ℝ) → EdgeFamily :=
      fun value ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
          W₂ B₂ U₀ hU₀
          (retainedData
            (SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero
              pivotNext value))
    ∀ Rbox : center → ℝ,
    ∃ R : ℝ, 0 < R ∧ R ≤ Rmax ∧
      let ρ := Fin (Module.finrank ℝ U₀)
      let κ := throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
      let Coord :=
        AoyagiRegularBlockCoordinateIndex ρ (κ (Fin.last 2)) (κ 0)
      let CedgeProd :=
        paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
          W₂ B₂ U₀ hU₀ sourceChart
      let regularMeasure :=
        (volume : Measure (EuclideanSpace ℝ Coord)).restrict
          (Metric.ball (0 : EuclideanSpace ℝ Coord) R)
      let sourceSet :=
        SelectedEntrySignedBox.CenterCoord.signedBoxSet Rbox ∩
          {y : center → ℝ | y pivotNext ≠ 0}
      let valueImage :=
        SelectedEntrySignedBox.CenterCoord.chartMap pivotNext '' sourceSet
      Measure.map
          (fun z : (center → ℝ) × EuclideanSpace ℝ Coord =>
            CedgeProd
              (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1, z.2))
          ((((volume : Measure (center → ℝ)).restrict sourceSet).withDensity
            (fun y : center → ℝ =>
              ENNReal.ofReal
                (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))).prod
            regularMeasure) =
        Measure.map CedgeProd
          (((volume : Measure (center → ℝ)).restrict valueImage).prod
            regularMeasure) := by
  intro center pivotNext EdgeFamily retainedData sourceChart Rbox
  let source : Set (center → ℝ) :=
    {value | value pivotNext ≠ 0}
  let residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0) ≃ center :=
    case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
      n S (J + 1) (e (Fin.last 2)).symm ((e 0).symm.trans eNext)
  let baseReadback :
      (AoyagiResidualBlockCoordinateIndex
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0) → ℝ) →
        center → ℝ :=
    fun coord i ↦ coord (residualCoordEquiv.symm i)
  have hsource : MeasurableSet source := by
    simpa [source] using
      SelectedEntrySignedBox.CenterCoord.measurableSet_pivot_ne_zero pivotNext
  have hsourceChart_direct :
      Continuous
        (fun yNext : center → ℝ ↦
          paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
            W₂ B₂ U₀ hU₀ (retainedData yNext)) := by
    simpa [center, EdgeFamily, retainedData] using
      continuous_retainedPassiveP13SourceEdgeFamilyOfData_of_case2EndpointTransport
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
  have hCedgeBase :
      ∀ value ∈ source, ContinuousAt sourceChart value := by
    intro value hvalue
    have hpre :
        ContinuousAt
          (SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero pivotNext)
          value :=
      SelectedEntrySignedBox.CenterCoord.continuousAt_preimageOfPivotNeZero
        pivotNext (by simpa [source] using hvalue)
    simpa [sourceChart] using
      hsourceChart_direct.continuousAt.comp hpre
  have hchart :
      ∀ value ∈ source, ∀ (p : Fin 2)
          (hpj : p.succ ≤ (Fin.last 2 : Fin 3)),
        identityCornerDetChart
          (ChartLocalSuffixState.transformedEdge
            (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
              (fun q : Fin 2 ↦
                (sourceChart value q :
                  reverseVertex W₂ q.castSucc →ₗ[ℝ] reverseVertex W₂ q.succ))) p
            (ChartLocalSuffixState.suffixState
              (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
                (fun q : Fin 2 ↦
                  (sourceChart value q :
                    reverseVertex W₂ q.castSucc →ₗ[ℝ] reverseVertex W₂ q.succ)))
              (Fin.last 2) p.succ hpj)) := by
    intro value _hvalue p hpj
    have hpre :
        sourceChart value ∈
          paperEndpointFixedBaseRetainedPassiveP13LocalSource
            W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) := by
      have hlocal :=
        (retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData
          W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e).1
          (SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero
            pivotNext value)
      simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart] using
        hlocal
    have hrecursive :
        ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceRecursiveDetChart
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
            (fun q : Fin 2 ↦
              (sourceChart value q :
                reverseVertex W₂ q.castSucc →ₗ[ℝ] reverseVertex W₂ q.succ))) := by
      simpa [paperEndpointFixedBaseRetainedPassiveP13LocalSource] using hpre
    exact hrecursive p hpj
  have hbaseReadback :
      ∀ value ∈ source,
        baseReadback
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ sourceChart value) =
          value := by
    intro value hvalue
    funext i
    have hresidual_id :
        paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀
            (fun E : EdgeFamily ↦ E) (sourceChart value) =
          paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ sourceChart value :=
      paperEndpointFixedBaseResidualBlockCoordinateMap_congr_point
        (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀
        (Cedge := fun E : EdgeFamily ↦ E) (Cedge' := sourceChart)
        (x := sourceChart value) (y := value) rfl
    have hcoord :=
      paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_value_of_case2EndpointTransport_sourceEdgeFamilyOfData_preimageOfPivotNeZero
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        value (by simpa [source] using hvalue) (residualCoordEquiv.symm i)
    calc
      baseReadback
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ sourceChart value) i =
          paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ sourceChart value
            (residualCoordEquiv.symm i) := by
            rfl
      _ =
          paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
            (sourceChart value) (residualCoordEquiv.symm i) := by
            rw [← congrFun hresidual_id (residualCoordEquiv.symm i)]
      _ = value (residualCoordEquiv (residualCoordEquiv.symm i)) := by
            simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart,
              residualCoordEquiv] using hcoord
      _ = value i := by
            exact congrArg value (residualCoordEquiv.apply_symm_apply i)
  rcases
      exists_pos_radius_le_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_sourceChart_readback_package_of_residualReadback
        (M := 0) W₂ B₂ U₀ hU₀ sourceChart (source := source) (Rmax := Rmax)
        hsource hRmax hCedgeBase hchart baseReadback hbaseReadback with
    ⟨R, hR, hRle, hpackage⟩
  refine ⟨R, hR, hRle, ?_⟩
  intro ρ κ Coord CedgeProd regularMeasure sourceSet valueImage
  let domain := source ×ˢ Metric.ball (0 : EuclideanSpace ℝ Coord) R
  let productReadback : EdgeFamily → (center → ℝ) × EuclideanSpace ℝ Coord :=
    fun E ↦
      (baseReadback
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀
            (fun E' : EdgeFamily ↦ E') E),
        (EuclideanSpace.equiv Coord ℝ).symm
          (paperEndpointFixedBaseRegularBlockCoordinateMap
            (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀
            (fun E' : EdgeFamily ↦ E') E))
  have hpackage' :
      (∀ z ∈ domain, productReadback (CedgeProd z) = z) ∧
        Set.InjOn CedgeProd domain ∧
          ContinuousOn CedgeProd domain ∧
            (∀ thetaMeasure : Measure ((center → ℝ) × EuclideanSpace ℝ Coord),
              AEMeasurable CedgeProd (thetaMeasure.restrict domain)) ∧
              MeasurableSet (CedgeProd '' domain) ∧
                ∀ E ∈ CedgeProd '' domain,
                  productReadback E ∈ domain ∧ CedgeProd (productReadback E) = E := by
    simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart, source,
      residualCoordEquiv, baseReadback, ρ, κ, Coord, CedgeProd, productReadback, domain] using
      hpackage
  rcases hpackage' with ⟨_hleft, _hinj, hcont_prod, _haemeas_prod, _himage_prod, _hright⟩
  have hdomain : MeasurableSet domain := by
    simpa [domain] using
      hsource.prod
        (Metric.isOpen_ball.measurableSet :
          MeasurableSet (Metric.ball (0 : EuclideanSpace ℝ Coord) R))
  have hvalueImage_meas : MeasurableSet valueImage := by
    simpa [sourceSet, valueImage] using
      SelectedEntrySignedBox.CenterCoord.measurableSet_chartMap_image_signedBoxSet_inter_pivot_ne_zero
        pivotNext Rbox
  have hvalueImage_subset_source : valueImage ⊆ source := by
    intro value hvalue
    rcases hvalue with ⟨y, hy, rfl⟩
    exact
      (SelectedEntrySignedBox.CenterCoord.chartMap_mem_pivot_ne_zero_iff pivotNext y).2
        hy.2
  let valueReference : Measure ((center → ℝ) × EuclideanSpace ℝ Coord) :=
    ((volume : Measure (center → ℝ)).restrict valueImage).prod regularMeasure
  have hvalueReference_support : valueReference.restrict domain = valueReference := by
    have hleft_ae :
        ∀ᵐ value ∂(volume : Measure (center → ℝ)).restrict valueImage,
          value ∈ source := by
      filter_upwards [ae_restrict_mem hvalueImage_meas] with value hvalue
      exact hvalueImage_subset_source hvalue
    have hright_ae :
        ∀ᵐ u ∂regularMeasure,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ Coord) R := by
      simpa [regularMeasure] using
        (ae_restrict_mem
          (Metric.isOpen_ball.measurableSet :
            MeasurableSet (Metric.ball (0 : EuclideanSpace ℝ Coord) R)))
    have hmem : ∀ᵐ z ∂valueReference, z ∈ domain := by
      rw [Measure.ae_prod_mem_iff_ae_ae_mem hdomain]
      filter_upwards [hleft_ae] with value hvalue
      filter_upwards [hright_ae] with u hu
      exact ⟨hvalue, hu⟩
    exact Measure.restrict_eq_self_of_ae_mem hmem
  have hCedgeProd :
      AEMeasurable CedgeProd valueReference := by
    exact
      aemeasurable_of_continuousOn_of_measure_restrict_eq_self
        (sourceChart := CedgeProd) (μ := valueReference) (V := domain)
        hcont_prod hdomain hvalueReference_support
  simpa [regularMeasure, sourceSet, valueImage, valueReference] using
    (SelectedEntrySignedBox.CenterCoord.map_comp_prod_chartMap_id_restrict_nonzeroSignedBox_withDensity_sourceDensity_eq_map_restrict_image_prod_of_aemeasurable
      (β := EuclideanSpace ℝ Coord) (γ := EdgeFamily)
      pivotNext Rbox regularMeasure (F := CedgeProd) hCedgeProd)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Domain-shaped version of the selected-entry product-coordinate pushforward.

The value-reference product measure is already supported on the p.13 source
domain `source × ball(0,R)`, so the right side can be written in the generic
source-reference handoff form `Measure.map CedgeProd (valueReference.restrict
domain)`. -/
theorem exists_pos_radius_le_case2EndpointTransport_selectedEntryValue_productCoordinate_map_selectedEntrySource_eq_map_valueReference_restrict_domain
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    {Rmax : ℝ} (hRmax : 0 < Rmax) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      ⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
          n hS hnext⟩
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        (center → ℝ) →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun yNext ↦
        (case2PostPivotSelectedEntryRetainedPassiveData
          (ρ := Fin (Module.finrank ℝ U₀))
          n hS hcont hnext yNext eNext).endpointTransport e
    let sourceChart : (center → ℝ) → EdgeFamily :=
      fun value ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
          W₂ B₂ U₀ hU₀
          (retainedData
            (SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero
              pivotNext value))
    ∀ Rbox : center → ℝ,
    ∃ R : ℝ, 0 < R ∧ R ≤ Rmax ∧
      let ρ := Fin (Module.finrank ℝ U₀)
      let κ := throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
      let Coord :=
        AoyagiRegularBlockCoordinateIndex ρ (κ (Fin.last 2)) (κ 0)
      let CedgeProd :=
        paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
          W₂ B₂ U₀ hU₀ sourceChart
      let regularMeasure :=
        (volume : Measure (EuclideanSpace ℝ Coord)).restrict
          (Metric.ball (0 : EuclideanSpace ℝ Coord) R)
      let sourceSet :=
        SelectedEntrySignedBox.CenterCoord.signedBoxSet Rbox ∩
          {y : center → ℝ | y pivotNext ≠ 0}
      let valueImage :=
        SelectedEntrySignedBox.CenterCoord.chartMap pivotNext '' sourceSet
      let source : Set (center → ℝ) :=
        {value | value pivotNext ≠ 0}
      let domain := source ×ˢ Metric.ball (0 : EuclideanSpace ℝ Coord) R
      let selectedEntrySource :=
        ((((volume : Measure (center → ℝ)).restrict sourceSet).withDensity
          (fun y : center → ℝ =>
            ENNReal.ofReal
              (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))).prod
          regularMeasure)
      let selectedEntryProductChart :
          (center → ℝ) × EuclideanSpace ℝ Coord → EdgeFamily :=
        fun z ↦
          CedgeProd
            (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1, z.2)
      let valueReference :=
        ((volume : Measure (center → ℝ)).restrict valueImage).prod regularMeasure
      Measure.map selectedEntryProductChart selectedEntrySource =
        Measure.map CedgeProd (valueReference.restrict domain) := by
  intro center pivotNext EdgeFamily retainedData sourceChart Rbox
  rcases
      exists_pos_radius_le_case2EndpointTransport_selectedEntryValue_productCoordinate_map_selectedEntrySource_eq_map_valueReference
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
        eNext e (Rmax := Rmax) hRmax Rbox with
    ⟨R, hR, hRle, hmap⟩
  refine ⟨R, hR, hRle, ?_⟩
  intro ρ κ Coord CedgeProd regularMeasure sourceSet valueImage source domain
    selectedEntrySource selectedEntryProductChart valueReference
  have hsource : MeasurableSet source := by
    simpa [source] using
      SelectedEntrySignedBox.CenterCoord.measurableSet_pivot_ne_zero pivotNext
  have hdomain : MeasurableSet domain := by
    simpa [domain] using
      hsource.prod
        (Metric.isOpen_ball.measurableSet :
          MeasurableSet (Metric.ball (0 : EuclideanSpace ℝ Coord) R))
  have hvalueImage_meas : MeasurableSet valueImage := by
    simpa [sourceSet, valueImage] using
      SelectedEntrySignedBox.CenterCoord.measurableSet_chartMap_image_signedBoxSet_inter_pivot_ne_zero
        pivotNext Rbox
  have hvalueImage_subset_source : valueImage ⊆ source := by
    intro value hvalue
    rcases hvalue with ⟨y, hy, rfl⟩
    exact
      (SelectedEntrySignedBox.CenterCoord.chartMap_mem_pivot_ne_zero_iff pivotNext y).2
        hy.2
  have hvalueReference_support : valueReference.restrict domain = valueReference := by
    have hleft_ae :
        ∀ᵐ value ∂(volume : Measure (center → ℝ)).restrict valueImage,
          value ∈ source := by
      filter_upwards [ae_restrict_mem hvalueImage_meas] with value hvalue
      exact hvalueImage_subset_source hvalue
    have hright_ae :
        ∀ᵐ u ∂regularMeasure,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ Coord) R := by
      simpa [regularMeasure] using
        (ae_restrict_mem
          (Metric.isOpen_ball.measurableSet :
            MeasurableSet (Metric.ball (0 : EuclideanSpace ℝ Coord) R)))
    have hmem : ∀ᵐ z ∂valueReference, z ∈ domain := by
      rw [Measure.ae_prod_mem_iff_ae_ae_mem hdomain]
      filter_upwards [hleft_ae] with value hvalue
      filter_upwards [hright_ae] with u hu
      exact ⟨hvalue, hu⟩
    exact Measure.restrict_eq_self_of_ae_mem hmem
  calc
    Measure.map selectedEntryProductChart selectedEntrySource =
        Measure.map CedgeProd valueReference := by
          simpa [ρ, κ, Coord, CedgeProd, regularMeasure, sourceSet,
            valueImage, selectedEntrySource, selectedEntryProductChart,
            valueReference] using hmap
    _ = Measure.map CedgeProd (valueReference.restrict domain) := by
          rw [hvalueReference_support]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Weighted selected-entry product-coordinate pushforward.

The selected-entry product-source pushforward remains true after multiplying
both sides by any downstream edge-family density.  This supplies the weighted
source-side identity expected by the product-coordinate handoff, but does not
identify formal-product Haar, raw Haar, original prior, normal crossings, pole
order, or RLCT. -/
theorem exists_pos_radius_le_case2EndpointTransport_selectedEntryValue_productCoordinate_map_selectedEntrySource_withDensity_eq_map_valueReference_withDensity_restrict_domain
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    {Rmax : ℝ} (hRmax : 0 < Rmax) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      ⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
          n hS hnext⟩
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        (center → ℝ) →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun yNext ↦
        (case2PostPivotSelectedEntryRetainedPassiveData
          (ρ := Fin (Module.finrank ℝ U₀))
          n hS hcont hnext yNext eNext).endpointTransport e
    let sourceChart : (center → ℝ) → EdgeFamily :=
      fun value ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
          W₂ B₂ U₀ hU₀
          (retainedData
            (SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero
              pivotNext value))
    ∀ Rbox : center → ℝ,
    ∃ R : ℝ, 0 < R ∧ R ≤ Rmax ∧
      let ρ := Fin (Module.finrank ℝ U₀)
      let κ := throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
      let Coord :=
        AoyagiRegularBlockCoordinateIndex ρ (κ (Fin.last 2)) (κ 0)
      let CedgeProd :=
        paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
          W₂ B₂ U₀ hU₀ sourceChart
      let regularMeasure :=
        (volume : Measure (EuclideanSpace ℝ Coord)).restrict
          (Metric.ball (0 : EuclideanSpace ℝ Coord) R)
      let sourceSet :=
        SelectedEntrySignedBox.CenterCoord.signedBoxSet Rbox ∩
          {y : center → ℝ | y pivotNext ≠ 0}
      let valueImage :=
        SelectedEntrySignedBox.CenterCoord.chartMap pivotNext '' sourceSet
      let source : Set (center → ℝ) :=
        {value | value pivotNext ≠ 0}
      let domain := source ×ˢ Metric.ball (0 : EuclideanSpace ℝ Coord) R
      let selectedEntrySource :=
        ((((volume : Measure (center → ℝ)).restrict sourceSet).withDensity
          (fun y : center → ℝ =>
            ENNReal.ofReal
              (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))).prod
          regularMeasure)
      let selectedEntryProductChart :
          (center → ℝ) × EuclideanSpace ℝ Coord → EdgeFamily :=
        fun z ↦
          CedgeProd
            (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1, z.2)
      let valueReference :=
        ((volume : Measure (center → ℝ)).restrict valueImage).prod regularMeasure
      ∀ density : EdgeFamily → ℝ≥0∞,
        AEMeasurable density
          (Measure.map CedgeProd (valueReference.restrict domain)) →
          Measure.map selectedEntryProductChart
            (selectedEntrySource.withDensity
              (fun z ↦ density (selectedEntryProductChart z))) =
            Measure.map CedgeProd
              ((valueReference.withDensity
                (fun z ↦ density (CedgeProd z))).restrict domain) := by
  intro center pivotNext EdgeFamily retainedData sourceChart Rbox
  let source : Set (center → ℝ) :=
    {value | value pivotNext ≠ 0}
  let residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0) ≃ center :=
    case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
      n S (J + 1) (e (Fin.last 2)).symm ((e 0).symm.trans eNext)
  let baseReadback :
      (AoyagiResidualBlockCoordinateIndex
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0) → ℝ) →
        center → ℝ :=
    fun coord i ↦ coord (residualCoordEquiv.symm i)
  have hsource : MeasurableSet source := by
    simpa [source] using
      SelectedEntrySignedBox.CenterCoord.measurableSet_pivot_ne_zero pivotNext
  have hsourceChart_direct :
      Continuous
        (fun yNext : center → ℝ ↦
          paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
            W₂ B₂ U₀ hU₀ (retainedData yNext)) := by
    simpa [center, EdgeFamily, retainedData] using
      continuous_retainedPassiveP13SourceEdgeFamilyOfData_of_case2EndpointTransport
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
  have hCedgeBase :
      ∀ value ∈ source, ContinuousAt sourceChart value := by
    intro value hvalue
    have hpre :
        ContinuousAt
          (SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero pivotNext)
          value :=
      SelectedEntrySignedBox.CenterCoord.continuousAt_preimageOfPivotNeZero
        pivotNext (by simpa [source] using hvalue)
    simpa [sourceChart] using
      hsourceChart_direct.continuousAt.comp hpre
  have hchart :
      ∀ value ∈ source, ∀ (p : Fin 2)
          (hpj : p.succ ≤ (Fin.last 2 : Fin 3)),
        identityCornerDetChart
          (ChartLocalSuffixState.transformedEdge
            (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
              (fun q : Fin 2 ↦
                (sourceChart value q :
                  reverseVertex W₂ q.castSucc →ₗ[ℝ] reverseVertex W₂ q.succ))) p
            (ChartLocalSuffixState.suffixState
              (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
                (fun q : Fin 2 ↦
                  (sourceChart value q :
                    reverseVertex W₂ q.castSucc →ₗ[ℝ] reverseVertex W₂ q.succ)))
              (Fin.last 2) p.succ hpj)) := by
    intro value _hvalue p hpj
    have hpre :
        sourceChart value ∈
          paperEndpointFixedBaseRetainedPassiveP13LocalSource
            W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) := by
      have hlocal :=
        (retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData
          W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e).1
          (SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero
            pivotNext value)
      simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart] using
        hlocal
    have hrecursive :
        ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceRecursiveDetChart
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
            (fun q : Fin 2 ↦
              (sourceChart value q :
                reverseVertex W₂ q.castSucc →ₗ[ℝ] reverseVertex W₂ q.succ))) := by
      simpa [paperEndpointFixedBaseRetainedPassiveP13LocalSource] using hpre
    exact hrecursive p hpj
  have hbaseReadback :
      ∀ value ∈ source,
        baseReadback
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ sourceChart value) =
          value := by
    intro value hvalue
    funext i
    have hresidual_id :
        paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀
            (fun E : EdgeFamily ↦ E) (sourceChart value) =
          paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ sourceChart value :=
      paperEndpointFixedBaseResidualBlockCoordinateMap_congr_point
        (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀
        (Cedge := fun E : EdgeFamily ↦ E) (Cedge' := sourceChart)
        (x := sourceChart value) (y := value) rfl
    have hcoord :=
      paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_value_of_case2EndpointTransport_sourceEdgeFamilyOfData_preimageOfPivotNeZero
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        value (by simpa [source] using hvalue) (residualCoordEquiv.symm i)
    calc
      baseReadback
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ sourceChart value) i =
          paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ sourceChart value
            (residualCoordEquiv.symm i) := by
            rfl
      _ =
          paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
            (sourceChart value) (residualCoordEquiv.symm i) := by
            rw [← congrFun hresidual_id (residualCoordEquiv.symm i)]
      _ = value (residualCoordEquiv (residualCoordEquiv.symm i)) := by
            simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart,
              residualCoordEquiv] using hcoord
      _ = value i := by
            exact congrArg value (residualCoordEquiv.apply_symm_apply i)
  rcases
      exists_pos_radius_le_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_sourceChart_readback_package_of_residualReadback
        (M := 0) W₂ B₂ U₀ hU₀ sourceChart (source := source) (Rmax := Rmax)
        hsource hRmax hCedgeBase hchart baseReadback hbaseReadback with
    ⟨R, hR, hRle, hpackage⟩
  refine ⟨R, hR, hRle, ?_⟩
  intro ρ κ Coord CedgeProd regularMeasure sourceSet valueImage source' domain
    selectedEntrySource selectedEntryProductChart valueReference density hdensity
  let productReadback : EdgeFamily → (center → ℝ) × EuclideanSpace ℝ Coord :=
    fun E ↦
      (baseReadback
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀
            (fun E' : EdgeFamily ↦ E') E),
        (EuclideanSpace.equiv Coord ℝ).symm
          (paperEndpointFixedBaseRegularBlockCoordinateMap
            (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀
            (fun E' : EdgeFamily ↦ E') E))
  have hpackage' :
      (∀ z ∈ domain, productReadback (CedgeProd z) = z) ∧
        Set.InjOn CedgeProd domain ∧
          ContinuousOn CedgeProd domain ∧
            (∀ thetaMeasure : Measure ((center → ℝ) × EuclideanSpace ℝ Coord),
              AEMeasurable CedgeProd (thetaMeasure.restrict domain)) ∧
              MeasurableSet (CedgeProd '' domain) ∧
                ∀ E ∈ CedgeProd '' domain,
                  productReadback E ∈ domain ∧ CedgeProd (productReadback E) = E := by
    simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart, source,
      residualCoordEquiv, baseReadback, ρ, κ, Coord, CedgeProd, productReadback,
      domain] using hpackage
  rcases hpackage' with ⟨_hleft, _hinj, hcont_prod, _haemeas_prod, _himage_prod, _hright⟩
  have hdomain : MeasurableSet domain := by
    simpa [domain, source'] using
      hsource.prod
        (Metric.isOpen_ball.measurableSet :
          MeasurableSet (Metric.ball (0 : EuclideanSpace ℝ Coord) R))
  have hvalueImage_meas : MeasurableSet valueImage := by
    simpa [sourceSet, valueImage] using
      SelectedEntrySignedBox.CenterCoord.measurableSet_chartMap_image_signedBoxSet_inter_pivot_ne_zero
        pivotNext Rbox
  have hvalueImage_subset_source : valueImage ⊆ source' := by
    intro value hvalue
    rcases hvalue with ⟨y, hy, rfl⟩
    exact
      (SelectedEntrySignedBox.CenterCoord.chartMap_mem_pivot_ne_zero_iff pivotNext y).2
        hy.2
  have hvalueReference_support : valueReference.restrict domain = valueReference := by
    have hleft_ae :
        ∀ᵐ value ∂(volume : Measure (center → ℝ)).restrict valueImage,
          value ∈ source' := by
      filter_upwards [ae_restrict_mem hvalueImage_meas] with value hvalue
      exact hvalueImage_subset_source hvalue
    have hright_ae :
        ∀ᵐ u ∂regularMeasure,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ Coord) R := by
      simpa [regularMeasure] using
        (ae_restrict_mem
          (Metric.isOpen_ball.measurableSet :
            MeasurableSet (Metric.ball (0 : EuclideanSpace ℝ Coord) R)))
    have hmem : ∀ᵐ z ∂valueReference, z ∈ domain := by
      rw [Measure.ae_prod_mem_iff_ae_ae_mem hdomain]
      filter_upwards [hleft_ae] with value hvalue
      filter_upwards [hright_ae] with u hu
      exact ⟨hvalue, hu⟩
    exact Measure.restrict_eq_self_of_ae_mem hmem
  have hCedgeProd :
      AEMeasurable CedgeProd valueReference := by
    exact
      aemeasurable_of_continuousOn_of_measure_restrict_eq_self
        (sourceChart := CedgeProd) (μ := valueReference) (V := domain)
        hcont_prod hdomain hvalueReference_support
  have hdensity_value :
      AEMeasurable density (Measure.map CedgeProd valueReference) := by
    simpa [hvalueReference_support] using hdensity
  have hweighted :=
    SelectedEntrySignedBox.CenterCoord.map_comp_prod_chartMap_id_restrict_nonzeroSignedBox_withDensity_sourceDensity_withDensity_comp_eq_map_restrict_image_prod_withDensity
      (β := EuclideanSpace ℝ Coord) (γ := EdgeFamily)
      pivotNext Rbox regularMeasure (F := CedgeProd) (density := density)
      hCedgeProd hdensity_value
  calc
    Measure.map selectedEntryProductChart
        (selectedEntrySource.withDensity
          (fun z ↦ density (selectedEntryProductChart z))) =
        Measure.map CedgeProd
          (valueReference.withDensity
            (fun z ↦ density (CedgeProd z))) := by
          simpa [regularMeasure, sourceSet, valueImage, selectedEntrySource,
            selectedEntryProductChart, valueReference] using hweighted
    _ =
        Measure.map CedgeProd
          ((valueReference.withDensity
            (fun z ↦ density (CedgeProd z))).restrict domain) := by
          rw [restrict_withDensity hdomain, hvalueReference_support]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Same-radius readback domination for a bounded downstream density on the
selected-entry product-coordinate pushforward.

This is the bounded-density version of the selected-entry readback theorem:
the weighted selected-entry product source is still chart-produced, and the
bound is against the selected-entry value-reference product measure.  It does
not identify formal-product Haar, determinant/raw Haar, original prior, normal
crossings, pole order, or RLCT. -/
theorem exists_pos_radius_le_case2EndpointTransport_selectedEntryValue_productCoordinate_map_selectedEntrySource_withDensity_readback_le_smul_valueReference_restrict_domain
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    {Rmax : ℝ} (hRmax : 0 < Rmax) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      ⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
          n hS hnext⟩
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        (center → ℝ) →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun yNext ↦
        (case2PostPivotSelectedEntryRetainedPassiveData
          (ρ := Fin (Module.finrank ℝ U₀))
          n hS hcont hnext yNext eNext).endpointTransport e
    let sourceChart : (center → ℝ) → EdgeFamily :=
      fun value ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
          W₂ B₂ U₀ hU₀
          (retainedData
            (SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero
              pivotNext value))
    ∀ Rbox : center → ℝ,
    ∃ R : ℝ, 0 < R ∧ R ≤ Rmax ∧
      let ρ := Fin (Module.finrank ℝ U₀)
      let κ := throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
      let Coord :=
        AoyagiRegularBlockCoordinateIndex ρ (κ (Fin.last 2)) (κ 0)
      let CedgeProd :=
        paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
          W₂ B₂ U₀ hU₀ sourceChart
      let regularMeasure :=
        (volume : Measure (EuclideanSpace ℝ Coord)).restrict
          (Metric.ball (0 : EuclideanSpace ℝ Coord) R)
      let sourceSet :=
        SelectedEntrySignedBox.CenterCoord.signedBoxSet Rbox ∩
          {y : center → ℝ | y pivotNext ≠ 0}
      let valueImage :=
        SelectedEntrySignedBox.CenterCoord.chartMap pivotNext '' sourceSet
      let source : Set (center → ℝ) :=
        {value | value pivotNext ≠ 0}
      let domain := source ×ˢ Metric.ball (0 : EuclideanSpace ℝ Coord) R
      let residualCoordEquiv :
          AoyagiResidualBlockCoordinateIndex (κ (Fin.last 2)) (κ 0) ≃ center :=
        case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
          n S (J + 1) (e (Fin.last 2)).symm ((e 0).symm.trans eNext)
      let baseReadback :
          (AoyagiResidualBlockCoordinateIndex (κ (Fin.last 2)) (κ 0) → ℝ) →
            center → ℝ :=
        fun coord i ↦ coord (residualCoordEquiv.symm i)
      let productReadback : EdgeFamily → (center → ℝ) × EuclideanSpace ℝ Coord :=
        fun E ↦
          (baseReadback
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀
                (fun E' : EdgeFamily ↦ E') E),
            (EuclideanSpace.equiv Coord ℝ).symm
              (paperEndpointFixedBaseRegularBlockCoordinateMap
                (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀
                (fun E' : EdgeFamily ↦ E') E))
      let selectedEntrySource :=
        ((((volume : Measure (center → ℝ)).restrict sourceSet).withDensity
          (fun y : center → ℝ =>
            ENNReal.ofReal
              (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))).prod
          regularMeasure)
      let selectedEntryProductChart :
          (center → ℝ) × EuclideanSpace ℝ Coord → EdgeFamily :=
        fun z ↦
          CedgeProd
            (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1, z.2)
      let valueReference :=
        ((volume : Measure (center → ℝ)).restrict valueImage).prod regularMeasure
      ∀ (chartPiece : Set EdgeFamily) (density : EdgeFamily → ℝ≥0∞) (c : ℝ≥0∞),
        MeasurableSet chartPiece →
          AEMeasurable density
            (Measure.map CedgeProd (valueReference.restrict domain)) →
          (∀ᵐ E ∂(Measure.map CedgeProd
              (valueReference.restrict domain)).restrict chartPiece,
            density E ≤ c) →
          AEMeasurable productReadback
            ((Measure.map selectedEntryProductChart
              (selectedEntrySource.withDensity
                (fun z ↦ density (selectedEntryProductChart z)))).restrict
              chartPiece) ∧
          Measure.map productReadback
            ((Measure.map selectedEntryProductChart
              (selectedEntrySource.withDensity
                (fun z ↦ density (selectedEntryProductChart z)))).restrict
              chartPiece) ≤
            c • valueReference.restrict domain := by
  intro center pivotNext EdgeFamily retainedData sourceChart Rbox
  let source : Set (center → ℝ) :=
    {value | value pivotNext ≠ 0}
  let residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0) ≃ center :=
    case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
      n S (J + 1) (e (Fin.last 2)).symm ((e 0).symm.trans eNext)
  let baseReadback :
      (AoyagiResidualBlockCoordinateIndex
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0) → ℝ) →
        center → ℝ :=
    fun coord i ↦ coord (residualCoordEquiv.symm i)
  have hsource : MeasurableSet source := by
    simpa [source] using
      SelectedEntrySignedBox.CenterCoord.measurableSet_pivot_ne_zero pivotNext
  have hsourceChart_direct :
      Continuous
        (fun yNext : center → ℝ ↦
          paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
            W₂ B₂ U₀ hU₀ (retainedData yNext)) := by
    simpa [center, EdgeFamily, retainedData] using
      continuous_retainedPassiveP13SourceEdgeFamilyOfData_of_case2EndpointTransport
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
  have hCedgeBase :
      ∀ value ∈ source, ContinuousAt sourceChart value := by
    intro value hvalue
    have hpre :
        ContinuousAt
          (SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero pivotNext)
          value :=
      SelectedEntrySignedBox.CenterCoord.continuousAt_preimageOfPivotNeZero
        pivotNext (by simpa [source] using hvalue)
    simpa [sourceChart] using
      hsourceChart_direct.continuousAt.comp hpre
  have hchart :
      ∀ value ∈ source, ∀ (p : Fin 2)
          (hpj : p.succ ≤ (Fin.last 2 : Fin 3)),
        identityCornerDetChart
          (ChartLocalSuffixState.transformedEdge
            (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
              (fun q : Fin 2 ↦
                (sourceChart value q :
                  reverseVertex W₂ q.castSucc →ₗ[ℝ] reverseVertex W₂ q.succ))) p
            (ChartLocalSuffixState.suffixState
              (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
                (fun q : Fin 2 ↦
                  (sourceChart value q :
                    reverseVertex W₂ q.castSucc →ₗ[ℝ] reverseVertex W₂ q.succ)))
              (Fin.last 2) p.succ hpj)) := by
    intro value _hvalue p hpj
    have hpre :
        sourceChart value ∈
          paperEndpointFixedBaseRetainedPassiveP13LocalSource
            W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) := by
      have hlocal :=
        (retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData
          W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e).1
          (SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero
            pivotNext value)
      simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart] using
        hlocal
    have hrecursive :
        ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceRecursiveDetChart
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
            (fun q : Fin 2 ↦
              (sourceChart value q :
                reverseVertex W₂ q.castSucc →ₗ[ℝ] reverseVertex W₂ q.succ))) := by
      simpa [paperEndpointFixedBaseRetainedPassiveP13LocalSource] using hpre
    exact hrecursive p hpj
  have hbaseReadback :
      ∀ value ∈ source,
        baseReadback
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ sourceChart value) =
          value := by
    intro value hvalue
    funext i
    have hresidual_id :
        paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀
            (fun E : EdgeFamily ↦ E) (sourceChart value) =
          paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ sourceChart value :=
      paperEndpointFixedBaseResidualBlockCoordinateMap_congr_point
        (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀
        (Cedge := fun E : EdgeFamily ↦ E) (Cedge' := sourceChart)
        (x := sourceChart value) (y := value) rfl
    have hcoord :=
      paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_value_of_case2EndpointTransport_sourceEdgeFamilyOfData_preimageOfPivotNeZero
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        value (by simpa [source] using hvalue) (residualCoordEquiv.symm i)
    calc
      baseReadback
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ sourceChart value) i =
          paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ sourceChart value
            (residualCoordEquiv.symm i) := by
            rfl
      _ =
          paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
            (sourceChart value) (residualCoordEquiv.symm i) := by
            rw [← congrFun hresidual_id (residualCoordEquiv.symm i)]
      _ = value (residualCoordEquiv (residualCoordEquiv.symm i)) := by
            simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart,
              residualCoordEquiv] using hcoord
      _ = value i := by
            exact congrArg value (residualCoordEquiv.apply_symm_apply i)
  rcases
      exists_pos_radius_le_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_sourceChart_readback_package_of_residualReadback
        (M := 0) W₂ B₂ U₀ hU₀ sourceChart (source := source) (Rmax := Rmax)
        hsource hRmax hCedgeBase hchart baseReadback hbaseReadback with
    ⟨R, hR, hRle, hpackage⟩
  refine ⟨R, hR, hRle, ?_⟩
  intro ρ κ Coord CedgeProd regularMeasure sourceSet valueImage source' domain
    residualCoordEquiv' baseReadback' productReadback selectedEntrySource
    selectedEntryProductChart valueReference chartPiece density c hchartPiece
    hdensity hdensity_le
  have hpackage' :
      (∀ z ∈ domain, productReadback (CedgeProd z) = z) ∧
        Set.InjOn CedgeProd domain ∧
          ContinuousOn CedgeProd domain ∧
            (∀ thetaMeasure : Measure ((center → ℝ) × EuclideanSpace ℝ Coord),
              AEMeasurable CedgeProd (thetaMeasure.restrict domain)) ∧
              MeasurableSet (CedgeProd '' domain) ∧
                ∀ E ∈ CedgeProd '' domain,
                  productReadback E ∈ domain ∧ CedgeProd (productReadback E) = E := by
    simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart, source,
      residualCoordEquiv, baseReadback, ρ, κ, Coord, CedgeProd, productReadback,
      domain, residualCoordEquiv', baseReadback'] using hpackage
  rcases hpackage' with ⟨hleft, hinj, hcont_prod, _haemeas_prod, _himage_prod, _hright⟩
  have hdomain : MeasurableSet domain := by
    simpa [domain, source'] using
      hsource.prod
        (Metric.isOpen_ball.measurableSet :
          MeasurableSet (Metric.ball (0 : EuclideanSpace ℝ Coord) R))
  have hvalueImage_meas : MeasurableSet valueImage := by
    simpa [sourceSet, valueImage] using
      SelectedEntrySignedBox.CenterCoord.measurableSet_chartMap_image_signedBoxSet_inter_pivot_ne_zero
        pivotNext Rbox
  have hvalueImage_subset_source : valueImage ⊆ source' := by
    intro value hvalue
    rcases hvalue with ⟨y, hy, rfl⟩
    exact
      (SelectedEntrySignedBox.CenterCoord.chartMap_mem_pivot_ne_zero_iff pivotNext y).2
        hy.2
  have hvalueReference_support : valueReference.restrict domain = valueReference := by
    have hleft_ae :
        ∀ᵐ value ∂(volume : Measure (center → ℝ)).restrict valueImage,
          value ∈ source' := by
      filter_upwards [ae_restrict_mem hvalueImage_meas] with value hvalue
      exact hvalueImage_subset_source hvalue
    have hright_ae :
        ∀ᵐ u ∂regularMeasure,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ Coord) R := by
      simpa [regularMeasure] using
        (ae_restrict_mem
          (Metric.isOpen_ball.measurableSet :
            MeasurableSet (Metric.ball (0 : EuclideanSpace ℝ Coord) R)))
    have hmem : ∀ᵐ z ∂valueReference, z ∈ domain := by
      rw [Measure.ae_prod_mem_iff_ae_ae_mem hdomain]
      filter_upwards [hleft_ae] with value hvalue
      filter_upwards [hright_ae] with u hu
      exact ⟨hvalue, hu⟩
    exact Measure.restrict_eq_self_of_ae_mem hmem
  have hCedgeProd :
      AEMeasurable CedgeProd valueReference := by
    exact
      aemeasurable_of_continuousOn_of_measure_restrict_eq_self
        (sourceChart := CedgeProd) (μ := valueReference) (V := domain)
        hcont_prod hdomain hvalueReference_support
  have hdensity_value :
      AEMeasurable density (Measure.map CedgeProd valueReference) := by
    simpa [hvalueReference_support] using hdensity
  have hweighted :=
    SelectedEntrySignedBox.CenterCoord.map_comp_prod_chartMap_id_restrict_nonzeroSignedBox_withDensity_sourceDensity_withDensity_comp_eq_map_restrict_image_prod_withDensity
      (β := EuclideanSpace ℝ Coord) (γ := EdgeFamily)
      pivotNext Rbox regularMeasure (F := CedgeProd) (density := density)
      hCedgeProd hdensity_value
  have heq :
      (Measure.map selectedEntryProductChart
        (selectedEntrySource.withDensity
          (fun z ↦ density (selectedEntryProductChart z)))).restrict chartPiece =
        (Measure.map CedgeProd
          ((valueReference.withDensity
            (fun z ↦ density (CedgeProd z))).restrict domain)).restrict chartPiece := by
    calc
      (Measure.map selectedEntryProductChart
        (selectedEntrySource.withDensity
          (fun z ↦ density (selectedEntryProductChart z)))).restrict chartPiece =
          (Measure.map CedgeProd
            (valueReference.withDensity
              (fun z ↦ density (CedgeProd z)))).restrict chartPiece := by
            rw [hweighted]
      _ =
          (Measure.map CedgeProd
            ((valueReference.withDensity
              (fun z ↦ density (CedgeProd z))).restrict domain)).restrict chartPiece := by
            rw [restrict_withDensity hdomain, hvalueReference_support]
  have hreadback :=
    aemeasurable_readback_and_measure_map_readback_restrict_piece_le_smul_restrict_superset_of_restrict_eq_map_sourceChart_withDensity_of_continuousOn_injOn
      CedgeProd productReadback
      (Measure.map selectedEntryProductChart
        (selectedEntrySource.withDensity
          (fun z ↦ density (selectedEntryProductChart z))))
      valueReference domain domain chartPiece density c hdomain hchartPiece
      (fun z hz ↦ hz) hcont_prod hinj hleft hdensity heq hdensity_le
  exact hreadback

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Same-radius readback domination for the selected-entry product-coordinate
pushforward.

The selected-entry product pushforward is used as the weighted source-side
identity with density `1`, so the generic p.13 product-readback handoff gives
domination by the value-reference product measure restricted to the same
domain.  This is not formal-product Haar, determinant/raw Haar, original-prior
transport, normal crossings, pole order, or RLCT. -/
theorem exists_pos_radius_le_case2EndpointTransport_selectedEntryValue_productCoordinate_map_selectedEntrySource_readback_le_valueReference_restrict_domain
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    {Rmax : ℝ} (hRmax : 0 < Rmax) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      ⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
          n hS hnext⟩
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        (center → ℝ) →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun yNext ↦
        (case2PostPivotSelectedEntryRetainedPassiveData
          (ρ := Fin (Module.finrank ℝ U₀))
          n hS hcont hnext yNext eNext).endpointTransport e
    let sourceChart : (center → ℝ) → EdgeFamily :=
      fun value ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
          W₂ B₂ U₀ hU₀
          (retainedData
            (SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero
              pivotNext value))
    ∀ Rbox : center → ℝ,
    ∃ R : ℝ, 0 < R ∧ R ≤ Rmax ∧
      let ρ := Fin (Module.finrank ℝ U₀)
      let κ := throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
      let Coord :=
        AoyagiRegularBlockCoordinateIndex ρ (κ (Fin.last 2)) (κ 0)
      let CedgeProd :=
        paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
          W₂ B₂ U₀ hU₀ sourceChart
      let regularMeasure :=
        (volume : Measure (EuclideanSpace ℝ Coord)).restrict
          (Metric.ball (0 : EuclideanSpace ℝ Coord) R)
      let sourceSet :=
        SelectedEntrySignedBox.CenterCoord.signedBoxSet Rbox ∩
          {y : center → ℝ | y pivotNext ≠ 0}
      let valueImage :=
        SelectedEntrySignedBox.CenterCoord.chartMap pivotNext '' sourceSet
      let source : Set (center → ℝ) :=
        {value | value pivotNext ≠ 0}
      let domain := source ×ˢ Metric.ball (0 : EuclideanSpace ℝ Coord) R
      let residualCoordEquiv :
          AoyagiResidualBlockCoordinateIndex (κ (Fin.last 2)) (κ 0) ≃ center :=
        case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
          n S (J + 1) (e (Fin.last 2)).symm ((e 0).symm.trans eNext)
      let baseReadback :
          (AoyagiResidualBlockCoordinateIndex (κ (Fin.last 2)) (κ 0) → ℝ) →
            center → ℝ :=
        fun coord i ↦ coord (residualCoordEquiv.symm i)
      let productReadback : EdgeFamily → (center → ℝ) × EuclideanSpace ℝ Coord :=
        fun E ↦
          (baseReadback
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀
                (fun E' : EdgeFamily ↦ E') E),
            (EuclideanSpace.equiv Coord ℝ).symm
              (paperEndpointFixedBaseRegularBlockCoordinateMap
                (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀
                (fun E' : EdgeFamily ↦ E') E))
      let selectedEntrySource :=
        ((((volume : Measure (center → ℝ)).restrict sourceSet).withDensity
          (fun y : center → ℝ =>
            ENNReal.ofReal
              (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))).prod
          regularMeasure)
      let selectedEntryProductChart :
          (center → ℝ) × EuclideanSpace ℝ Coord → EdgeFamily :=
        fun z ↦
          CedgeProd
            (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1, z.2)
      let valueReference :=
        ((volume : Measure (center → ℝ)).restrict valueImage).prod regularMeasure
      ∀ chartPiece : Set EdgeFamily,
        MeasurableSet chartPiece →
          AEMeasurable productReadback
            ((Measure.map selectedEntryProductChart selectedEntrySource).restrict chartPiece) ∧
          Measure.map productReadback
            ((Measure.map selectedEntryProductChart selectedEntrySource).restrict chartPiece) ≤
            valueReference.restrict domain := by
  intro center pivotNext EdgeFamily retainedData sourceChart Rbox
  let source : Set (center → ℝ) :=
    {value | value pivotNext ≠ 0}
  let residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0) ≃ center :=
    case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
      n S (J + 1) (e (Fin.last 2)).symm ((e 0).symm.trans eNext)
  let baseReadback :
      (AoyagiResidualBlockCoordinateIndex
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0) → ℝ) →
        center → ℝ :=
    fun coord i ↦ coord (residualCoordEquiv.symm i)
  have hsource : MeasurableSet source := by
    simpa [source] using
      SelectedEntrySignedBox.CenterCoord.measurableSet_pivot_ne_zero pivotNext
  have hsourceChart_direct :
      Continuous
        (fun yNext : center → ℝ ↦
          paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
            W₂ B₂ U₀ hU₀ (retainedData yNext)) := by
    simpa [center, EdgeFamily, retainedData] using
      continuous_retainedPassiveP13SourceEdgeFamilyOfData_of_case2EndpointTransport
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
  have hCedgeBase :
      ∀ value ∈ source, ContinuousAt sourceChart value := by
    intro value hvalue
    have hpre :
        ContinuousAt
          (SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero pivotNext)
          value :=
      SelectedEntrySignedBox.CenterCoord.continuousAt_preimageOfPivotNeZero
        pivotNext (by simpa [source] using hvalue)
    simpa [sourceChart] using
      hsourceChart_direct.continuousAt.comp hpre
  have hchart :
      ∀ value ∈ source, ∀ (p : Fin 2)
          (hpj : p.succ ≤ (Fin.last 2 : Fin 3)),
        identityCornerDetChart
          (ChartLocalSuffixState.transformedEdge
            (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
              (fun q : Fin 2 ↦
                (sourceChart value q :
                  reverseVertex W₂ q.castSucc →ₗ[ℝ] reverseVertex W₂ q.succ))) p
            (ChartLocalSuffixState.suffixState
              (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
                (fun q : Fin 2 ↦
                  (sourceChart value q :
                    reverseVertex W₂ q.castSucc →ₗ[ℝ] reverseVertex W₂ q.succ)))
              (Fin.last 2) p.succ hpj)) := by
    intro value _hvalue p hpj
    have hpre :
        sourceChart value ∈
          paperEndpointFixedBaseRetainedPassiveP13LocalSource
            W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) := by
      have hlocal :=
        (retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData
          W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e).1
          (SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero
            pivotNext value)
      simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart] using
        hlocal
    have hrecursive :
        ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceRecursiveDetChart
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
            (fun q : Fin 2 ↦
              (sourceChart value q :
                reverseVertex W₂ q.castSucc →ₗ[ℝ] reverseVertex W₂ q.succ))) := by
      simpa [paperEndpointFixedBaseRetainedPassiveP13LocalSource] using hpre
    exact hrecursive p hpj
  have hbaseReadback :
      ∀ value ∈ source,
        baseReadback
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ sourceChart value) =
          value := by
    intro value hvalue
    funext i
    have hresidual_id :
        paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀
            (fun E : EdgeFamily ↦ E) (sourceChart value) =
          paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ sourceChart value :=
      paperEndpointFixedBaseResidualBlockCoordinateMap_congr_point
        (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀
        (Cedge := fun E : EdgeFamily ↦ E) (Cedge' := sourceChart)
        (x := sourceChart value) (y := value) rfl
    have hcoord :=
      paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_value_of_case2EndpointTransport_sourceEdgeFamilyOfData_preimageOfPivotNeZero
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        value (by simpa [source] using hvalue) (residualCoordEquiv.symm i)
    calc
      baseReadback
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ sourceChart value) i =
          paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ sourceChart value
            (residualCoordEquiv.symm i) := by
            rfl
      _ =
          paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
            (sourceChart value) (residualCoordEquiv.symm i) := by
            rw [← congrFun hresidual_id (residualCoordEquiv.symm i)]
      _ = value (residualCoordEquiv (residualCoordEquiv.symm i)) := by
            simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart,
              residualCoordEquiv] using hcoord
      _ = value i := by
            exact congrArg value (residualCoordEquiv.apply_symm_apply i)
  rcases
      exists_pos_radius_le_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_sourceChart_readback_package_of_residualReadback
        (M := 0) W₂ B₂ U₀ hU₀ sourceChart (source := source) (Rmax := Rmax)
        hsource hRmax hCedgeBase hchart baseReadback hbaseReadback with
    ⟨R, hR, hRle, hpackage⟩
  refine ⟨R, hR, hRle, ?_⟩
  intro ρ κ Coord CedgeProd regularMeasure sourceSet valueImage source' domain
    residualCoordEquiv' baseReadback' productReadback selectedEntrySource
    selectedEntryProductChart valueReference chartPiece hchartPiece
  have hpackage' :
      (∀ z ∈ domain, productReadback (CedgeProd z) = z) ∧
        Set.InjOn CedgeProd domain ∧
          ContinuousOn CedgeProd domain ∧
            (∀ thetaMeasure : Measure ((center → ℝ) × EuclideanSpace ℝ Coord),
              AEMeasurable CedgeProd (thetaMeasure.restrict domain)) ∧
              MeasurableSet (CedgeProd '' domain) ∧
                ∀ E ∈ CedgeProd '' domain,
                  productReadback E ∈ domain ∧ CedgeProd (productReadback E) = E := by
    simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart, source,
      residualCoordEquiv, baseReadback, ρ, κ, Coord, CedgeProd, productReadback,
      domain, residualCoordEquiv', baseReadback'] using hpackage
  rcases hpackage' with ⟨hleft, hinj, hcont_prod, _haemeas_prod, _himage_prod, _hright⟩
  have hdomain : MeasurableSet domain := by
    simpa [domain, source'] using
      hsource.prod
        (Metric.isOpen_ball.measurableSet :
          MeasurableSet (Metric.ball (0 : EuclideanSpace ℝ Coord) R))
  have hvalueImage_meas : MeasurableSet valueImage := by
    simpa [sourceSet, valueImage] using
      SelectedEntrySignedBox.CenterCoord.measurableSet_chartMap_image_signedBoxSet_inter_pivot_ne_zero
        pivotNext Rbox
  have hvalueImage_subset_source : valueImage ⊆ source' := by
    intro value hvalue
    rcases hvalue with ⟨y, hy, rfl⟩
    exact
      (SelectedEntrySignedBox.CenterCoord.chartMap_mem_pivot_ne_zero_iff pivotNext y).2
        hy.2
  have hvalueReference_support : valueReference.restrict domain = valueReference := by
    have hleft_ae :
        ∀ᵐ value ∂(volume : Measure (center → ℝ)).restrict valueImage,
          value ∈ source' := by
      filter_upwards [ae_restrict_mem hvalueImage_meas] with value hvalue
      exact hvalueImage_subset_source hvalue
    have hright_ae :
        ∀ᵐ u ∂regularMeasure,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ Coord) R := by
      simpa [regularMeasure] using
        (ae_restrict_mem
          (Metric.isOpen_ball.measurableSet :
            MeasurableSet (Metric.ball (0 : EuclideanSpace ℝ Coord) R)))
    have hmem : ∀ᵐ z ∂valueReference, z ∈ domain := by
      rw [Measure.ae_prod_mem_iff_ae_ae_mem hdomain]
      filter_upwards [hleft_ae] with value hvalue
      filter_upwards [hright_ae] with u hu
      exact ⟨hvalue, hu⟩
    exact Measure.restrict_eq_self_of_ae_mem hmem
  have hCedgeProd :
      AEMeasurable CedgeProd valueReference := by
    exact
      aemeasurable_of_continuousOn_of_measure_restrict_eq_self
        (sourceChart := CedgeProd) (μ := valueReference) (V := domain)
        hcont_prod hdomain hvalueReference_support
  have hmap :
      Measure.map selectedEntryProductChart selectedEntrySource =
        Measure.map CedgeProd (valueReference.restrict domain) := by
    calc
      Measure.map selectedEntryProductChart selectedEntrySource =
          Measure.map CedgeProd valueReference := by
            simpa [regularMeasure, sourceSet, valueImage, source', domain,
              selectedEntrySource, selectedEntryProductChart, valueReference] using
              (SelectedEntrySignedBox.CenterCoord.map_comp_prod_chartMap_id_restrict_nonzeroSignedBox_withDensity_sourceDensity_eq_map_restrict_image_prod_of_aemeasurable
                (β := EuclideanSpace ℝ Coord) (γ := EdgeFamily)
                pivotNext Rbox regularMeasure (F := CedgeProd) hCedgeProd)
      _ = Measure.map CedgeProd (valueReference.restrict domain) := by
            rw [hvalueReference_support]
  have hdensity :
      AEMeasurable (fun _ : EdgeFamily ↦ (1 : ℝ≥0∞))
        (Measure.map CedgeProd (valueReference.restrict domain)) := by
    exact aemeasurable_const
  have heq :
      (Measure.map selectedEntryProductChart selectedEntrySource).restrict chartPiece =
        (Measure.map CedgeProd
          ((valueReference.withDensity
            (fun z ↦ (fun _ : EdgeFamily ↦ (1 : ℝ≥0∞)) (CedgeProd z))).restrict
            domain)).restrict chartPiece := by
    calc
      (Measure.map selectedEntryProductChart selectedEntrySource).restrict chartPiece =
          (Measure.map CedgeProd (valueReference.restrict domain)).restrict chartPiece := by
            rw [hmap]
      _ =
          (Measure.map CedgeProd
            ((valueReference.withDensity
              (fun z ↦ (fun _ : EdgeFamily ↦ (1 : ℝ≥0∞)) (CedgeProd z))).restrict
              domain)).restrict chartPiece := by
            simp
  have hdensity_le :
      ∀ᵐ E ∂(Measure.map CedgeProd
          (valueReference.restrict domain)).restrict chartPiece,
        (fun _ : EdgeFamily ↦ (1 : ℝ≥0∞)) E ≤ (1 : ℝ≥0∞) := by
    simp
  have hreadback :=
    aemeasurable_readback_and_measure_map_readback_restrict_piece_le_smul_restrict_superset_of_restrict_eq_map_sourceChart_withDensity_of_continuousOn_injOn
      CedgeProd productReadback (Measure.map selectedEntryProductChart selectedEntrySource)
      valueReference domain domain chartPiece (fun _ : EdgeFamily ↦ (1 : ℝ≥0∞))
      (1 : ℝ≥0∞) hdomain hchartPiece (fun z hz ↦ hz) hcont_prod hinj hleft
      hdensity heq hdensity_le
  exact ⟨hreadback.1, by simpa only [one_smul] using hreadback.2⟩

end PaperEndpointFixedBaseRegularCoordinateSourceData

end Aoyagi
end DLN
end DLNFibre

end
