import DLNFibre.DLN.Aoyagi.ProductReductionBoundary
import DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates
import DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesTopology

/-!
# Retained-passive local source in fixed endpoint bases

This file ties the retained-passive source-recursive determinant chart to the
fixed-base endpoint edge-family map used by the p.13 local-measure handoff.
It proves determinant-chart local coverage near the self-base point,
measurability under global source-edge continuity, and a finite residual
readout through the retained-passive source readback.  It does not prove
exact-rank openness, source-image equality, measure transport, a Jacobian
theorem, normal crossings, pole order, or RLCT extraction.
-/

noncomputable section

open Matrix

namespace DLNFibre
namespace DLN
namespace Aoyagi

open ChartLocalSuffixState
open ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData

section RetainedPassiveLocalSource

universe u v

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
  {M : ℕ}
  (W : Fin (M + 2) → Type v) [∀ i, AddCommGroup (W i)] [∀ i, TopologicalSpace (W i)]
  [∀ i, IsTopologicalAddGroup (W i)] [∀ i, T2Space (W i)]
  [∀ i, Module K (W i)] [∀ i, ContinuousSMul K (W i)]
  (B : ∀ i : Fin (M + 1), W i.succ →ₗ[K] W i.castSucc)

/-- The retained-passive p.13 local source obtained by pulling back the
source-recursive determinant chart along the fixed-base endpoint edge-matrix
map. -/
def paperEndpointFixedBaseRetainedPassiveP13LocalSource
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin (M + 1),
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ) : Set α :=
  {x |
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
        (fun p : Fin (M + 1) ↦
          (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)) ∈
      ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceRecursiveDetChartSet
        (K := K) (ρ := Fin (Module.finrank K U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀)}

/-- The named fixed-base retained-passive p.13 coordinate-to-source edge-family
map obtained by realising a determinant-chart datum's retained edge matrices
as continuous reversed edge maps.

This is the source-chart leg from retained-passive coordinates to source edge
families; it is not a source-image equality or coverage theorem. -/
def paperEndpointFixedBaseRetainedPassiveP13SourceChart
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (data :
      {data :
        RetainedPassiveNonredundantCoordinateData
          (K := K) (ρ := Fin (Module.finrank K U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) // data.detChart}) :
    ∀ p : Fin (M + 1),
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ :=
  paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices
    W B U₀ hU₀ data.1.edgeMatrix

/-- Continuous fixed-base retained-passive source edge families whose extracted
edge matrices lie in the source-recursive determinant chart. -/
def paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))) :
    Set (∀ p : Fin (M + 1),
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ) :=
  {E |
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
        (fun p : Fin (M + 1) ↦
          (E p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)) ∈
      sourceRecursiveDetChartSet
        (K := K) (ρ := Fin (Module.finrank K U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀)}

set_option linter.unusedSectionVars false in
/-- Fixed-base residual coordinates read as the residual-factor product of the
retained-passive source-readback residual blocks. -/
theorem paperEndpointFixedBaseResidualBlockCoordinateMap_eq_sourceReadback_residualFactorProduct
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin (M + 1),
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (x : α) :
    let E :=
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
        (fun p : Fin (M + 1) ↦
          (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ))
    paperEndpointFixedBaseResidualBlockCoordinateMap W B U₀ hU₀ Cedge x =
      AoyagiResidualBlockCoordinateIndex.value
        (ChartLocalSuffixState.residualFactorProduct
          (sourceReadback (K := K) (ρ := Fin (Module.finrank K U₀)) E).C
          (Fin.last (M + 1)) 0 (Fin.zero_le (Fin.last (M + 1)))) := by
  intro E
  let ρ := Fin (Module.finrank K U₀)
  let κ' := throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀
  let h0 : (0 : Fin (M + 2)) ≤ Fin.last (M + 1) :=
    Fin.zero_le (Fin.last (M + 1))
  have hres :
      paperEndpointFixedBaseResidualBlockCoordinateMap W B U₀ hU₀ Cedge x =
        AoyagiResidualBlockCoordinateIndex.value
          (ChartLocalSuffixState.residualProduct E (Fin.last (M + 1)) 0 h0) := by
    simpa [E, paperEndpointFixedBaseEdgeMatrixOfReverseEdges, ρ, κ', h0] using
      paperEndpointFixedBaseResidualBlockCoordinateMap_eq_residualProduct
        (K := K) W B U₀ hU₀ Cedge x
  have hD :
      (sourceReadbackSuffixState (K := K) (ρ := ρ) (κ' := κ') E 0 h0).D =
        ChartLocalSuffixState.residualProduct E (Fin.last (M + 1)) 0 h0 := by
    simpa [sourceReadbackSuffixState, ρ, κ', h0] using
      ChartLocalSuffixState.suffixState_D_eq_residualProduct
        (K := K) E h0
  have hsource :
      (sourceReadbackSuffixState (K := K) (ρ := ρ) (κ' := κ') E 0 h0).D =
        ChartLocalSuffixState.residualFactorProduct
          (sourceReadback (K := K) (ρ := ρ) E).C
          (Fin.last (M + 1)) 0 h0 := by
    simpa [ρ, κ', h0] using
      sourceReadbackSuffixState_D_eq_residualFactorProduct_C
        (K := K) (ρ := ρ) E 0 h0
  have hfactor :
      ChartLocalSuffixState.residualProduct E (Fin.last (M + 1)) 0 h0 =
        ChartLocalSuffixState.residualFactorProduct
          (sourceReadback (K := K) (ρ := ρ) E).C
          (Fin.last (M + 1)) 0 h0 :=
    hD.symm.trans hsource
  calc
    paperEndpointFixedBaseResidualBlockCoordinateMap W B U₀ hU₀ Cedge x =
        AoyagiResidualBlockCoordinateIndex.value
          (ChartLocalSuffixState.residualProduct E (Fin.last (M + 1)) 0 h0) := hres
    _ =
        AoyagiResidualBlockCoordinateIndex.value
          (ChartLocalSuffixState.residualFactorProduct
            (sourceReadback (K := K) (ρ := ρ) E).C
            (Fin.last (M + 1)) 0 h0) := by
      rw [hfactor]

set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The fixed-base continuous edge family realised from a retained-passive
datum's edge matrices has exactly those fixed-base edge matrices.

This is the prescribed-matrix realisation theorem specialized to
retained-passive coordinate data.  It is not source-chart construction: the
edge family is defined from the supplied `data.edgeMatrix`. -/
theorem paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousReverseEdgeFamilyOf_retainedPassiveEdgeMatrix
    [∀ j, FiniteDimensional K (W j)]
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    (data :
      RetainedPassiveNonredundantCoordinateData
        (K := K) (ρ := Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀)) :
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
        (fun p : Fin (M + 1) ↦
          (paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices
              W B U₀ hU₀ data.edgeMatrix p :
            reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)) =
      data.edgeMatrix := by
  funext p
  exact
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousReverseEdgeFamilyOfMatrices
      (K := K) W B U₀ hU₀ data.edgeMatrix p

set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Source readback of the fixed-base continuous edge family realised from a
determinant-chart retained-passive datum recovers that datum. -/
theorem sourceReadback_paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousReverseEdgeFamilyOf_retainedPassiveEdgeMatrix_eq
    [∀ j, FiniteDimensional K (W j)]
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    (data :
      RetainedPassiveNonredundantCoordinateData
        (K := K) (ρ := Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀))
    (hdet : data.detChart) :
    sourceReadback (K := K) (ρ := Fin (Module.finrank K U₀))
        (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
          (fun p : Fin (M + 1) ↦
            (paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices
                W B U₀ hU₀ data.edgeMatrix p :
              reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ))) =
      data := by
  rw [
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousReverseEdgeFamilyOf_retainedPassiveEdgeMatrix
      (K := K) W B data]
  exact
    sourceReadback_edgeMatrix_eq
      (K := K) (ρ := Fin (Module.finrank K U₀))
      (data := data) hdet

set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The named retained-passive p.13 source chart has exactly the retained edge
matrices of its coordinate datum. -/
theorem paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13SourceChart_eq
    [∀ j, FiniteDimensional K (W j)]
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    (data :
      {data :
        RetainedPassiveNonredundantCoordinateData
          (K := K) (ρ := Fin (Module.finrank K U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) // data.detChart}) :
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
        (fun p : Fin (M + 1) ↦
          (paperEndpointFixedBaseRetainedPassiveP13SourceChart W B U₀ hU₀ data p :
            reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)) =
      data.1.edgeMatrix := by
  simpa [paperEndpointFixedBaseRetainedPassiveP13SourceChart] using
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousReverseEdgeFamilyOf_retainedPassiveEdgeMatrix
      (K := K) W B (U₀ := U₀) (hU₀ := hU₀) data.1

set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Source readback of the named retained-passive p.13 source chart recovers
the determinant-chart coordinate datum. -/
theorem sourceReadback_paperEndpointFixedBaseRetainedPassiveP13SourceChart_eq
    [∀ j, FiniteDimensional K (W j)]
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    (data :
      {data :
        RetainedPassiveNonredundantCoordinateData
          (K := K) (ρ := Fin (Module.finrank K U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) // data.detChart}) :
    sourceReadback (K := K) (ρ := Fin (Module.finrank K U₀))
        (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
          (fun p : Fin (M + 1) ↦
            (paperEndpointFixedBaseRetainedPassiveP13SourceChart W B U₀ hU₀ data p :
              reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ))) =
      data.1 := by
  simpa [paperEndpointFixedBaseRetainedPassiveP13SourceChart] using
    sourceReadback_paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousReverseEdgeFamilyOf_retainedPassiveEdgeMatrix_eq
      (K := K) W B (U₀ := U₀) (hU₀ := hU₀) data.1 data.2

set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The named retained-passive p.13 source chart lands in the fixed-base local
source set at every determinant-chart coordinate datum. -/
theorem paperEndpointFixedBaseRetainedPassiveP13SourceChart_mem_localSource
    [∀ j, FiniteDimensional K (W j)]
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    (data :
      {data :
        RetainedPassiveNonredundantCoordinateData
          (K := K) (ρ := Fin (Module.finrank K U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) // data.detChart}) :
    data ∈
      paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U₀ hU₀
        (paperEndpointFixedBaseRetainedPassiveP13SourceChart W B U₀ hU₀) := by
  change
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
        (fun p : Fin (M + 1) ↦
          (paperEndpointFixedBaseRetainedPassiveP13SourceChart W B U₀ hU₀ data p :
            reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)) ∈
      sourceRecursiveDetChartSet
        (K := K) (ρ := Fin (Module.finrank K U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀)
  rw [paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13SourceChart_eq
    (K := K) W B data]
  exact
    (mem_sourceRecursiveDetChartSet
      (K := K) (ρ := Fin (Module.finrank K U₀))
      (κ' := throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀)
      data.1.edgeMatrix).2
      (sourceRecursiveDetChart_edgeMatrix_of_detChart
        (K := K) (ρ := Fin (Module.finrank K U₀)) data.1 data.2)

set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The named retained-passive p.13 source chart is continuous as a map from
determinant-chart coordinate data to fixed-base continuous edge families. -/
theorem continuous_paperEndpointFixedBaseRetainedPassiveP13SourceChart
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))) :
    Continuous
      (fun data :
        {data :
          RetainedPassiveNonredundantCoordinateData
            (K := K) (ρ := Fin (Module.finrank K U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀) // data.detChart} ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceChart W B U₀ hU₀ data) := by
  simpa [paperEndpointFixedBaseRetainedPassiveP13SourceChart] using
    (paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices_continuous
      (K := K) W B U₀ hU₀).comp
      (continuous_edgeMatrix_detChart_subtype
        (ρ := Fin (Module.finrank K U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀)
        (K := K))

set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The named retained-passive p.13 source chart lands in the continuous
source edge-family set. -/
theorem paperEndpointFixedBaseRetainedPassiveP13SourceChart_mem_sourceEdgeFamilySet
    [∀ j, FiniteDimensional K (W j)]
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    (data :
      {data :
        RetainedPassiveNonredundantCoordinateData
          (K := K) (ρ := Fin (Module.finrank K U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) // data.detChart}) :
    paperEndpointFixedBaseRetainedPassiveP13SourceChart W B U₀ hU₀ data ∈
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet W B U₀ hU₀ := by
  change
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
        (fun p : Fin (M + 1) ↦
          (paperEndpointFixedBaseRetainedPassiveP13SourceChart W B U₀ hU₀ data p :
            reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)) ∈
      sourceRecursiveDetChartSet
        (K := K) (ρ := Fin (Module.finrank K U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀)
  rw [paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13SourceChart_eq
    (K := K) W B data]
  exact
    (mem_sourceRecursiveDetChartSet
      (K := K) (ρ := Fin (Module.finrank K U₀))
      (κ' := throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀)
      data.1.edgeMatrix).2
      (sourceRecursiveDetChart_edgeMatrix_of_detChart
        (K := K) (ρ := Fin (Module.finrank K U₀)) data.1 data.2)

set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Source readback of a continuous fixed-base edge family in the source set,
viewed as retained-passive determinant-chart coordinate data. -/
def paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyReadback
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (E :
      {E : ∀ p : Fin (M + 1),
          reverseVertex W p.castSucc →L[K] reverseVertex W p.succ //
        E ∈ paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet W B U₀ hU₀}) :
    {data :
      RetainedPassiveNonredundantCoordinateData
        (K := K) (ρ := Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) // data.detChart} :=
  let EMat :=
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
      (fun p : Fin (M + 1) ↦
        (E.1 p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ))
  have hmem :
      EMat ∈
        sourceRecursiveDetChartSet
          (K := K) (ρ := Fin (Module.finrank K U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) := by
    change
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
          (fun p : Fin (M + 1) ↦
            (E.1 p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)) ∈
        sourceRecursiveDetChartSet
          (K := K) (ρ := Fin (Module.finrank K U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀)
    exact E.2
  have hchart :
      sourceRecursiveDetChart (K := K) (ρ := Fin (Module.finrank K U₀)) EMat :=
    (mem_sourceRecursiveDetChartSet
      (K := K) (ρ := Fin (Module.finrank K U₀))
      (κ' := throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀)
      EMat).1 hmem
  ⟨sourceReadback (K := K) (ρ := Fin (Module.finrank K U₀)) EMat,
    sourceReadback_detChart_of_sourceRecursiveDetChart
      (K := K) (ρ := Fin (Module.finrank K U₀)) EMat hchart⟩

set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The fixed-base retained-passive determinant chart is homeomorphic to the
continuous source edge-family set cut out by the source-recursive determinant
chart condition. -/
def paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamily_homeomorph
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))) :
    {data :
      RetainedPassiveNonredundantCoordinateData
        (K := K) (ρ := Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) // data.detChart} ≃ₜ
      {E : ∀ p : Fin (M + 1),
          reverseVertex W p.castSucc →L[K] reverseVertex W p.succ //
        E ∈ paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet W B U₀ hU₀} where
  toFun data :=
    ⟨paperEndpointFixedBaseRetainedPassiveP13SourceChart W B U₀ hU₀ data,
      paperEndpointFixedBaseRetainedPassiveP13SourceChart_mem_sourceEdgeFamilySet
        (K := K) W B data⟩
  invFun E :=
    paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyReadback W B U₀ hU₀ E
  left_inv data := by
    apply Subtype.ext
    exact
      sourceReadback_paperEndpointFixedBaseRetainedPassiveP13SourceChart_eq
        (K := K) W B data
  right_inv E := by
    apply Subtype.ext
    let EMat :=
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
        (fun p : Fin (M + 1) ↦
          (E.1 p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ))
    have hmem :
        EMat ∈
          sourceRecursiveDetChartSet
            (K := K) (ρ := Fin (Module.finrank K U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀) := by
      change
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
            (fun p : Fin (M + 1) ↦
              (E.1 p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)) ∈
          sourceRecursiveDetChartSet
            (K := K) (ρ := Fin (Module.finrank K U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀)
      exact E.2
    have hchart :
        sourceRecursiveDetChart (K := K) (ρ := Fin (Module.finrank K U₀)) EMat :=
      (mem_sourceRecursiveDetChartSet
        (K := K) (ρ := Fin (Module.finrank K U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀)
        EMat).1 hmem
    have hreadEdge :
        (sourceReadback (K := K) (ρ := Fin (Module.finrank K U₀)) EMat).edgeMatrix =
          EMat :=
      edgeMatrix_sourceReadback_eq_of_sourceRecursiveDetChart
        (K := K) (ρ := Fin (Module.finrank K U₀)) EMat hchart
    simpa [paperEndpointFixedBaseRetainedPassiveP13SourceChart,
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyReadback, EMat, hreadEdge] using
      paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices_edgeMatrixOfReverseEdges
        (K := K) W B U₀ hU₀ E.1
  continuous_toFun :=
    (continuous_paperEndpointFixedBaseRetainedPassiveP13SourceChart
      (K := K) W B U₀ hU₀).subtype_mk _
  continuous_invFun := by
    let toSourceMatrix :
        {E : ∀ p : Fin (M + 1),
            reverseVertex W p.castSucc →L[K] reverseVertex W p.succ //
          E ∈ paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet W B U₀ hU₀} →
          {EMat : ∀ p : Fin (M + 1),
              Matrix
                (Fin (Module.finrank K U₀) ⊕
                  throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ p.succ)
                (Fin (Module.finrank K U₀) ⊕
                  throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K //
            sourceRecursiveDetChart (K := K) (ρ := Fin (Module.finrank K U₀)) EMat} :=
      fun E ↦
        let EMat :=
          paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
            (fun p : Fin (M + 1) ↦
              (E.1 p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ))
        have hmem :
            EMat ∈
              sourceRecursiveDetChartSet
                (K := K) (ρ := Fin (Module.finrank K U₀))
                (κ' := throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀) := by
          change
            paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
                (fun p : Fin (M + 1) ↦
                  (E.1 p :
                    reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)) ∈
              sourceRecursiveDetChartSet
                (K := K) (ρ := Fin (Module.finrank K U₀))
                (κ' := throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀)
          exact E.2
        ⟨EMat,
          (mem_sourceRecursiveDetChartSet
            (K := K) (ρ := Fin (Module.finrank K U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀)
            EMat).1 hmem⟩
    have hEdgeMat :
        Continuous fun E :
          {E : ∀ p : Fin (M + 1),
              reverseVertex W p.castSucc →L[K] reverseVertex W p.succ //
            E ∈ paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet W B U₀ hU₀} ↦
          paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
            (fun p : Fin (M + 1) ↦
              (E.1 p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)) :=
      (paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuous
        (K := K) W B U₀ hU₀).comp continuous_subtype_val
    have hToSourceMatrix : Continuous toSourceMatrix := by
      exact hEdgeMat.subtype_mk _
    have hReadValue :
        Continuous fun E :
          {E : ∀ p : Fin (M + 1),
              reverseVertex W p.castSucc →L[K] reverseVertex W p.succ //
            E ∈ paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet W B U₀ hU₀} ↦
          sourceReadback (K := K) (ρ := Fin (Module.finrank K U₀))
            (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
              (fun p : Fin (M + 1) ↦
                (E.1 p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ))) := by
      simpa [toSourceMatrix, Function.comp_def] using
        (continuous_sourceReadback_sourceRecursiveDetChart_subtype
          (ρ := Fin (Module.finrank K U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀)
          (K := K)).comp hToSourceMatrix
    simpa [paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyReadback] using
      hReadValue.subtype_mk _

set_option linter.unusedSectionVars false in
/-- Source readback recovers supplied retained-passive coordinate data when
the fixed-base edge matrices are the coordinate data's retained-passive source
edge matrix.

This is a pointwise inverse bridge for the fixed-base p.13 source side.  The
determinant-chart hypothesis on `data` is essential: it is exactly the
hypothesis used by `sourceReadback_edgeMatrix_eq`. -/
theorem sourceReadback_paperEndpointFixedBaseEdgeMatrix_eq_retainedPassiveData_of_edgeMatrix_eq
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin (M + 1),
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    (x : α)
    (data :
      RetainedPassiveNonredundantCoordinateData
        (K := K) (ρ := Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀))
    (hdet : data.detChart)
    (hedge :
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
        (fun p : Fin (M + 1) ↦
          (Cedge x p :
            reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)) =
        data.edgeMatrix) :
    sourceReadback (K := K) (ρ := Fin (Module.finrank K U₀))
        (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
          (fun p : Fin (M + 1) ↦
            (Cedge x p :
              reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ))) =
      data := by
  rw [hedge]
  exact
    sourceReadback_edgeMatrix_eq
      (K := K) (ρ := Fin (Module.finrank K U₀))
      (data := data) hdet

set_option linter.unusedSectionVars false in
/-- Membership in the retained-passive local source is exactly the existing
fixed-base recursive determinant-chart predicate. -/
theorem mem_paperEndpointFixedBaseRetainedPassiveP13LocalSource_iff_recursiveDetCharts
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin (M + 1),
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (x : α) :
    x ∈ paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U₀ hU₀ Cedge ↔
      paperEndpointFixedBaseContinuousEdgesRecursiveDetCharts W B U₀ hU₀ Cedge x := by
  have hE :
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
          (fun p : Fin (M + 1) ↦
            (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)) =
        (fun q : Fin (M + 1) ↦
          LinearMap.toMatrix
            (paperEndpointFixedBaseBasis W B U₀ hU₀ q.castSucc)
            (paperEndpointFixedBaseBasis W B U₀ hU₀ q.succ)
            (Cedge x q : reverseVertex W q.castSucc →ₗ[K] reverseVertex W q.succ)) := by
    funext q
    rfl
  simp [paperEndpointFixedBaseRetainedPassiveP13LocalSource,
    paperEndpointFixedBaseContinuousEdgesRecursiveDetCharts,
    hE,
    ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.mem_sourceRecursiveDetChartSet,
    ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceRecursiveDetChart_iff,
    ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadbackTransformedEdge,
    ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadbackSuffixState]

set_option linter.style.longLine false in
/-- At a self-base continuous edge family, the retained-passive p.13 local
source is a neighborhood of the base parameter. -/
theorem paperEndpointFixedBaseRetainedPassiveP13LocalSource_mem_nhds_of_selfBase
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin (M + 1),
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ =
        fun p : Fin (M + 1) ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p)) :
    paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U₀ hU₀ Cedge ∈
      nhds x₀ := by
  have hchart₀ :=
    paperEndpointFixedBaseContinuousEdges_selfBase_recursiveBprev_detChart
      W B U₀ hU₀ Cedge hbase
  have hcharts :
      {x : α |
        paperEndpointFixedBaseContinuousEdgesRecursiveDetCharts W B U₀ hU₀ Cedge x} ∈
        nhds x₀ := by
    have hraw :=
      paperEndpointFixedBaseContinuousEdges_recursiveBprev_mem_nhds_transformed_identityCornerDetChart
        W B U₀ hU₀ Cedge hCedge hchart₀
    simpa [paperEndpointFixedBaseContinuousEdgesRecursiveDetCharts] using hraw
  exact Filter.mem_of_superset hcharts (by
    intro x hx
    exact
      (mem_paperEndpointFixedBaseRetainedPassiveP13LocalSource_iff_recursiveDetCharts
        W B U₀ hU₀ Cedge x).2 hx)

/-- A globally continuous edge family gives a continuous fixed-base edge-matrix
map into the retained-passive source-family space. -/
theorem continuous_paperEndpointFixedBaseRetainedPassiveP13EdgeMatrix_of_continuous
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin (M + 1),
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (hCedge : Continuous Cedge) :
    Continuous fun x : α ↦
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
        (fun p : Fin (M + 1) ↦
          (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousAt
      W B U₀ hU₀ Cedge hCedge.continuousAt

/-- Under global continuity of the edge family, the retained-passive p.13
local source is measurable. -/
theorem measurableSet_paperEndpointFixedBaseRetainedPassiveP13LocalSource_of_continuous
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin (M + 1),
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (hCedge : Continuous Cedge) :
    MeasurableSet
      (paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U₀ hU₀ Cedge) := by
  have hE :=
    continuous_paperEndpointFixedBaseRetainedPassiveP13EdgeMatrix_of_continuous
      W B U₀ hU₀ Cedge hCedge
  let sourceSet :=
    ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceRecursiveDetChartSet
      (K := K) (ρ := Fin (Module.finrank K U₀))
      (κ' := throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀)
  have hopen : IsOpen sourceSet := by
    dsimp [sourceSet]
    exact RetainedPassiveNonredundantCoordinateData.isOpen_sourceRecursiveDetChartSet
  have hpre :
      IsOpen (paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U₀ hU₀ Cedge) := by
    simpa [paperEndpointFixedBaseRetainedPassiveP13LocalSource] using
      hE.isOpen_preimage sourceSet hopen
  exact hpre.measurableSet

/-- The retained-passive determinant-chart preimage is an open-neighborhood
local source, giving the handoff-shaped source-rank inclusion locally. -/
theorem exists_open_paperEndpointFixedBaseRetainedPassiveP13LocalSource_coverage_of_selfBase
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin (M + 1),
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (r : ℕ) (rEdge : Fin (M + 1) → ℕ)
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ =
        fun p : Fin (M + 1) ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p)) :
    ∃ Ulocal : Set α, IsOpen Ulocal ∧ x₀ ∈ Ulocal ∧
      Ulocal ⊆ paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U₀ hU₀ Cedge ∧
      Ulocal ∩ paperEndpointFixedBaseSourceRankStratum
          (K := K) W B Cedge r rEdge ⊆
        Ulocal ∩ paperEndpointFixedBaseRetainedPassiveP13LocalSource
          W B U₀ hU₀ Cedge := by
  have hlocal :
      paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U₀ hU₀ Cedge ∈
        nhds x₀ :=
    paperEndpointFixedBaseRetainedPassiveP13LocalSource_mem_nhds_of_selfBase
      W B U₀ hU₀ Cedge hCedge hbase
  rcases mem_nhds_iff.mp hlocal with ⟨Ulocal, hUlocal_sub, hUlocal_open, hx₀Ulocal⟩
  refine ⟨Ulocal, hUlocal_open, hx₀Ulocal, hUlocal_sub, ?_⟩
  intro x hx
  exact ⟨hx.1, hUlocal_sub hx.1⟩

end RetainedPassiveLocalSource

end Aoyagi
end DLN
end DLNFibre
