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
