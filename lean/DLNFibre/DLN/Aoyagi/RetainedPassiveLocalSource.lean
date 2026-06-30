import DLNFibre.DLN.Aoyagi.ProductReductionBoundary
import DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates
import DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesTopology

/-!
# Retained-passive local source in fixed endpoint bases

This file ties the retained-passive source-recursive determinant chart to the
fixed-base endpoint edge-family map used by the p.13 local-measure handoff.
It proves determinant-chart local coverage near the self-base point,
the raw-order source-chart image inside the reduced retained-passive
coordinates, measurability under global source-edge continuity, and a finite
residual readout through the retained-passive source readback.  It does not
prove original-source exact-rank coverage, original-prior measure transport, a
Jacobian theorem, normal crossings, pole order, or RLCT extraction.
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

/-- The ambient fixed-base retained-passive p.13 coordinate-to-source
edge-family map, defined on all retained-passive coordinate data. -/
def paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (data :
      RetainedPassiveNonredundantCoordinateData
        (K := K) (ρ := Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀)) :
    ∀ p : Fin (M + 1),
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ :=
  paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices
    W B U₀ hU₀ data.edgeMatrix

/-- The canonical raw-order retained-passive source chart obtained by first
reading a raw-order tuple back into determinant-chart coordinates, then
realising its retained edge matrices as fixed-base continuous reversed edge
maps. -/
def paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (y :
      TopologyTuple (Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) K) :
    ∀ p : Fin (M + 1),
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ :=
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U₀ hU₀
    (ofTopologyTuple (K := K) (ρ := Fin (Module.finrank K U₀)) (κ' := κ')
      (topologyTupleEdgeRawOrderInverse
        (K := K) (ρ := Fin (Module.finrank K U₀)) (κ' := κ') y))

set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- On the determinant chart, the public raw-order source chart after the
raw-order tuple map is the direct fixed-base source family attached to the
original retained-passive tuple.

This is a pointwise source-chart presentation identity.  It is not source-rank
coverage, selected-entry factor alignment, pivot provenance, measure transport,
normal crossings, pole order, or RLCT extraction. -/
theorem paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_topologyTupleEdgeRawOrder_eq_sourceEdgeFamilyOfData
    [∀ j, FiniteDimensional K (W j)]
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {z :
      TopologyTuple (Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) K}
    (hz : z ∈
      topologyTupleDetChartSet
        (K := K) (ρ := Fin (Module.finrank K U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀)) :
    paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart W B U₀ hU₀
        (topologyTupleEdgeRawOrder
          (K := K) (ρ := Fin (Module.finrank K U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) z) =
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U₀ hU₀
        (ofTopologyTuple (K := K) (ρ := Fin (Module.finrank K U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) z) := by
  let ρ := Fin (Module.finrank K U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  have hinv :
      topologyTupleEdgeRawOrderInverse (K := K) (ρ := ρ) (κ' := κ')
          (topologyTupleEdgeRawOrder (K := K) (ρ := ρ) (κ' := κ') z) =
        z :=
    topologyTupleEdgeRawOrderInverse_topologyTupleEdgeRawOrder
      (K := K) (ρ := ρ) (κ' := κ') hz
  simpa [paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart, ρ, κ'] using
    congrArg
      (fun w : TopologyTuple ρ κ' K ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U₀ hU₀
          (ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') w))
      hinv

set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- For a retained-passive determinant-chart datum, the raw-order p.13 source
chart evaluated on the raw-order tuple of `topologyTuple data` is the direct
fixed-base p.13 source edge family of `data`.

This is a pointwise source-family presentation identity.  It is not a
source-image equality, pushforward-measure theorem, source-rank coverage,
Jacobian comparison, normal crossings, pole order, or RLCT extraction. -/
theorem paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_topologyTupleEdgeRawOrder_topologyTuple_eq_sourceEdgeFamilyOfData
    [∀ j, FiniteDimensional K (W j)]
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    (data :
      RetainedPassiveNonredundantCoordinateData
        (K := K) (ρ := Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀))
    (hdet : data.detChart) :
    paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart W B U₀ hU₀
        (topologyTupleEdgeRawOrder
          (K := K) (ρ := Fin (Module.finrank K U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀)
          (topologyTuple data)) =
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U₀ hU₀
        data := by
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  have hz :
      topologyTuple data ∈
        topologyTupleDetChartSet
          (K := K) (ρ := Fin (Module.finrank K U₀)) (κ' := κ') :=
    (topologyTuple_mem_topologyTupleDetChartSet
      (K := K) (ρ := Fin (Module.finrank K U₀)) (κ' := κ') data).2 hdet
  simpa [κ'] using
    paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_topologyTupleEdgeRawOrder_eq_sourceEdgeFamilyOfData
      (K := K) (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) (z := topologyTuple data) hz

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
/-- The parameterized retained-passive p.13 local source is the preimage of
the ambient fixed-base continuous source edge-family set. -/
theorem paperEndpointFixedBaseRetainedPassiveP13LocalSource_eq_preimage_sourceEdgeFamilySet
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin (M + 1),
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ) :
    paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U₀ hU₀ Cedge =
      Cedge ⁻¹'
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet W B U₀ hU₀ := by
  rfl

set_option linter.unusedSectionVars false in
/-- A raw-order target point realized by the fixed-base edge family lands in
the retained-passive p.13 local source. -/
theorem
    paperEndpointFixedBaseRetainedPassiveP13LocalSource_mem_of_edgeFamilyOfRawOrderTuple_realization
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin (M + 1),
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (sourceChart :
      TopologyTuple (Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) K → α)
    {y :
      TopologyTuple (Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) K}
    (hy : y ∈
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := K) (ρ := Fin (Module.finrank K U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀))
    (hrealize :
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
          (fun p : Fin (M + 1) ↦
            (Cedge (sourceChart y) p :
              reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)) =
        edgeFamilyOfRawOrderTuple
          (K := K) (ρ := Fin (Module.finrank K U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) y) :
    sourceChart y ∈
      paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U₀ hU₀ Cedge := by
  dsimp [paperEndpointFixedBaseRetainedPassiveP13LocalSource]
  rw [hrealize]
  simpa [topologyTupleRawOrderSourceRecursiveDetChartSet] using hy

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
/-- The ambient retained-passive p.13 source edge-family map has exactly the
retained edge matrices of its coordinate datum. -/
theorem paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13SourceEdgeFamilyOfData_eq
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
          (paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U₀ hU₀ data p :
            reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)) =
      data.edgeMatrix := by
  simpa [paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData] using
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousReverseEdgeFamilyOf_retainedPassiveEdgeMatrix
      (K := K) W B (U₀ := U₀) (hU₀ := hU₀) data

set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The retained-passive realised p.13 source edge family belongs to Aoyagi's
source-shaped rank stratum when the base-product rank, realised edge-matrix
ranks, and source inequalities are supplied explicitly.

This is a membership constructor only.  It does not prove source-rank coverage,
exact-rank openness, or any numerical edge-rank formula. -/
theorem paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData_mem_sourceRankStratum_of_edgeMatrix_rank
    [∀ j, FiniteDimensional K (W j)]
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    (data :
      RetainedPassiveNonredundantCoordinateData
        (K := K) (ρ := Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀))
    {r : ℕ} {rEdge : Fin (M + 1) → ℕ}
    (hprod : Module.finrank K (LinearMap.range (paperTotalMap W B)) = r)
    (hedge : ∀ p : Fin (M + 1), (data.edgeMatrix p).rank = rEdge p)
    (hle : ∀ p : Fin (M + 1), r ≤ rEdge p) :
    paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
        W B U₀ hU₀ data ∈
      paperEndpointFixedBaseSourceRankStratum
        (K := K) (N := M + 1) W B
        (fun E : ∀ p : Fin (M + 1),
            reverseVertex W p.castSucc →L[K] reverseVertex W p.succ ↦ E)
        r rEdge := by
  classical
  let Eclm : ∀ p : Fin (M + 1),
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ :=
    paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
      W B U₀ hU₀ data
  let Elin : ∀ p : Fin (M + 1),
      reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
    fun p ↦ (Eclm p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
  have hmat :=
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13SourceEdgeFamilyOfData_eq
      (K := K) W B (U₀ := U₀) (hU₀ := hU₀) data
  refine ⟨hprod, ?_, hle⟩
  intro p
  have hedgeMatrix :
      (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ Elin p).rank =
        rEdge p := by
    calc
      (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ Elin p).rank =
          (data.edgeMatrix p).rank := by
        rw [congrFun hmat p]
      _ = rEdge p := hedge p
  have hedgeRange :
      Module.finrank K (LinearMap.range (Elin p)) = rEdge p := by
    calc
      Module.finrank K (LinearMap.range (Elin p)) =
          (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ Elin p).rank := by
        exact
          (rank_paperEndpointFixedBaseEdgeMatrixOfReverseEdges_eq_finrank_range
            (K := K) (W := W) (B := B) U₀ hU₀ Elin p).symm
      _ = rEdge p := hedgeMatrix
  simpa [Eclm, Elin] using hedgeRange

set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- A determinant-chart retained-passive datum belongs to Aoyagi's source-shaped
rank stratum when its residual block ranks realise the supplied source-edge
rank differences.

This theorem uses the retained-passive edge-rank formula to turn
`rank(C_p) = rEdge p - r` into exact source-edge ranks.  It still assumes the
base-product rank equality and the source inequalities explicitly. -/
theorem paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData_mem_sourceRankStratum_of_C_rank
    [∀ j, FiniteDimensional K (W j)]
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    (data :
      RetainedPassiveNonredundantCoordinateData
        (K := K) (ρ := Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀))
    (hdet : data.detChart)
    {r : ℕ} {rEdge : Fin (M + 1) → ℕ}
    (hprod : Module.finrank K (LinearMap.range (paperTotalMap W B)) = r)
    (hC : ∀ p : Fin (M + 1), (data.C p).rank = rEdge p - r)
    (hle : ∀ p : Fin (M + 1), r ≤ rEdge p) :
    paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
        W B U₀ hU₀ data ∈
      paperEndpointFixedBaseSourceRankStratum
        (K := K) (N := M + 1) W B
        (fun E : ∀ p : Fin (M + 1),
            reverseVertex W p.castSucc →L[K] reverseVertex W p.succ ↦ E)
        r rEdge := by
  classical
  have hUrank : Fintype.card (Fin (Module.finrank K U₀)) = r := by
    have hfin :
        Module.finrank K U₀ = r :=
      (paperEndpointBasepointCertificate_of_isCompl W B U₀ hU₀).finrank_eq_range.trans hprod
    simpa [Fintype.card_fin] using hfin
  have hedge : ∀ p : Fin (M + 1), (data.edgeMatrix p).rank = rEdge p := by
    intro p
    have hEdgeFormula :
        (data.edgeMatrix p).rank =
          Fintype.card (Fin (Module.finrank K U₀)) + (data.C p).rank :=
      ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.rank_edgeMatrix
        (K := K) (ρ := Fin (Module.finrank K U₀)) data hdet p
    have hsum : r + (data.C p).rank = rEdge p := by
      have hp := hC p
      have hle' := hle p
      omega
    calc
      (data.edgeMatrix p).rank =
          Fintype.card (Fin (Module.finrank K U₀)) + (data.C p).rank := hEdgeFormula
      _ = r + (data.C p).rank := by rw [hUrank]
      _ = rEdge p := hsum
  exact
    paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData_mem_sourceRankStratum_of_edgeMatrix_rank
      (K := K) W B (U₀ := U₀) (hU₀ := hU₀) data hprod hedge hle

set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- A determinant-chart retained-passive datum belongs to Aoyagi's source-shaped
rank stratum when the supplied edge ranks are exactly `r + rank(C_p)`.

This is the same conditional membership bridge as
`..._of_C_rank`, but avoids exposing truncated natural subtraction to callers.
It does not prove source-rank coverage or exact-rank openness. -/
theorem paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData_mem_sourceRankStratum_of_C_rank_add_eq
    [∀ j, FiniteDimensional K (W j)]
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    (data :
      RetainedPassiveNonredundantCoordinateData
        (K := K) (ρ := Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀))
    (hdet : data.detChart)
    {r : ℕ} {rEdge : Fin (M + 1) → ℕ}
    (hprod : Module.finrank K (LinearMap.range (paperTotalMap W B)) = r)
    (hrEdge : ∀ p : Fin (M + 1), r + (data.C p).rank = rEdge p) :
    paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
        W B U₀ hU₀ data ∈
      paperEndpointFixedBaseSourceRankStratum
        (K := K) (N := M + 1) W B
        (fun E : ∀ p : Fin (M + 1),
            reverseVertex W p.castSucc →L[K] reverseVertex W p.succ ↦ E)
        r rEdge := by
  classical
  have hC : ∀ p : Fin (M + 1), (data.C p).rank = rEdge p - r := by
    intro p
    have hp := hrEdge p
    omega
  have hle : ∀ p : Fin (M + 1), r ≤ rEdge p := by
    intro p
    have hp := hrEdge p
    omega
  exact
    paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData_mem_sourceRankStratum_of_C_rank
      (K := K) W B (U₀ := U₀) (hU₀ := hU₀) data hdet hprod hC hle

set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- If a retained-passive datum's realised p.13 source edge family lies in
Aoyagi's source-shaped rank stratum, then its stored residual blocks have ranks
`rEdge p - r`.

This theorem consumes source-rank membership; it does not prove source-rank
coverage for retained-passive coordinates or for the Case 2 selected-entry
chart. -/
theorem rank_C_of_retainedPassiveP13SourceEdgeFamilyOfData_mem_sourceRankStratum
    [∀ j, FiniteDimensional K (W j)]
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    (data :
      RetainedPassiveNonredundantCoordinateData
        (K := K) (ρ := Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀))
    (hdet : data.detChart)
    {r : ℕ} {rEdge : Fin (M + 1) → ℕ}
    (hsrc :
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
          W B U₀ hU₀ data ∈
        paperEndpointFixedBaseSourceRankStratum
          (K := K) (N := M + 1) W B
          (fun E : ∀ p : Fin (M + 1),
              reverseVertex W p.castSucc →L[K] reverseVertex W p.succ ↦ E)
          r rEdge)
    (p : Fin (M + 1)) :
    (data.C p).rank = rEdge p - r := by
  classical
  let Eclm : ∀ p : Fin (M + 1),
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ :=
    paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
      W B U₀ hU₀ data
  let Elin : ∀ p : Fin (M + 1),
      reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
    fun p ↦ (Eclm p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
  have hmat :=
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13SourceEdgeFamilyOfData_eq
      (K := K) W B (U₀ := U₀) (hU₀ := hU₀) data
  have hedgeRank : (data.edgeMatrix p).rank = rEdge p := by
    calc
      (data.edgeMatrix p).rank =
          (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ Elin p).rank := by
        exact (congrFun hmat p).symm ▸ rfl
      _ = Module.finrank K (LinearMap.range (Elin p)) := by
        exact
          rank_paperEndpointFixedBaseEdgeMatrixOfReverseEdges_eq_finrank_range
            (K := K) (W := W) (B := B) U₀ hU₀ Elin p
      _ = rEdge p := by
        simpa [Eclm, Elin] using hsrc.2.1 p
  have hEdgeFormula :
      (data.edgeMatrix p).rank =
        Fintype.card (Fin (Module.finrank K U₀)) + (data.C p).rank :=
    ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.rank_edgeMatrix
      (K := K) (ρ := Fin (Module.finrank K U₀)) data hdet p
  have hUrank : Module.finrank K U₀ = r :=
    (paperEndpointBasepointCertificate_of_isCompl W B U₀ hU₀).finrank_eq_range.trans hsrc.1
  have hsum : r + (data.C p).rank = rEdge p := by
    have h := hEdgeFormula.symm.trans hedgeRank
    simpa [Fintype.card_fin, hUrank] using h
  omega

set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- On the raw-order source-recursive determinant chart, the canonical
raw-order retained-passive source chart has exactly the raw-order tuple's edge
matrices. -/
theorem paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13RawOrderSourceChart_eq
    [∀ j, FiniteDimensional K (W j)]
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {y :
      TopologyTuple (Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) K}
    (hy : y ∈
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := K) (ρ := Fin (Module.finrank K U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀)) :
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
        (fun p : Fin (M + 1) ↦
          (paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart W B U₀ hU₀ y p :
            reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)) =
      edgeFamilyOfRawOrderTuple
        (K := K) (ρ := Fin (Module.finrank K U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) y := by
  let ρ := Fin (Module.finrank K U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  have hraw :
      topologyTupleEdgeRawOrder (K := K) (ρ := ρ) (κ' := κ')
          (topologyTupleEdgeRawOrderInverse (K := K) (ρ := ρ) (κ' := κ') y) =
        y :=
    topologyTupleEdgeRawOrder_topologyTupleEdgeRawOrderInverse
      (K := K) (ρ := ρ) (κ' := κ') hy
  calc
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
        (fun p : Fin (M + 1) ↦
          (paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart W B U₀ hU₀ y p :
            reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)) =
        (ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ')
          (topologyTupleEdgeRawOrderInverse
            (K := K) (ρ := ρ) (κ' := κ') y)).edgeMatrix := by
      simpa [paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart, ρ, κ'] using
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13SourceEdgeFamilyOfData_eq
          (K := K) W B (U₀ := U₀) (hU₀ := hU₀)
          (ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ')
            (topologyTupleEdgeRawOrderInverse
              (K := K) (ρ := ρ) (κ' := κ') y))
    _ =
        topologyTupleEdgeMatrix
          (K := K) (ρ := ρ) (κ' := κ')
          (topologyTupleEdgeRawOrderInverse
            (K := K) (ρ := ρ) (κ' := κ') y) := by
      rfl
    _ =
        edgeFamilyOfRawOrderTuple (K := K) (ρ := ρ) (κ' := κ')
          (topologyTupleEdgeRawOrder (K := K) (ρ := ρ) (κ' := κ')
            (topologyTupleEdgeRawOrderInverse
              (K := K) (ρ := ρ) (κ' := κ') y)) := by
      exact
        (edgeFamilyOfRawOrderTuple_topologyTupleEdgeRawOrder
          (K := K) (ρ := ρ) (κ' := κ')
          (topologyTupleEdgeRawOrderInverse
            (K := K) (ρ := ρ) (κ' := κ') y)).symm
    _ = edgeFamilyOfRawOrderTuple (K := K) (ρ := ρ) (κ' := κ') y := by
      rw [hraw]

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
/-- The fixed-base continuous source edge-family set is open. -/
theorem isOpen_paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))) :
    IsOpen (paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet W B U₀ hU₀) := by
  let sourceSet :=
    sourceRecursiveDetChartSet
      (K := K) (ρ := Fin (Module.finrank K U₀))
      (κ' := throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀)
  have hmap :
      Continuous
        (fun E : ∀ p : Fin (M + 1),
            reverseVertex W p.castSucc →L[K] reverseVertex W p.succ ↦
          paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
            (fun p : Fin (M + 1) ↦
              (E p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ))) :=
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuous
      (K := K) W B U₀ hU₀
  have hopen : IsOpen sourceSet := by
    dsimp [sourceSet]
    exact isOpen_sourceRecursiveDetChartSet
      (K := K) (ρ := Fin (Module.finrank K U₀))
      (κ' := throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀)
  simpa [paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet, sourceSet] using
    hmap.isOpen_preimage sourceSet hopen

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
set_option linter.style.longLine false in
/-- The canonical raw-order retained-passive source chart maps the raw-order
source-recursive determinant chart onto exactly the fixed-base continuous
source edge-family set.

This is a reduced retained-passive source-image theorem.  It is not original
DLN source-rank coverage, measure transport, a Jacobian theorem, normal
crossings, pole order, or RLCT extraction. -/
theorem image_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_eq_sourceEdgeFamilySet
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))) :
    paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart W B U₀ hU₀ ''
        topologyTupleRawOrderSourceRecursiveDetChartSet
          (K := K) (ρ := Fin (Module.finrank K U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) =
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet W B U₀ hU₀ := by
  let ρ := Fin (Module.finrank K U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  ext E
  constructor
  · rintro ⟨y, hy, rfl⟩
    change
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
          (fun p : Fin (M + 1) ↦
            (paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart W B U₀ hU₀ y p :
              reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)) ∈
        sourceRecursiveDetChartSet (K := K) (ρ := ρ) (κ' := κ')
    rw [paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13RawOrderSourceChart_eq
      (K := K) W B (U₀ := U₀) (hU₀ := hU₀) (y := y)
      (hy := by simpa [ρ, κ'] using hy)]
    simpa [topologyTupleRawOrderSourceRecursiveDetChartSet, ρ, κ'] using hy
  · intro hE
    let EMat :=
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
        (fun p : Fin (M + 1) ↦
          (E p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ))
    have hsource :
        EMat ∈ sourceRecursiveDetChartSet (K := K) (ρ := ρ) (κ' := κ') := by
      simpa [paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet, ρ, κ', EMat] using hE
    have hchart : sourceRecursiveDetChart (K := K) (ρ := ρ) EMat :=
      (mem_sourceRecursiveDetChartSet
        (K := K) (ρ := ρ) (κ' := κ') EMat).1 hsource
    let data := sourceReadback (K := K) (ρ := ρ) EMat
    have hdet : data.detChart :=
      sourceReadback_detChart_of_sourceRecursiveDetChart
        (K := K) (ρ := ρ) EMat hchart
    let z : TopologyTuple ρ κ' K := topologyTuple data
    let y : TopologyTuple ρ κ' K :=
      topologyTupleEdgeRawOrder (K := K) (ρ := ρ) (κ' := κ') z
    have hzdet :
        z ∈ topologyTupleDetChartSet (K := K) (ρ := ρ) (κ' := κ') := by
      simpa [z] using hdet
    have hy :
        y ∈ topologyTupleRawOrderSourceRecursiveDetChartSet
          (K := K) (ρ := ρ) (κ' := κ') :=
      mapsTo_topologyTupleEdgeRawOrder_detChartSet_rawOrderSourceRecursiveDetChartSet
        (K := K) (ρ := ρ) (κ' := κ') hzdet
    refine ⟨y, hy, ?_⟩
    have hinv :
        topologyTupleEdgeRawOrderInverse (K := K) (ρ := ρ) (κ' := κ') y = z := by
      simpa [y] using
        topologyTupleEdgeRawOrderInverse_topologyTupleEdgeRawOrder
          (K := K) (ρ := ρ) (κ' := κ') hzdet
    have hreadEdge : data.edgeMatrix = EMat :=
      edgeMatrix_sourceReadback_eq_of_sourceRecursiveDetChart
        (K := K) (ρ := ρ) EMat hchart
    have hsourceChart_eq :
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U₀ hU₀ data = E := by
      simpa [paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData, EMat, hreadEdge] using
        paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices_edgeMatrixOfReverseEdges
          (K := K) W B U₀ hU₀ E
    calc
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart W B U₀ hU₀ y =
          paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U₀ hU₀
            (ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ')
              (topologyTupleEdgeRawOrderInverse (K := K) (ρ := ρ) (κ' := κ') y)) := by
        rfl
      _ = paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U₀ hU₀ data := by
        rw [hinv]
        simp [z]
      _ = E := hsourceChart_eq

set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The canonical raw-order retained-passive source chart as a homeomorphism
from the raw-order source-recursive determinant chart to the fixed-base
continuous source edge-family set.

This is a reduced retained-passive local-inverse package.  It is not original
DLN source-rank coverage, measure transport, a Jacobian theorem, normal
crossings, pole order, or RLCT extraction. -/
def paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceEdgeFamily_homeomorph
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))) :
    topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := K) (ρ := Fin (Module.finrank K U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ≃ₜ
      {E : ∀ p : Fin (M + 1),
          reverseVertex W p.castSucc →L[K] reverseVertex W p.succ //
        E ∈ paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet W B U₀ hU₀} :=
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  (topologyTupleDetChartSet_rawOrderSourceRecursiveDetChartSet_homeomorph
      (K := K) (ρ := Fin (Module.finrank K U₀)) (κ' := κ')).symm.trans
    ((detChart_topologyTupleDetChartSet_homeomorph
        (K := K) (ρ := Fin (Module.finrank K U₀)) (κ' := κ')).symm.trans
      (paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamily_homeomorph
        (K := K) W B U₀ hU₀))

set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The `toFun` of the raw-order source-family homeomorphism is the public
canonical raw-order source chart. -/
theorem paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceEdgeFamily_homeomorph_apply
    [∀ j, FiniteDimensional K (W j)]
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    (y :
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := K) (ρ := Fin (Module.finrank K U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀)) :
    (paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceEdgeFamily_homeomorph
        (K := K) W B U₀ hU₀ y).1 =
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart W B U₀ hU₀ y.1 := by
  simp [paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceEdgeFamily_homeomorph,
    paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart,
    paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamily_homeomorph,
    detChart_topologyTupleDetChartSet_homeomorph,
    topologyTupleDetChartSet_rawOrderSourceRecursiveDetChartSet_homeomorph,
    paperEndpointFixedBaseRetainedPassiveP13SourceChart,
    paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData]

set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The fixed-base retained-passive determinant chart as an ambient open
partial homeomorphism from retained-passive coordinates to continuous source
edge families.

The source is `detChartSet`; the target is the fixed-base continuous
source-recursive determinant chart.  This is not source-rank coverage, measure
transport, a Jacobian theorem, normal crossings, pole order, or RLCT
extraction. -/
def paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamily_openPartialHomeomorph
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))) :
    OpenPartialHomeomorph
      (RetainedPassiveNonredundantCoordinateData
        (K := K) (ρ := Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀))
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[K] reverseVertex W p.succ) :=
  let κ' := throughSubspaceEndpointComplementIndex
    (reverseVertex W) (reverseEdge W B) U₀
  let S : Set
      (RetainedPassiveNonredundantCoordinateData
        (K := K) (ρ := Fin (Module.finrank K U₀)) κ') :=
    detChartSet (K := K) (ρ := Fin (Module.finrank K U₀)) (κ' := κ')
  let T : Set (∀ p : Fin (M + 1),
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ) :=
    paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet W B U₀ hU₀
  { toFun := fun data ↦
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U₀ hU₀ data
    invFun := fun E ↦
      sourceReadback (K := K) (ρ := Fin (Module.finrank K U₀))
        (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
          (fun p : Fin (M + 1) ↦
            (E p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)))
    source := S
    target := T
    map_source' := by
      intro data hdata
      have hdet : data.detChart :=
        (mem_detChartSet
          (K := K) (ρ := Fin (Module.finrank K U₀)) (κ' := κ') data).1 hdata
      change
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
            (fun p : Fin (M + 1) ↦
              (paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
                W B U₀ hU₀ data p :
                reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)) ∈
          sourceRecursiveDetChartSet
            (K := K) (ρ := Fin (Module.finrank K U₀)) (κ' := κ')
      rw [paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13SourceEdgeFamilyOfData_eq
        (K := K) W B data]
      exact
        (mem_sourceRecursiveDetChartSet
          (K := K) (ρ := Fin (Module.finrank K U₀)) (κ' := κ')
          data.edgeMatrix).2
          (sourceRecursiveDetChart_edgeMatrix_of_detChart
            (K := K) (ρ := Fin (Module.finrank K U₀)) data hdet)
    map_target' := by
      intro E hE
      let EMat :=
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
          (fun p : Fin (M + 1) ↦
            (E p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ))
      have hchart :
          sourceRecursiveDetChart (K := K) (ρ := Fin (Module.finrank K U₀)) EMat := by
        exact
          (mem_sourceRecursiveDetChartSet
            (K := K) (ρ := Fin (Module.finrank K U₀)) (κ' := κ')
            EMat).1 hE
      exact
        (mem_detChartSet
          (K := K) (ρ := Fin (Module.finrank K U₀)) (κ' := κ')
          (sourceReadback (K := K) (ρ := Fin (Module.finrank K U₀)) EMat)).2
          (sourceReadback_detChart_of_sourceRecursiveDetChart
            (K := K) (ρ := Fin (Module.finrank K U₀)) EMat hchart)
    left_inv' := by
      intro data hdata
      have hdet : data.detChart :=
        (mem_detChartSet
          (K := K) (ρ := Fin (Module.finrank K U₀)) (κ' := κ') data).1 hdata
      simpa [paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData] using
        sourceReadback_paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousReverseEdgeFamilyOf_retainedPassiveEdgeMatrix_eq
          (K := K) W B (U₀ := U₀) (hU₀ := hU₀) data hdet
    right_inv' := by
      intro E hE
      let EMat :=
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
          (fun p : Fin (M + 1) ↦
            (E p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ))
      have hchart :
          sourceRecursiveDetChart (K := K) (ρ := Fin (Module.finrank K U₀)) EMat := by
        exact
          (mem_sourceRecursiveDetChartSet
            (K := K) (ρ := Fin (Module.finrank K U₀)) (κ' := κ')
            EMat).1 hE
      have hreadEdge :
          (sourceReadback (K := K) (ρ := Fin (Module.finrank K U₀)) EMat).edgeMatrix =
            EMat :=
        edgeMatrix_sourceReadback_eq_of_sourceRecursiveDetChart
          (K := K) (ρ := Fin (Module.finrank K U₀)) EMat hchart
      simpa [paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData, EMat, hreadEdge] using
        paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices_edgeMatrixOfReverseEdges
          (K := K) W B U₀ hU₀ E
    open_source :=
      isOpen_detChartSet
        (K := K) (ρ := Fin (Module.finrank K U₀)) (κ' := κ')
    open_target :=
      isOpen_paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := K) W B U₀ hU₀
    continuousOn_toFun := by
      have hdet :
          (fun data :
            RetainedPassiveNonredundantCoordinateData
              (K := K) (ρ := Fin (Module.finrank K U₀)) κ' ↦
              data ∈ S) =
            fun data ↦ data.detChart := by
        funext data
        exact propext
          (mem_detChartSet
            (K := K) (ρ := Fin (Module.finrank K U₀)) (κ' := κ') data)
      rw [continuousOn_iff_continuous_restrict]
      simpa [S, Set.restrict,
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData,
        paperEndpointFixedBaseRetainedPassiveP13SourceChart] using
        (continuous_paperEndpointFixedBaseRetainedPassiveP13SourceChart
          (K := K) W B U₀ hU₀).comp
          (Homeomorph.ofEqSubtypes hdet).continuous
    continuousOn_invFun := by
      intro E hE
      let EMat :=
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
          (fun p : Fin (M + 1) ↦
            (E p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ))
      have hchart :
          sourceRecursiveDetChart (K := K) (ρ := Fin (Module.finrank K U₀)) EMat := by
        exact
          (mem_sourceRecursiveDetChartSet
            (K := K) (ρ := Fin (Module.finrank K U₀)) (κ' := κ')
            EMat).1 hE
      exact
        (continuousAt_sourceReadback
          (K := K) (ρ := Fin (Module.finrank K U₀)) (κ' := κ')
          (E := fun E' : ∀ p : Fin (M + 1),
              reverseVertex W p.castSucc →L[K] reverseVertex W p.succ ↦
            paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
              (fun p : Fin (M + 1) ↦
                (E' p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)))
          (x₀ := E)
          (paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuous
            (K := K) W B U₀ hU₀).continuousAt
          hchart).continuousWithinAt }

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

set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Near the self-base point, retained-passive local-source membership gives
an explicit retained-passive source-chart preimage.

This is retained-passive determinant-chart image coverage only.  It exposes a
coordinate datum whose fixed-base retained-passive source chart is `Cedge x`
for points in the local source neighborhood.  It does not prove Case 2
passive-theta or selected-entry coverage, source-image equality with a
source-rank stratum, source-prior transport, a Jacobian theorem, normal
crossings, pole order, or RLCT extraction. -/
theorem exists_open_paperEndpointFixedBaseRetainedPassiveP13SourceChart_image_coverage_of_selfBase
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
      (∀ x ∈ Ulocal,
        ∃ data :
          {data :
            RetainedPassiveNonredundantCoordinateData
              (K := K) (ρ := Fin (Module.finrank K U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀) // data.detChart},
          paperEndpointFixedBaseRetainedPassiveP13SourceChart W B U₀ hU₀ data =
            Cedge x) ∧
      Ulocal ∩ paperEndpointFixedBaseSourceRankStratum
          (K := K) W B Cedge r rEdge ⊆
        {x |
          ∃ data :
            {data :
              RetainedPassiveNonredundantCoordinateData
                (K := K) (ρ := Fin (Module.finrank K U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀) // data.detChart},
            paperEndpointFixedBaseRetainedPassiveP13SourceChart W B U₀ hU₀ data =
              Cedge x} := by
  rcases
      exists_open_paperEndpointFixedBaseRetainedPassiveP13LocalSource_coverage_of_selfBase
        (K := K) W B U₀ hU₀ Cedge r rEdge hCedge hbase with
    ⟨Ulocal, hUopen, hx₀U, hUsub, _hcoverage⟩
  have himage : ∀ x ∈ Ulocal,
      ∃ data :
        {data :
          RetainedPassiveNonredundantCoordinateData
            (K := K) (ρ := Fin (Module.finrank K U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀) // data.detChart},
        paperEndpointFixedBaseRetainedPassiveP13SourceChart W B U₀ hU₀ data =
          Cedge x := by
    intro x hxU
    have hsource :
        Cedge x ∈
          paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet W B U₀ hU₀ := by
      have hxlocal := hUsub hxU
      simpa [paperEndpointFixedBaseRetainedPassiveP13LocalSource,
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet] using hxlocal
    let Esub :
        {E : ∀ p : Fin (M + 1),
            reverseVertex W p.castSucc →L[K] reverseVertex W p.succ //
          E ∈ paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet W B U₀ hU₀} :=
      ⟨Cedge x, hsource⟩
    let H :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamily_homeomorph
        (K := K) W B U₀ hU₀
    let data := H.symm Esub
    refine ⟨data, ?_⟩
    have hright : H data = Esub := by
      simp [data]
    simpa [H, Esub, data, paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamily_homeomorph]
      using congrArg Subtype.val hright
  refine ⟨Ulocal, hUopen, hx₀U, hUsub, himage, ?_⟩
  intro x hx
  exact himage x hx.1

end RetainedPassiveLocalSource

end Aoyagi
end DLN
end DLNFibre
