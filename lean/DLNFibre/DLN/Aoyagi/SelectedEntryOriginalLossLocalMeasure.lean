import DLNFibre.DLN.Aoyagi.OriginalLossLocalMeasure
import DLNFibre.DLN.Aoyagi.SelectedEntrySignedBoxLocalMeasure

/-!
# Original-loss local handoff for selected-entry signed boxes

This file plugs the concrete selected-entry signed-box chart into local
original-`lossDLN` finite-integral front ends.  Source/image identifications
with the original p.13 source remain explicit hypotheses when used.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace DLNFibre
namespace DLN
namespace Aoyagi

set_option linter.style.longLine false in
/-- If two source sets agree after intersecting a neighborhood of `x₀`, then
their relative-neighborhood filters at `x₀` agree. -/
theorem nhdsWithin_eq_of_mem_nhds_inter_eq
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U s t : Set α} (hU : U ∈ nhds x₀) (hst : U ∩ s = U ∩ t) :
    nhdsWithin x₀ s = nhdsWithin x₀ t := by
  calc
    nhdsWithin x₀ s = nhdsWithin x₀ (U ∩ s) := by
      exact (nhdsWithin_inter_of_mem (a := x₀) (s := U) (t := s)
        (mem_nhdsWithin_of_mem_nhds hU)).symm
    _ = nhdsWithin x₀ (U ∩ t) := by rw [hst]
    _ = nhdsWithin x₀ t := by
      exact nhdsWithin_inter_of_mem (a := x₀) (s := U) (t := t)
        (mem_nhdsWithin_of_mem_nhds hU)

set_option linter.style.longLine false in
/-- Restricting to a smaller set contained in the equality neighborhood turns
a local source-set equality into equality of restricted measures. -/
theorem restrict_inter_eq_of_subset_inter_eq
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {U Ulocal s t : Set α} (hUsub : U ⊆ Ulocal)
    (hst : Ulocal ∩ s = Ulocal ∩ t) :
    μ.restrict (U ∩ s) = μ.restrict (U ∩ t) := by
  have hset : U ∩ s = U ∩ t := by
    ext x
    constructor
    · intro hx
      have hxlocal : x ∈ Ulocal ∩ s := ⟨hUsub hx.1, hx.2⟩
      have hxlocal' : x ∈ Ulocal ∩ t := by
        rwa [hst] at hxlocal
      exact ⟨hx.1, hxlocal'.2⟩
    · intro hx
      have hxlocal : x ∈ Ulocal ∩ t := ⟨hUsub hx.1, hx.2⟩
      have hxlocal' : x ∈ Ulocal ∩ s := by
        rwa [← hst] at hxlocal
      exact ⟨hx.1, hxlocal'.2⟩
  rw [hset]

namespace PaperEndpointFixedBaseRegularCoordinateSourceData

universe v

set_option linter.style.longLine false in
set_option linter.unusedSectionVars false in
/-- A matrix-level residual-product identity gives the selected-entry
coordinate readout expected by the local original-loss endpoint.

This is only a readout bridge: the residual-product matrix identity, source
coverage, and source-chart construction remain hypotheses for downstream
source work. -/
theorem paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_residualProduct_eq_matrix
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {ι : Type*} [DecidableEq ι]
    {center : Finset ι} (pivot : center)
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    {CedgeBase : (center → ℝ) → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ}
    (residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0) ≃ center)
    (hresidualProduct :
      ∀ y : center → ℝ,
        ChartLocalSuffixState.residualProduct
          (paperEndpointFixedBaseEdgeMatrixOfReverseEdges
            (K := ℝ) (W := V) (B := Bv) U₀ hU₀
            (fun p : Fin (M + 2) ↦
              (CedgeBase (SelectedEntrySignedBox.CenterCoord.chartMap pivot y) p :
                reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ)))
          (Fin.last (M + 2)) 0 (Fin.zero_le (Fin.last (M + 2))) =
        AoyagiResidualBlockCoordinateIndex.matrix
          (fun c ↦
            SelectedEntrySignedBox.CenterCoord.chartMap pivot y
              (residualCoordEquiv c))) :
      ∀ y c,
        paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) (W := V) (B := Bv) U₀ hU₀ CedgeBase
            (SelectedEntrySignedBox.CenterCoord.chartMap pivot y) c =
        SelectedEntrySignedBox.CenterCoord.chartMap pivot y (residualCoordEquiv c) := by
  intro y c
  let E : ∀ p : Fin (M + 2),
      Matrix
        (Fin (Module.finrank ℝ U₀) ⊕
          throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ p.succ)
        (Fin (Module.finrank ℝ U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ p.castSucc) ℝ :=
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges
      (K := ℝ) (W := V) (B := Bv) U₀ hU₀
      (fun p : Fin (M + 2) ↦
        (CedgeBase (SelectedEntrySignedBox.CenterCoord.chartMap pivot y) p :
          reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ))
  have hread :
      paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) (W := V) (B := Bv) U₀ hU₀ CedgeBase
            (SelectedEntrySignedBox.CenterCoord.chartMap pivot y) =
        AoyagiResidualBlockCoordinateIndex.value
          (ChartLocalSuffixState.residualProduct E
            (Fin.last (M + 2)) 0 (Fin.zero_le (Fin.last (M + 2)))) := by
    simpa [E] using
      paperEndpointFixedBaseResidualBlockCoordinateMap_eq_residualProduct
        (K := ℝ) (W := V) (B := Bv) U₀ hU₀ CedgeBase
        (SelectedEntrySignedBox.CenterCoord.chartMap pivot y)
  have hmatrix :
      ChartLocalSuffixState.residualProduct E
          (Fin.last (M + 2)) 0 (Fin.zero_le (Fin.last (M + 2))) =
        AoyagiResidualBlockCoordinateIndex.matrix
          (fun c ↦
            SelectedEntrySignedBox.CenterCoord.chartMap pivot y
              (residualCoordEquiv c)) := by
    simpa [E] using hresidualProduct y
  calc
    paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) (W := V) (B := Bv) U₀ hU₀ CedgeBase
            (SelectedEntrySignedBox.CenterCoord.chartMap pivot y) c =
        AoyagiResidualBlockCoordinateIndex.value
          (ChartLocalSuffixState.residualProduct E
            (Fin.last (M + 2)) 0 (Fin.zero_le (Fin.last (M + 2)))) c := by
      exact congrFun hread c
    _ =
        AoyagiResidualBlockCoordinateIndex.value
          (AoyagiResidualBlockCoordinateIndex.matrix
            (fun c ↦
              SelectedEntrySignedBox.CenterCoord.chartMap pivot y
                (residualCoordEquiv c))) c := by
      rw [hmatrix]
    _ = SelectedEntrySignedBox.CenterCoord.chartMap pivot y
          (residualCoordEquiv c) := by
      simpa using congrFun
        (AoyagiResidualBlockCoordinateIndex.value_matrix
          (fun c ↦
            SelectedEntrySignedBox.CenterCoord.chartMap pivot y
              (residualCoordEquiv c))) c

set_option linter.style.longLine false in
set_option linter.unusedSectionVars false in
/-- A matrix-level residual-product identity gives the scalar selected-entry
residual square-sum expected by the local original-loss endpoint.

This is only a readout composition: the residual-product matrix identity,
source coverage, and source-chart construction remain hypotheses for
downstream source work. -/
theorem aoyagiCoordinateSquareSum_paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_residual_of_residualProduct_eq_matrix
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {ι : Type*} [DecidableEq ι]
    {center : Finset ι} (pivot : center)
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    {CedgeBase : (center → ℝ) → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ}
    (residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0) ≃ center)
    (hresidualProduct :
      ∀ y : center → ℝ,
        ChartLocalSuffixState.residualProduct
          (paperEndpointFixedBaseEdgeMatrixOfReverseEdges
            (K := ℝ) (W := V) (B := Bv) U₀ hU₀
            (fun p : Fin (M + 2) ↦
              (CedgeBase (SelectedEntrySignedBox.CenterCoord.chartMap pivot y) p :
                reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ)))
          (Fin.last (M + 2)) 0 (Fin.zero_le (Fin.last (M + 2))) =
        AoyagiResidualBlockCoordinateIndex.matrix
          (fun c ↦
            SelectedEntrySignedBox.CenterCoord.chartMap pivot y
              (residualCoordEquiv c))) :
      ∀ y : center → ℝ,
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (W := V) (B := Bv) U₀ hU₀ CedgeBase
              (SelectedEntrySignedBox.CenterCoord.chartMap pivot y)) =
        SelectedEntrySignedBox.CenterCoord.residual pivot y := by
  have hreadout :
      ∀ y c,
        paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) (W := V) (B := Bv) U₀ hU₀ CedgeBase
            (SelectedEntrySignedBox.CenterCoord.chartMap pivot y) c =
        SelectedEntrySignedBox.CenterCoord.chartMap pivot y (residualCoordEquiv c) :=
    paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_residualProduct_eq_matrix
      (V := V) (Bv := Bv) (pivot := pivot) U₀ hU₀ residualCoordEquiv hresidualProduct
  exact
    SelectedEntrySignedBox.CenterCoord.aoyagiCoordinateSquareSum_eq_residual_of_coord_readout
      (pivot := pivot)
      (F := fun x : center → ℝ =>
        paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) (W := V) (B := Bv) U₀ hU₀ CedgeBase x)
      residualCoordEquiv hreadout

set_option linter.style.longLine false in
set_option linter.unusedSectionVars false in
/-- Prescribed fixed-base edge matrices give the selected-entry coordinate
readout once their suffix residual product is the selected-entry chart matrix.

This is still a readout bridge: the prescribed matrix family, residual-product
identity, residual-index equivalence, and source coverage remain supplied. -/
theorem paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_prescribedEdgeMatrix_residualProduct_eq_matrix
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {ι : Type*} [DecidableEq ι]
    {center : Finset ι} (pivot : center)
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (Ebase : (center → ℝ) → ∀ p : Fin (M + 2),
      Matrix
        (Fin (Module.finrank ℝ U₀) ⊕
          throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ p.succ)
        (Fin (Module.finrank ℝ U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ p.castSucc) ℝ)
    (residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0) ≃ center)
    (hresidualProduct :
      ∀ y : center → ℝ,
        ChartLocalSuffixState.residualProduct
          (Ebase (SelectedEntrySignedBox.CenterCoord.chartMap pivot y))
          (Fin.last (M + 2)) 0 (Fin.zero_le (Fin.last (M + 2))) =
        AoyagiResidualBlockCoordinateIndex.matrix
          (fun c ↦
            SelectedEntrySignedBox.CenterCoord.chartMap pivot y
              (residualCoordEquiv c))) :
      ∀ y c,
        paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) (W := V) (B := Bv) U₀ hU₀
            (fun x ↦
              paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices
                V Bv U₀ hU₀ (Ebase x))
            (SelectedEntrySignedBox.CenterCoord.chartMap pivot y) c =
        SelectedEntrySignedBox.CenterCoord.chartMap pivot y (residualCoordEquiv c) := by
  refine
    paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_residualProduct_eq_matrix
      (V := V) (Bv := Bv) (pivot := pivot) U₀ hU₀ residualCoordEquiv ?_
  intro y
  have hE :
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) (W := V) (B := Bv) U₀ hU₀
          (fun p : Fin (M + 2) ↦
            (paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices
                V Bv U₀ hU₀
                (Ebase (SelectedEntrySignedBox.CenterCoord.chartMap pivot y)) p :
              reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ)) =
        Ebase (SelectedEntrySignedBox.CenterCoord.chartMap pivot y) := by
    funext p
    exact
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousReverseEdgeFamilyOfMatrices
        (K := ℝ) (W := V) (B := Bv) U₀ hU₀
        (Ebase (SelectedEntrySignedBox.CenterCoord.chartMap pivot y)) p
  rw [hE]
  exact hresidualProduct y

set_option linter.style.longLine false in
set_option linter.unusedSectionVars false in
/-- One-edge p.13 product-coordinate edge family whose supplied residual
matrix is the finite selected-entry chart coordinate matrix.

This is only a finite selected-entry specialization of the one-edge
source-dependent residual-matrix family. -/
def paperEndpointFixedBaseSingleEdgeSelectedEntryProductCoordinateEdgeFamilyEuclidean
    (V : Fin 2 → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin 1, V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {ι : Type*} [DecidableEq ι]
    {center : Finset ι} (pivot : center)
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0) ≃ center) :
    (center → ℝ) × EuclideanSpace ℝ
      (AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)) →
      ∀ p : Fin 1, reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ :=
  paperEndpointFixedBaseSingleEdgeProductCoordinateEdgeFamilyOfResidualMatrixEuclidean
    V Bv U₀ hU₀
    (fun y : center → ℝ =>
      AoyagiResidualBlockCoordinateIndex.matrix
        (fun c ↦
          SelectedEntrySignedBox.CenterCoord.chartMap pivot y
            (residualCoordEquiv c)))

set_option linter.style.longLine false in
set_option linter.unusedSectionVars false in
/-- The one-edge selected-entry product-coordinate family reads out the
selected-entry chart coordinates on the residual block. -/
theorem paperEndpointFixedBaseRegular_residualBlockCoordinateMap_eq_singleEdgeSelectedEntryProductCoordinateEuclidean
    (V : Fin 2 → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin 1, V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {ι : Type*} [DecidableEq ι]
    {center : Finset ι} (pivot : center)
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0) ≃ center)
    (y : center → ℝ)
    (u : EuclideanSpace ℝ
      (AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)))
    (hCtop :
      IsUnit
        (AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c ↦ u c)).det) :
    let CedgeProd :=
      paperEndpointFixedBaseSingleEdgeSelectedEntryProductCoordinateEdgeFamilyEuclidean
        V Bv pivot U₀ hU₀ residualCoordEquiv
    (paperEndpointFixedBaseRegularBlockCoordinateMap
        (K := ℝ) (N := 1) V Bv U₀ hU₀ CedgeProd (y, u) = fun c ↦ u c) ∧
      (∀ c,
        paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 1) V Bv U₀ hU₀ CedgeProd (y, u) c =
          SelectedEntrySignedBox.CenterCoord.chartMap pivot y
            (residualCoordEquiv c)) := by
  intro CedgeProd
  let Dbase : (center → ℝ) → Matrix
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ 0) ℝ :=
    fun y ↦
      AoyagiResidualBlockCoordinateIndex.matrix
        (fun c ↦
          SelectedEntrySignedBox.CenterCoord.chartMap pivot y
            (residualCoordEquiv c))
  have hfull :=
    paperEndpointFixedBaseRegular_residualBlockCoordinateMap_eq_singleEdgeProductCoordinateEuclidean_residualMatrix
      (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
      (Dbase := Dbase) (x := y) (u := u) hCtop
  constructor
  · simpa [CedgeProd, Dbase,
      paperEndpointFixedBaseSingleEdgeSelectedEntryProductCoordinateEdgeFamilyEuclidean] using
      hfull.1
  · intro c
    have hres :
        paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 1) V Bv U₀ hU₀ CedgeProd (y, u) c =
          AoyagiResidualBlockCoordinateIndex.value (Dbase y) c := by
      simpa [CedgeProd, Dbase,
        paperEndpointFixedBaseSingleEdgeSelectedEntryProductCoordinateEdgeFamilyEuclidean] using
        congrFun hfull.2 c
    have hmatrix :
        AoyagiResidualBlockCoordinateIndex.value (Dbase y) c =
          SelectedEntrySignedBox.CenterCoord.chartMap pivot y
            (residualCoordEquiv c) := by
      simpa [Dbase] using congrFun
        (AoyagiResidualBlockCoordinateIndex.value_matrix
          (fun c ↦
            SelectedEntrySignedBox.CenterCoord.chartMap pivot y
              (residualCoordEquiv c))) c
    exact hres.trans hmatrix

set_option linter.style.longLine false in
set_option linter.unusedSectionVars false in
/-- The one-edge selected-entry product-coordinate family has scalar residual
square-sum equal to the center-indexed selected-entry residual. -/
theorem aoyagiCoordinateSquareSum_paperEndpointFixedBaseResidualBlockCoordinateMap_eq_singleEdgeSelectedEntryProductCoordinateEuclidean
    (V : Fin 2 → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin 1, V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {ι : Type*} [DecidableEq ι]
    {center : Finset ι} (pivot : center)
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0) ≃ center)
    (y : center → ℝ)
    (u : EuclideanSpace ℝ
      (AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)))
    (hCtop :
      IsUnit
        (AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c ↦ u c)).det) :
    let CedgeProd :=
      paperEndpointFixedBaseSingleEdgeSelectedEntryProductCoordinateEdgeFamilyEuclidean
        V Bv pivot U₀ hU₀ residualCoordEquiv
    aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) (N := 1) V Bv U₀ hU₀ CedgeProd (y, u)) =
      SelectedEntrySignedBox.CenterCoord.residual pivot y := by
  intro CedgeProd
  have hfull :=
    paperEndpointFixedBaseRegular_residualBlockCoordinateMap_eq_singleEdgeSelectedEntryProductCoordinateEuclidean
      (V := V) (Bv := Bv) (pivot := pivot) (U₀ := U₀) (hU₀ := hU₀)
      (residualCoordEquiv := residualCoordEquiv) (y := y) (u := u) hCtop
  have hread :
      ∀ c,
        paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 1) V Bv U₀ hU₀ CedgeProd (y, u) c =
          SelectedEntrySignedBox.CenterCoord.chartMap pivot y
            (residualCoordEquiv c) := by
    simpa [CedgeProd] using hfull.2
  have hpoint :
      paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) (N := 1) V Bv U₀ hU₀ CedgeProd (y, u) =
        fun c ↦ SelectedEntrySignedBox.CenterCoord.chartMap pivot y
          (residualCoordEquiv c) := by
    funext c
    exact hread c
  calc
    aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) (N := 1) V Bv U₀ hU₀ CedgeProd (y, u)) =
        aoyagiCoordinateSquareSum
          (fun c ↦ SelectedEntrySignedBox.CenterCoord.chartMap pivot y
            (residualCoordEquiv c)) := by
      rw [hpoint]
    _ = aoyagiCoordinateSquareSum
        (SelectedEntrySignedBox.CenterCoord.chartMap pivot y) :=
      aoyagiCoordinateSquareSum_comp_equiv residualCoordEquiv
        (SelectedEntrySignedBox.CenterCoord.chartMap pivot y)
    _ = SelectedEntrySignedBox.CenterCoord.residual pivot y :=
      (SelectedEntrySignedBox.CenterCoord.residual_eq_aoyagiCoordinateSquareSum_chartMap
        pivot y).symm

set_option linter.style.longLine false in
set_option linter.unusedSectionVars false in
/-- The one-edge selected-entry product-coordinate edge family is continuous
in the selected-entry chart parameter and the regular coordinates. -/
theorem continuousAt_paperEndpointFixedBaseSingleEdgeSelectedEntryProductCoordinateEdgeFamilyEuclidean
    (V : Fin 2 → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin 1, V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {ι : Type*} [DecidableEq ι]
    {center : Finset ι} (pivot : center)
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0) ≃ center)
    (y₀ : center → ℝ)
    (u₀ : EuclideanSpace ℝ
      (AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0))) :
    ContinuousAt
      (paperEndpointFixedBaseSingleEdgeSelectedEntryProductCoordinateEdgeFamilyEuclidean
        V Bv pivot U₀ hU₀ residualCoordEquiv) (y₀, u₀) := by
  let Dbase : (center → ℝ) → Matrix
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ 0) ℝ :=
    fun y ↦
      AoyagiResidualBlockCoordinateIndex.matrix
        (fun c ↦
          SelectedEntrySignedBox.CenterCoord.chartMap pivot y
            (residualCoordEquiv c))
  have hDbase : Continuous Dbase := by
    refine continuous_matrix ?_
    intro i j
    simpa [Dbase] using
      (continuous_apply (residualCoordEquiv (i, j))).comp
        (SelectedEntrySignedBox.CenterCoord.continuous_chartMap pivot)
  simpa [Dbase,
    paperEndpointFixedBaseSingleEdgeSelectedEntryProductCoordinateEdgeFamilyEuclidean] using
    continuousAt_paperEndpointFixedBaseSingleEdgeProductCoordinateEdgeFamilyOfResidualMatrixEuclidean
      (V := V) (Bv := Bv) (x₀ := y₀) U₀ hU₀ u₀ Dbase hDbase

set_option linter.style.longLine false in
set_option linter.unusedSectionVars false in
/-- Selected-entry finite chart-image handoff for the original square-Frobenius
`lossDLN`.

The finite selected-entry chart supplies the weighted pushforward and
monomial-unit residual integrability input.  The source remains the finite
chart image, not an original p.13 source stratum.  The adapted-product
lower-bound hypothesis is still explicit. -/
theorem exists_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_chartMap_selectedEntryCenter_signedBox_withDensity_edgeMatrix_adaptedProductDifferenceSquareSum_lower
    {N : ℕ}
    (W : Fin (N + 1) → Type v) [∀ i, AddCommGroup (W i)]
    [∀ i, TopologicalSpace (W i)] [∀ i, IsTopologicalAddGroup (W i)]
    [∀ i, T2Space (W i)] [∀ i, Module ℝ (W i)]
    [∀ i, ContinuousSMul ℝ (W i)]
    (B : ∀ i : Fin N, W i.succ →ₗ[ℝ] W i.castSucc)
    [∀ j, FiniteDimensional ℝ (W j)]
    {ι : Type*} [DecidableEq ι]
    {center : Finset ι} (pivot : center) {x₀ : center → ℝ}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {CedgeBase : (center → ℝ) → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ CedgeBase H r rEdge)
    {d : Fin (N + 1) → ℕ}
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (reverseVertex W j))
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {CedgeProd :
      (center → ℝ) × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ∀ p : Fin N,
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {density :
      (center → ℝ) × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t Rreg creg Creg : ℝ} {Rres : center → ℝ}
    (hRreg : 0 < Rreg) (hcreg : 0 < creg) (hCreg : 0 ≤ Creg) (ht : 0 < t)
    (hEdgeMatrix :
      Measurable (fun x : center → ℝ ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) W B U₀ hU₀
          (fun p : Fin N ↦
            (CedgeBase x p : reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ))))
    (hRres : ∀ i, 0 < Rres i)
    (hcrit_pivot :
      2 * t < ((center.erase pivot.1).card : ℝ) + 1)
    (hresidual_eq :
      ∀ y : center → ℝ,
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ CedgeBase
              (SelectedEntrySignedBox.CenterCoord.chartMap pivot y)) =
        SelectedEntrySignedBox.CenterCoord.residual pivot y)
    (hadapted_lower :
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
                  (K := ℝ) W B U₀ hU₀ CedgeBase x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u))
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
    let ρ :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ 0)
    let target :=
      LinearMap.toMatrix (b 0) (b (Fin.last N))
        (chainMap (reverseVertex W) (reverseEdge W B)
          0 (Fin.last N) (Fin.zero_le (Fin.last N)))
    ∃ U : Set (center → ℝ), IsOpen U ∧ x₀ ∈ U ∧
      (∫⁻ z : (center → ℝ) × EuclideanSpace ℝ ρ,
        ENNReal.ofReal
          ((Metric.ball (0 : EuclideanSpace ℝ ρ) Rreg).indicator
            (fun u =>
              (lossDLN d target
                (chainMapMatrixTuple b
                  (fun p : Fin N =>
                    (CedgeProd (z.1, u) p :
                      reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)))) ^
                (-(t + (aoyagiTheorem2RegularVariableCount N H r : ℝ) / 2)) *
                density (z.1, u)) z.2) ∂
          ((volume : Measure (center → ℝ)).restrict
            (U ∩
              (SelectedEntrySignedBox.CenterCoord.chartMap pivot ''
                SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres))).prod ν) < ∞ := by
  classical
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  let target : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ :=
    LinearMap.toMatrix (b 0) (b (Fin.last N))
      (chainMap (reverseVertex W) (reverseEdge W B)
        0 (Fin.last N) (Fin.zero_le (Fin.last N)))
  let originalLoss : (center → ℝ) × EuclideanSpace ℝ ρ → ℝ :=
    fun z =>
      lossDLN d target
        (chainMapMatrixTuple b
          (fun p : Fin N =>
            (CedgeProd z p :
              reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)))
  rcases
      exists_pos_const_forall_adaptedProductDifferenceFrobeniusLoss_le_lossDLN_chainMapMatrixTuple
        (W := W) (B := B) b U₀ hU₀ CedgeProd with
    ⟨c0, hc0, hcmp⟩
  have hloss :
      ∀ᶠ x in nhdsWithin x₀
          (SelectedEntrySignedBox.CenterCoord.chartMap pivot ''
            SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres),
        ∀ u : EuclideanSpace ℝ ρ,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ ρ) Rreg →
            (c0 * creg) * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ CedgeBase x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ originalLoss (x, u) := by
    filter_upwards [hadapted_lower] with x hx
    intro u hu
    have hsq :
        c0 * paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
            (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) ≤ originalLoss (x, u) := by
      have hcmp' := hcmp (x, u)
      rw [paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss_eq_squareSum
        (W := W) (B := B) U₀ hU₀ CedgeProd (x, u)] at hcmp'
      simpa [originalLoss, target] using hcmp'
    calc
      (c0 * creg) *
          (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ CedgeBase x) +
            aoyagiCoordinateSquareSum (fun i => u i))
          = c0 * (creg *
              (aoyagiCoordinateSquareSum
                  (paperEndpointFixedBaseResidualBlockCoordinateMap
                    (K := ℝ) W B U₀ hU₀ CedgeBase x) +
                aoyagiCoordinateSquareSum (fun i => u i))) := by ring
      _ ≤ c0 * paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
            (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) :=
          mul_le_mul_of_nonneg_left (hx u hu) (le_of_lt hc0)
      _ ≤ originalLoss (x, u) := hsq
  simpa [ρ, target, originalLoss] using
    exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_chartMap_selectedEntryCenter_signedBox_withDensity_edgeMatrix
      (W := W) (B := B) (pivot := pivot) sourceData
      (ν := ν) (loss := originalLoss) (density := density)
      (t := t) (Rreg := Rreg) (creg := c0 * creg) (Creg := Creg)
      (Rres := Rres)
      hRreg (mul_pos hc0 hcreg) hCreg ht hEdgeMatrix hRres
      hcrit_pivot hresidual_eq
      (by simpa [ρ] using hloss)
      (by simpa [ρ] using hdensity_nonneg)
      (by simpa [ρ] using hdensity_le)

set_option linter.style.longLine false in
set_option linter.unusedSectionVars false in
/-- Locally boundary-explicit selected-entry signed-box handoff for the
original square-Frobenius `lossDLN`.

This is the neighborhood-local version of the global
`sourceStratum = chartMap '' signedBoxSet` handoff below.  It assumes only that
the source-rank stratum and finite selected-entry chart image agree after
intersecting a specified open neighborhood of `x₀`; the proof shrinks the final
open integration set into that neighborhood before rewriting the restricted
measure.  It still does not prove Aoyagi's p.13 source chart coverage. -/
theorem exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_locally_eq_chartMap_selectedEntryCenter_signedBox_withDensity_edgeMatrix_multiEdgeProductCoordinateEdgeFamily_selfBase
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {ι : Type*} [DecidableEq ι]
    {center : Finset ι} (pivot : center) {x₀ : center → ℝ}
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    {CedgeBase : (center → ℝ) → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin (M + 2) → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) (N := M + 2) V Bv U₀ hU₀ x₀ CedgeBase H r rEdge)
    {d : Fin (M + 3) → ℕ}
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (reverseVertex V j))
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {density :
      (center → ℝ) × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0)) → ℝ}
    {t Rmax : ℝ} {Rres : center → ℝ}
    (hRmax : 0 < Rmax) (ht : 0 < t)
    (hCedgeBase : ContinuousAt CedgeBase x₀)
    (hbase :
      CedgeBase x₀ =
        fun p : Fin (M + 2) ↦ LinearMap.toContinuousLinearMap (reverseEdge V Bv p))
    (hEdgeMatrix :
      Measurable (fun x : center → ℝ ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) (N := M + 2) V Bv U₀ hU₀
          (fun p : Fin (M + 2) ↦
            (CedgeBase x p :
              reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ))))
    (Ulocal : Set (center → ℝ))
    (hUlocal_open : IsOpen Ulocal)
    (hx₀Ulocal : x₀ ∈ Ulocal)
    (hsourceStratum_local_eq :
      Ulocal ∩ paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge =
        Ulocal ∩
          (SelectedEntrySignedBox.CenterCoord.chartMap pivot ''
            SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres))
    (hRres : ∀ i, 0 < Rres i)
    (hcrit_pivot :
      2 * t < ((center.erase pivot.1).card : ℝ) + 1)
    (hresidual_eq :
      ∀ y : center → ℝ,
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeBase
              (SelectedEntrySignedBox.CenterCoord.chartMap pivot y)) =
        SelectedEntrySignedBox.CenterCoord.residual pivot y)
    (hdensity_cont : ContinuousAt density (x₀, 0))
    (hdensity_pos : 0 < density (x₀, 0)) :
    let ρ :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge
    let CedgeProd :=
      paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
        V Bv U₀ hU₀ CedgeBase
    let target :=
      LinearMap.toMatrix (b 0) (b (Fin.last (M + 2)))
        (chainMap (reverseVertex V) (reverseEdge V Bv)
          0 (Fin.last (M + 2)) (Fin.zero_le (Fin.last (M + 2))))
    ∃ R C : ℝ, ∃ U : Set (center → ℝ),
      0 < R ∧ R ≤ Rmax ∧ 0 ≤ C ∧ IsOpen U ∧ x₀ ∈ U ∧
        (∫⁻ z : (center → ℝ) × EuclideanSpace ℝ ρ,
          ENNReal.ofReal
            ((Metric.ball (0 : EuclideanSpace ℝ ρ) R).indicator
              (fun u =>
                (lossDLN d target
                  (chainMapMatrixTuple b
                    (fun p : Fin (M + 2) =>
                      (CedgeProd (z.1, u) p :
                        reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ)))) ^
                    (-(t + (aoyagiTheorem2RegularVariableCount (M + 2) H r : ℝ) / 2)) *
                  density (z.1, u)) z.2) ∂
            ((volume : Measure (center → ℝ)).restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
  classical
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ 0)
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge
  let chartImage :=
    SelectedEntrySignedBox.CenterCoord.chartMap pivot ''
      SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres
  let CedgeProd :=
    paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
      V Bv U₀ hU₀ CedgeBase
  let target : Matrix (Fin (d (Fin.last (M + 2)))) (Fin (d 0)) ℝ :=
    LinearMap.toMatrix (b 0) (b (Fin.last (M + 2)))
      (chainMap (reverseVertex V) (reverseEdge V Bv)
        0 (Fin.last (M + 2)) (Fin.zero_le (Fin.last (M + 2))))
  have hfilter_source_chart :
      nhdsWithin x₀ sourceStratum = nhdsWithin x₀ chartImage := by
    exact
      nhdsWithin_eq_of_mem_nhds_inter_eq
        (x₀ := x₀) (U := Ulocal) (s := sourceStratum) (t := chartImage)
        (hUlocal_open.mem_nhds hx₀Ulocal)
        (by simpa [sourceStratum, chartImage] using hsourceStratum_local_eq)
  rcases
      exists_measurable_localSource_pos_radius_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase
        (V := V) (Bv := Bv) (x₀ := x₀) U₀ hU₀ sourceData
        hCedgeBase hbase hEdgeMatrix hRmax with
    ⟨source, _sourceU, Rprod, cprod, _hsourceU_nhds, _hsourceU_open, _hxsourceU,
      _hsource_eq, _hsource_meas, _hxsource, _hsource_subset, _hsourceRanks,
      hnhds_source, hRprod, hRprod_le_Rmax, hcprod, hadapted_lower⟩
  have hadapted_sourceStratum :
      ∀ᶠ x in nhdsWithin x₀ sourceStratum,
        ∀ u : EuclideanSpace ℝ ρ,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ ρ) Rprod →
            cprod * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeBase x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeProd (x, u) := by
    rw [← hnhds_source]
    simpa [ρ, sourceStratum, CedgeProd] using hadapted_lower
  have hadapted_chart_Rprod :
      ∀ᶠ x in nhdsWithin x₀ chartImage,
        ∀ u : EuclideanSpace ℝ ρ,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ ρ) Rprod →
            cprod * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeBase x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeProd (x, u) := by
    rw [← hfilter_source_chart]
    simpa [ρ, sourceStratum, chartImage, CedgeProd] using hadapted_sourceStratum
  rcases
      exists_pos_radius_le_eventually_nhdsWithin_density_bounds_of_continuousAt_pos
        (density := density) (x₀ := x₀) (s := chartImage) (Rmax := Rprod)
        hdensity_cont hdensity_pos hRprod with
    ⟨R, C, hR, hR_le_Rprod, hC, hdensity_nonneg_chart, hdensity_le_chart⟩
  have hadapted_chart :
      ∀ᶠ x in nhdsWithin x₀ chartImage,
        ∀ u : EuclideanSpace ℝ ρ,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ ρ) R →
            cprod * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeBase x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeProd (x, u) := by
    filter_upwards [hadapted_chart_Rprod] with x hx
    intro u hu
    exact hx u (Metric.ball_subset_ball hR_le_Rprod hu)
  rcases
      exists_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_chartMap_selectedEntryCenter_signedBox_withDensity_edgeMatrix_adaptedProductDifferenceSquareSum_lower
        (W := V) (B := Bv) (pivot := pivot) sourceData b
        (ν := ν) (CedgeProd := CedgeProd) (density := density)
        (t := t) (Rreg := R) (creg := cprod) (Creg := C) (Rres := Rres)
        hR hcprod hC ht hEdgeMatrix hRres hcrit_pivot hresidual_eq
        (by simpa [ρ, chartImage, CedgeProd] using hadapted_chart)
        (by simpa [ρ, chartImage] using hdensity_nonneg_chart)
        (by simpa [ρ, chartImage] using hdensity_le_chart) with
    ⟨Uchart, hUchart_open, hx₀Uchart, hfinite_chart⟩
  let U := Uchart ∩ Ulocal
  have hU_open : IsOpen U := hUchart_open.inter hUlocal_open
  have hx₀U : x₀ ∈ U := ⟨hx₀Uchart, hx₀Ulocal⟩
  have hU_subset_Ulocal : U ⊆ Ulocal := fun _ hx => hx.2
  have hrestrict_eq :
      ((volume : Measure (center → ℝ)).restrict (U ∩ sourceStratum)).prod ν =
        ((volume : Measure (center → ℝ)).restrict (U ∩ chartImage)).prod ν := by
    rw [restrict_inter_eq_of_subset_inter_eq
      (μ := (volume : Measure (center → ℝ))) (U := U) (Ulocal := Ulocal)
      (s := sourceStratum) (t := chartImage) hU_subset_Ulocal
      (by simpa [sourceStratum, chartImage] using hsourceStratum_local_eq)]
  have hsubset_chart : U ∩ chartImage ⊆ Uchart ∩ chartImage := by
    intro x hx
    exact ⟨hx.1.1, hx.2⟩
  have hmeasure_le :
      ((volume : Measure (center → ℝ)).restrict (U ∩ chartImage)).prod ν ≤
        ((volume : Measure (center → ℝ)).restrict (Uchart ∩ chartImage)).prod ν := by
    rw [Measure.restrict_prod_eq_prod_univ, Measure.restrict_prod_eq_prod_univ]
    exact Measure.restrict_mono (Set.prod_mono_left hsubset_chart) le_rfl
  let integrand :
      (center → ℝ) × EuclideanSpace ℝ ρ → ℝ≥0∞ :=
    fun z =>
      ENNReal.ofReal
        ((Metric.ball (0 : EuclideanSpace ℝ ρ) R).indicator
          (fun u =>
            (lossDLN d target
              (chainMapMatrixTuple b
                (fun p : Fin (M + 2) =>
                  (CedgeProd (z.1, u) p :
                    reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ)))) ^
              (-(t + (aoyagiTheorem2RegularVariableCount (M + 2) H r : ℝ) / 2)) *
              density (z.1, u)) z.2)
  have hfinite_chart_small :
      (∫⁻ z : (center → ℝ) × EuclideanSpace ℝ ρ, integrand z ∂
          ((volume : Measure (center → ℝ)).restrict (U ∩ chartImage)).prod ν) < ∞ := by
    have hmono :
        (∫⁻ z : (center → ℝ) × EuclideanSpace ℝ ρ, integrand z ∂
            ((volume : Measure (center → ℝ)).restrict (U ∩ chartImage)).prod ν) ≤
          (∫⁻ z : (center → ℝ) × EuclideanSpace ℝ ρ, integrand z ∂
            ((volume : Measure (center → ℝ)).restrict (Uchart ∩ chartImage)).prod ν) := by
      exact lintegral_mono' hmeasure_le (le_refl integrand)
    exact hmono.trans_lt
      (by simpa [integrand, ρ, chartImage, CedgeProd, target] using hfinite_chart)
  have hfinite_source :
      (∫⁻ z : (center → ℝ) × EuclideanSpace ℝ ρ, integrand z ∂
          ((volume : Measure (center → ℝ)).restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
    rwa [hrestrict_eq]
  exact
    ⟨R, C, U, hR, hR_le_Rprod.trans hRprod_le_Rmax, hC, hU_open, hx₀U,
      by simpa [integrand, ρ, sourceStratum, CedgeProd, target] using hfinite_source⟩

set_option linter.style.longLine false in
/-- Locally boundary-explicit selected-entry original-loss handoff with the
residual square-sum hypothesis replaced by an explicit finite coordinate
readout.

This is still conditional on the local source/image equality.  The new readout
hypotheses only identify the fixed-base residual coordinates with the
selected-entry center coordinates up to a finite reindexing. -/
theorem exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_locally_eq_chartMap_selectedEntryCenter_signedBox_withDensity_edgeMatrix_multiEdgeProductCoordinateEdgeFamily_selfBase_of_residualBlockCoordinateReadout
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {ι : Type*} [DecidableEq ι]
    {center : Finset ι} (pivot : center) {x₀ : center → ℝ}
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    {CedgeBase : (center → ℝ) → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin (M + 2) → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) (N := M + 2) V Bv U₀ hU₀ x₀ CedgeBase H r rEdge)
    {d : Fin (M + 3) → ℕ}
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (reverseVertex V j))
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {density :
      (center → ℝ) × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0)) → ℝ}
    {t Rmax : ℝ} {Rres : center → ℝ}
    (hRmax : 0 < Rmax) (ht : 0 < t)
    (hCedgeBase : ContinuousAt CedgeBase x₀)
    (hbase :
      CedgeBase x₀ =
        fun p : Fin (M + 2) ↦ LinearMap.toContinuousLinearMap (reverseEdge V Bv p))
    (hEdgeMatrix :
      Measurable (fun x : center → ℝ ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) (N := M + 2) V Bv U₀ hU₀
          (fun p : Fin (M + 2) ↦
            (CedgeBase x p :
              reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ))))
    (Ulocal : Set (center → ℝ))
    (hUlocal_open : IsOpen Ulocal)
    (hx₀Ulocal : x₀ ∈ Ulocal)
    (hsourceStratum_local_eq :
      Ulocal ∩ paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge =
        Ulocal ∩
          (SelectedEntrySignedBox.CenterCoord.chartMap pivot ''
            SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres))
    (hRres : ∀ i, 0 < Rres i)
    (hcrit_pivot :
      2 * t < ((center.erase pivot.1).card : ℝ) + 1)
    (residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0) ≃ center)
    (hresidual_readout :
      ∀ y c,
        paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeBase
            (SelectedEntrySignedBox.CenterCoord.chartMap pivot y) c =
        SelectedEntrySignedBox.CenterCoord.chartMap pivot y (residualCoordEquiv c))
    (hdensity_cont : ContinuousAt density (x₀, 0))
    (hdensity_pos : 0 < density (x₀, 0)) :
    let ρ :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge
    let CedgeProd :=
      paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
        V Bv U₀ hU₀ CedgeBase
    let target :=
      LinearMap.toMatrix (b 0) (b (Fin.last (M + 2)))
        (chainMap (reverseVertex V) (reverseEdge V Bv)
          0 (Fin.last (M + 2)) (Fin.zero_le (Fin.last (M + 2))))
    ∃ R C : ℝ, ∃ U : Set (center → ℝ),
      0 < R ∧ R ≤ Rmax ∧ 0 ≤ C ∧ IsOpen U ∧ x₀ ∈ U ∧
        (∫⁻ z : (center → ℝ) × EuclideanSpace ℝ ρ,
          ENNReal.ofReal
            ((Metric.ball (0 : EuclideanSpace ℝ ρ) R).indicator
              (fun u =>
                (lossDLN d target
                  (chainMapMatrixTuple b
                    (fun p : Fin (M + 2) =>
                      (CedgeProd (z.1, u) p :
                        reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ)))) ^
                    (-(t + (aoyagiTheorem2RegularVariableCount (M + 2) H r : ℝ) / 2)) *
                  density (z.1, u)) z.2) ∂
            ((volume : Measure (center → ℝ)).restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
  classical
  have hresidual_eq :
      ∀ y : center → ℝ,
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeBase
              (SelectedEntrySignedBox.CenterCoord.chartMap pivot y)) =
        SelectedEntrySignedBox.CenterCoord.residual pivot y :=
    SelectedEntrySignedBox.CenterCoord.aoyagiCoordinateSquareSum_eq_residual_of_coord_readout
      (pivot := pivot)
      (F := fun x : center → ℝ =>
        paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeBase x)
      residualCoordEquiv hresidual_readout
  exact
    exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_locally_eq_chartMap_selectedEntryCenter_signedBox_withDensity_edgeMatrix_multiEdgeProductCoordinateEdgeFamily_selfBase
      (V := V) (Bv := Bv) (pivot := pivot) U₀ hU₀ sourceData b
      (ν := ν) (density := density) (t := t) (Rmax := Rmax) (Rres := Rres)
      hRmax ht hCedgeBase hbase hEdgeMatrix Ulocal hUlocal_open hx₀Ulocal
      hsourceStratum_local_eq hRres hcrit_pivot hresidual_eq hdensity_cont
      hdensity_pos

set_option linter.style.longLine false in
set_option linter.unusedSectionVars false in
/-- Boundary-explicit selected-entry signed-box handoff for the original
square-Frobenius `lossDLN`.

The selected-entry chart supplies the weighted pushforward and monomial
source-density/residual estimates.  The statement still assumes that the
source rank stratum is exactly the finite chart image, and assumes the
residual-coordinate identity along the chart. -/
theorem exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_eq_chartMap_selectedEntryCenter_signedBox_withDensity_edgeMatrix_multiEdgeProductCoordinateEdgeFamily_selfBase
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {ι : Type*} [DecidableEq ι]
    {center : Finset ι} (pivot : center) {x₀ : center → ℝ}
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    {CedgeBase : (center → ℝ) → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin (M + 2) → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) (N := M + 2) V Bv U₀ hU₀ x₀ CedgeBase H r rEdge)
    {d : Fin (M + 3) → ℕ}
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (reverseVertex V j))
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {density :
      (center → ℝ) × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0)) → ℝ}
    {t Rmax : ℝ} {Rres : center → ℝ}
    (hRmax : 0 < Rmax) (ht : 0 < t)
    (hCedgeBase : ContinuousAt CedgeBase x₀)
    (hbase :
      CedgeBase x₀ =
        fun p : Fin (M + 2) ↦ LinearMap.toContinuousLinearMap (reverseEdge V Bv p))
    (hEdgeMatrix :
      Measurable (fun x : center → ℝ ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) (N := M + 2) V Bv U₀ hU₀
          (fun p : Fin (M + 2) ↦
            (CedgeBase x p :
              reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ))))
    (hsourceStratum_eq :
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge =
        SelectedEntrySignedBox.CenterCoord.chartMap pivot ''
          SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit_pivot :
      2 * t < ((center.erase pivot.1).card : ℝ) + 1)
    (hresidual_eq :
      ∀ y : center → ℝ,
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeBase
              (SelectedEntrySignedBox.CenterCoord.chartMap pivot y)) =
        SelectedEntrySignedBox.CenterCoord.residual pivot y)
    (hdensity_cont : ContinuousAt density (x₀, 0))
    (hdensity_pos : 0 < density (x₀, 0)) :
    let ρ :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge
    let CedgeProd :=
      paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
        V Bv U₀ hU₀ CedgeBase
    let target :=
      LinearMap.toMatrix (b 0) (b (Fin.last (M + 2)))
        (chainMap (reverseVertex V) (reverseEdge V Bv)
          0 (Fin.last (M + 2)) (Fin.zero_le (Fin.last (M + 2))))
    ∃ R C : ℝ, ∃ U : Set (center → ℝ),
      0 < R ∧ R ≤ Rmax ∧ 0 ≤ C ∧ IsOpen U ∧ x₀ ∈ U ∧
        (∫⁻ z : (center → ℝ) × EuclideanSpace ℝ ρ,
          ENNReal.ofReal
            ((Metric.ball (0 : EuclideanSpace ℝ ρ) R).indicator
              (fun u =>
                (lossDLN d target
                  (chainMapMatrixTuple b
                    (fun p : Fin (M + 2) =>
                      (CedgeProd (z.1, u) p :
                        reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ)))) ^
                    (-(t + (aoyagiTheorem2RegularVariableCount (M + 2) H r : ℝ) / 2)) *
                  density (z.1, u)) z.2) ∂
            ((volume : Measure (center → ℝ)).restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
  classical
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ 0)
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge
  let CedgeProd :=
    paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
      V Bv U₀ hU₀ CedgeBase
  let target : Matrix (Fin (d (Fin.last (M + 2)))) (Fin (d 0)) ℝ :=
    LinearMap.toMatrix (b 0) (b (Fin.last (M + 2)))
      (chainMap (reverseVertex V) (reverseEdge V Bv)
        0 (Fin.last (M + 2)) (Fin.zero_le (Fin.last (M + 2))))
  rcases SelectedEntrySignedBox.CenterCoord.monomialLower_sourceDensityBounds
      pivot Rres with
    ⟨hsourceDensity_aemeas, hres_lower_selected,
      hsourceDensity_nonneg, hsourceDensity_le⟩
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
  have hmap :
      (volume : Measure (center → ℝ)).restrict sourceStratum =
        Measure.map (SelectedEntrySignedBox.CenterCoord.chartMap pivot)
          ((Measure.pi
              (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))).withDensity
            (fun y : center → ℝ =>
              ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivot y))) := by
    simpa [sourceStratum, hsourceStratum_eq] using
      (SelectedEntrySignedBox.CenterCoord.map_chartMap_signedBoxMeasure_withDensity_sourceDensity_eq_restrict_image
        pivot Rres).symm
  have hres_lower :
      ∀ᵐ y : center → ℝ
        ∂Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
        1 * ∏ i, |y i| ^ (2 * (SelectedEntrySignedBox.CenterCoord.lossExp pivot i : ℝ)) ≤
          aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeBase
                (SelectedEntrySignedBox.CenterCoord.chartMap pivot y)) := by
    exact hres_lower_selected.mono fun y hy => by
      rw [hresidual_eq y]
      exact hy
  simpa [ρ, sourceStratum, CedgeProd, target] using
    exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_multiEdgeProductCoordinateEdgeFamily_selfBase_continuousAt_pos_density
      (V := V) (Bv := Bv) (x₀ := x₀) U₀ hU₀ sourceData b
      (μ := (volume : Measure (center → ℝ))) (ν := ν)
      (sourceChart := SelectedEntrySignedBox.CenterCoord.chartMap pivot)
      (sourceDensity := SelectedEntrySignedBox.CenterCoord.sourceDensity pivot)
      (density := density)
      (t := t) (Rmax := Rmax) (cres := 1) (Cres := 1)
      (Rres := Rres)
      (hres := SelectedEntrySignedBox.CenterCoord.densityExp pivot)
      (kres := SelectedEntrySignedBox.CenterCoord.lossExp pivot)
      hRmax ht hCedgeBase hbase hEdgeMatrix
      hsourceDensity_aemeas
      (SelectedEntrySignedBox.CenterCoord.aemeasurable_chartMap pivot Rres)
      (by simpa [sourceStratum] using hmap)
      (by norm_num) (by norm_num) hRres hcrit hres_lower
      hsourceDensity_nonneg hsourceDensity_le hdensity_cont hdensity_pos

end PaperEndpointFixedBaseRegularCoordinateSourceData

end Aoyagi
end DLN
end DLNFibre
