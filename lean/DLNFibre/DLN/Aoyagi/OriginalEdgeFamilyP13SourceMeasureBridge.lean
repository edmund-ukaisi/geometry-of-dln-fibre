import DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyRawOrderMeasureBridge
import DLNFibre.DLN.Aoyagi.RetainedPassiveLocalJacobianMeasure
import DLNFibre.DLN.Aoyagi.LocalMeasureHandoff

/-!
# p.13 source-set measure bridge for original edge-family volume

This file specializes the raw-order-to-edge-family restricted measure bridge
to the public p.13 fixed-base retained-passive source chart and its named
source edge-family set.

The statements keep the same full-space Haar scalar from the tuple-coordinate
comparison.  They do not prove the scalar is `1`, identify a restricted
measure as Haar, prove original source coverage, construct normal crossings,
or extract an RLCT.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DLNFibre
namespace DLN
namespace Aoyagi

open DLNFibre.Core
open ChartLocalSuffixState
open ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData

section P13SourceMeasureBridge

universe v

variable {M : ℕ}
variable (W : Fin (M + 2) → Type v)
variable [∀ i, AddCommGroup (W i)]
variable [∀ i, TopologicalSpace (W i)]
variable [∀ i, IsTopologicalAddGroup (W i)]
variable [∀ i, T2Space (W i)]
variable [∀ i, Module ℝ (W i)]
variable [∀ i, ContinuousSMul ℝ (W i)]
variable [∀ i, FiniteDimensional ℝ (W i)]
variable (B : ∀ i : Fin (M + 1), W i.succ →ₗ[ℝ] W i.castSucc)

set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- On the raw source-recursive determinant chart, the public p.13 raw-order
source chart is the fixed-basis reconstruction of the raw-order matrix tuple.

This is a chart-domain pointwise identity only. -/
theorem paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_eq_tupleToEdgeFamily_rawOrderMatrixTuple
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {y :
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ}
    (hy : y ∈
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀)) :
    paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W B U₀ hU₀ y =
      tupleToEdgeFamily (V := reverseVertex W)
        (paperEndpointFixedBaseFinBasis W B U₀ hU₀)
        (rawOrderMatrixTuple
          (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀)
          (d := paperEndpointFixedBaseDim W B U₀)
          (fun j ↦
            Fintype.equivFin
              (paperEndpointFixedBaseCoordinateIndex W B U₀ j)) y) := by
  let b := paperEndpointFixedBaseFinBasis W B U₀ hU₀
  let e :=
    fun j ↦ Fintype.equivFin (paperEndpointFixedBaseCoordinateIndex W B U₀ j)
  let sourceChart :=
    paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
      (K := ℝ) W B U₀ hU₀
  have hmat :=
    edgeFamilyMatrixTuple_p13FinBasis_rawOrderSourceChart_eq_rawOrderMatrixTuple
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) (y := y) hy
  calc
    sourceChart y =
        tupleToEdgeFamily (V := reverseVertex W) b
          (edgeFamilyMatrixTuple (V := reverseVertex W) b (sourceChart y)) := by
          simp [sourceChart, b]
    _ =
        tupleToEdgeFamily (V := reverseVertex W) b
          (rawOrderMatrixTuple
            (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀)
            (d := paperEndpointFixedBaseDim W B U₀) e y) := by
          rw [hmat]

set_option linter.style.longLine false in
/-- The p.13 raw-order source chart pushes the restricted raw-coordinate Haar
measure to `originalEdgeFamilyVolume` restricted to the named p.13 source
edge-family set, up to the tuple-side full-space Haar scalar.

This is a source-set specialization of the raw-order edge-family bridge.  It
does not assert that a restricted measure is Haar or that the scalar is `1`. -/
theorem map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_restrict_eq_smul_originalEdgeFamilyVolume_restrict_sourceEdgeFamilySet
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [BorelSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ))
    [m.IsAddHaarMeasure] :
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀
    let d := paperEndpointFixedBaseDim W B U₀
    let sourceChart : TopologyTuple ρ κ' ℝ →
        (∀ p : Fin (M + 1),
          reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W B U₀ hU₀
    let sourceSet :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W B U₀ hU₀
    Measure.map sourceChart
        (m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ')))=
      ((Measure.map
          (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
            W B U₀)
          m).addHaarScalarFactor (originalTupleVolume d)) •
        (originalEdgeFamilyVolume (V := reverseVertex W)
          (paperEndpointFixedBaseFinBasis W B U₀ hU₀)).restrict sourceSet := by
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  let d := paperEndpointFixedBaseDim W B U₀
  let e := fun j ↦ Fintype.equivFin
    (paperEndpointFixedBaseCoordinateIndex W B U₀ j)
  let b := paperEndpointFixedBaseFinBasis W B U₀ hU₀
  let T : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleRawOrderSourceRecursiveDetChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ')
  let sourceChart : TopologyTuple ρ κ' ℝ →
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
    paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
      (K := ℝ) W B U₀ hU₀
  let sourceSet : Set
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
    paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
      (K := ℝ) W B U₀ hU₀
  let ψ : TopologyTuple ρ κ' ℝ →
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
    fun y ↦
      tupleToEdgeFamily (V := reverseVertex W) b
        (rawOrderMatrixTuple (ρ := ρ) (κ' := κ') (d := d) e y)
  have hpoint : ∀ y ∈ T, sourceChart y = ψ y := by
    intro y hy
    simpa [sourceChart, ψ, T, ρ, κ', d, e, b] using
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_eq_tupleToEdgeFamily_rawOrderMatrixTuple
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) (y := y) hy
  have hTnull : NullMeasurableSet T m := by
    simpa [T, ρ, κ'] using
      nullMeasurableSet_topologyTupleRawOrderSourceRecursiveDetChartSet
        (ρ := ρ) (κ' := κ') m
  have hmap_eq :
      Measure.map sourceChart (m.restrict T) =
        Measure.map ψ (m.restrict T) := by
    exact Measure.map_congr
      (by
        filter_upwards [ae_restrict_mem₀ hTnull] with y hy
        exact hpoint y hy)
  have himage : ψ '' T = sourceSet := by
    calc
      ψ '' T = sourceChart '' T := by
        ext E
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact ⟨y, hy, hpoint y hy⟩
        · rintro ⟨y, hy, rfl⟩
          exact ⟨y, hy, (hpoint y hy).symm⟩
      _ = sourceSet := by
        simpa [sourceChart, sourceSet, T, ρ, κ'] using
          image_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_eq_sourceEdgeFamilySet
            (K := ℝ) W B U₀ hU₀
  have hgeneric :=
    map_rawOrderMatrixTuple_tupleToEdgeFamily_restrict_eq_smul_originalEdgeFamilyVolume_restrict_image
      (ρ := ρ) (κ' := κ') (d := d) (V := reverseVertex W) m e b T
  calc
    Measure.map sourceChart (m.restrict T) =
        Measure.map ψ (m.restrict T) := hmap_eq
    _ =
      ((Measure.map
          (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
            W B U₀)
          m).addHaarScalarFactor (originalTupleVolume d)) •
        (originalEdgeFamilyVolume (V := reverseVertex W) b).restrict sourceSet := by
          simpa [ψ, T, d, e, b, himage,
            paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv]
            using hgeneric

set_option linter.style.longLine false in
/-- The unweighted p.13 source-set scalar comparison restricts to any
measurable chart piece contained in the named p.13 source edge-family set. -/
theorem map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_restrict_chartPiece_eq_smul_originalEdgeFamilyVolume_restrict_chartPiece
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [BorelSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ))
    [m.IsAddHaarMeasure]
    {chartPiece : Set
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)}
    (hchartPiece : MeasurableSet chartPiece)
    (hchartPiece_sub :
      chartPiece ⊆
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
          (K := ℝ) W B U₀ hU₀) :
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀
    let d := paperEndpointFixedBaseDim W B U₀
    let sourceChart : TopologyTuple ρ κ' ℝ →
        (∀ p : Fin (M + 1),
          reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W B U₀ hU₀
    let c :=
      ((Measure.map
          (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
            W B U₀)
          m).addHaarScalarFactor (originalTupleVolume d))
    (Measure.map sourceChart
        (m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ')))).restrict chartPiece =
      c •
        (originalEdgeFamilyVolume (V := reverseVertex W)
          (paperEndpointFixedBaseFinBasis W B U₀ hU₀)).restrict chartPiece := by
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  let d := paperEndpointFixedBaseDim W B U₀
  let sourceChart : TopologyTuple ρ κ' ℝ →
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
    paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
      (K := ℝ) W B U₀ hU₀
  let sourceSet : Set
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
    paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
      (K := ℝ) W B U₀ hU₀
  let c :=
    ((Measure.map
        (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
          W B U₀)
        m).addHaarScalarFactor (originalTupleVolume d))
  let volume :=
    originalEdgeFamilyVolume (V := reverseVertex W)
      (paperEndpointFixedBaseFinBasis W B U₀ hU₀)
  have _hchartPiece : MeasurableSet chartPiece := hchartPiece
  have hsub : chartPiece ⊆ sourceSet := by
    simpa [sourceSet] using hchartPiece_sub
  have hsourceSet :=
    map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_restrict_eq_smul_originalEdgeFamilyVolume_restrict_sourceEdgeFamilySet
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) m
  calc
    (Measure.map sourceChart
        (m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ')))).restrict chartPiece =
        (c • volume.restrict sourceSet).restrict chartPiece := by
          simpa [sourceChart, sourceSet, c, volume, ρ, κ', d] using
            congrArg (fun μ ↦ μ.restrict chartPiece) hsourceSet
    _ = c • (volume.restrict sourceSet).restrict chartPiece := by
          rw [Measure.restrict_smul]
    _ = c • volume.restrict chartPiece := by
          rw [Measure.restrict_restrict_of_subset hsub]

set_option linter.style.longLine false in
/-- Inverse-scalar form of the unweighted p.13 chart-piece measure comparison. -/
theorem originalEdgeFamilyVolume_restrict_chartPiece_eq_inv_smul_map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_restrict_chartPiece
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [BorelSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ))
    [m.IsAddHaarMeasure]
    {chartPiece : Set
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)}
    (hchartPiece : MeasurableSet chartPiece)
    (hchartPiece_sub :
      chartPiece ⊆
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
          (K := ℝ) W B U₀ hU₀) :
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀
    let d := paperEndpointFixedBaseDim W B U₀
    let sourceChart : TopologyTuple ρ κ' ℝ →
        (∀ p : Fin (M + 1),
          reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W B U₀ hU₀
    let c :=
      ((Measure.map
          (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
            W B U₀)
          m).addHaarScalarFactor (originalTupleVolume d))
    (originalEdgeFamilyVolume (V := reverseVertex W)
      (paperEndpointFixedBaseFinBasis W B U₀ hU₀)).restrict chartPiece =
      c⁻¹ •
        (Measure.map sourceChart
          (m.restrict
            (topologyTupleRawOrderSourceRecursiveDetChartSet
              (K := ℝ) (ρ := ρ) (κ' := κ')))).restrict chartPiece := by
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  let d := paperEndpointFixedBaseDim W B U₀
  let sourceChart : TopologyTuple ρ κ' ℝ →
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
    paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
      (K := ℝ) W B U₀ hU₀
  let c :=
    ((Measure.map
        (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
          W B U₀)
        m).addHaarScalarFactor (originalTupleVolume d))
  let volume :=
    originalEdgeFamilyVolume (V := reverseVertex W)
      (paperEndpointFixedBaseFinBasis W B U₀ hU₀)
  let L : TopologyTuple ρ κ' ℝ ≃L[ℝ] Tuple (k := ℝ) d :=
    paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv W B U₀
  haveI : Measure.IsAddHaarMeasure (Measure.map L m) :=
    L.isAddHaarMeasure_map m
  haveI : Measure.IsAddHaarMeasure (originalTupleVolume d) :=
    isAddHaarMeasure_originalTupleVolume d
  have hc_pos : 0 < c := by
    simpa [c, L] using
      MeasureTheory.Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
        (Measure.map L m) (originalTupleVolume d)
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hchart :
      (Measure.map sourceChart
        (m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ')))).restrict chartPiece =
        c • volume.restrict chartPiece := by
    simpa [sourceChart, c, volume, ρ, κ', d] using
      map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_restrict_chartPiece_eq_smul_originalEdgeFamilyVolume_restrict_chartPiece
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) m
        hchartPiece hchartPiece_sub
  simpa [sourceChart, c, volume, ρ, κ', d] using
    measure_eq_inv_smul_of_eq_nnreal_smul
      (μ := (Measure.map sourceChart
        (m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ')))).restrict chartPiece)
      (ν := volume.restrict chartPiece) (c := c) hc_ne hchart

set_option linter.style.longLine false in
/-- The formal-product retained-passive p.13 source-chart Jacobian measure is
the restricted original edge-family volume on the named p.13 source edge-family
set, up to the tuple-side full-space Haar scalar.

This keeps the same nonclaims as the restricted theorem: no restricted Haar
claim, no scalar normalization, no source coverage, and no RLCT extraction. -/
theorem map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_eq_smul_originalEdgeFamilyVolume_restrict_sourceEdgeFamilySet
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [BorelSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ))
    [m.IsAddHaarMeasure] :
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀
    let d := paperEndpointFixedBaseDim W B U₀
    let S : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
    let sourceChart : TopologyTuple ρ κ' ℝ →
        (∀ p : Fin (M + 1),
          reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W B U₀ hU₀
    let sourceSet :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W B U₀ hU₀
    Measure.map
        (fun z : TopologyTuple ρ κ' ℝ ↦
          sourceChart
            (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
        ((m.restrict S).withDensity
          (fun z : TopologyTuple ρ κ' ℝ ↦
            ENNReal.ofReal
              (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                (M := M) (ρ := ρ) (κ' := κ') z))) =
      ((Measure.map
          (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
            W B U₀)
          m).addHaarScalarFactor (originalTupleVolume d)) •
        (originalEdgeFamilyVolume (V := reverseVertex W)
          (paperEndpointFixedBaseFinBasis W B U₀ hU₀)).restrict sourceSet := by
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  let d := paperEndpointFixedBaseDim W B U₀
  let S : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let T : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleRawOrderSourceRecursiveDetChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ')
  let sourceChart : TopologyTuple ρ κ' ℝ →
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
    paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
      (K := ℝ) W B U₀ hU₀
  let sourceSet : Set
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
    paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
      (K := ℝ) W B U₀ hU₀
  have hcov :=
    PaperEndpointFixedBaseRegularCoordinateSourceData.measure_map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_eq_restrict_sourceEdgeFamilySet
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) m
  have hsupport :=
    PaperEndpointFixedBaseRegularCoordinateSourceData.measure_map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_restrict_sourceEdgeFamilySet_eq_self
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) m
  have hrestrict :=
    map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_restrict_eq_smul_originalEdgeFamilyVolume_restrict_sourceEdgeFamilySet
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) m
  calc
    Measure.map
        (fun z : TopologyTuple ρ κ' ℝ ↦
          sourceChart
            (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
        ((m.restrict S).withDensity
          (fun z : TopologyTuple ρ κ' ℝ ↦
            ENNReal.ofReal
              (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                (M := M) (ρ := ρ) (κ' := κ') z))) =
        (Measure.map sourceChart (m.restrict T)).restrict sourceSet := by
          simpa [S, T, sourceChart, sourceSet, ρ, κ', d] using hcov
    _ = Measure.map sourceChart (m.restrict T) := by
          simpa [T, sourceChart, sourceSet, ρ, κ'] using hsupport
    _ =
      ((Measure.map
          (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
            W B U₀)
          m).addHaarScalarFactor (originalTupleVolume d)) •
        (originalEdgeFamilyVolume (V := reverseVertex W)
          (paperEndpointFixedBaseFinBasis W B U₀ hU₀)).restrict sourceSet := by
          simpa [T, sourceChart, sourceSet, ρ, κ', d] using hrestrict

set_option linter.style.longLine false in
/-- The formal-product p.13 source-set scalar comparison restricts to any
measurable chart piece contained in the named p.13 source edge-family set. -/
theorem map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_eq_smul_originalEdgeFamilyVolume_restrict_chartPiece
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [BorelSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ))
    [m.IsAddHaarMeasure]
    {chartPiece : Set
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)}
    (hchartPiece : MeasurableSet chartPiece)
    (hchartPiece_sub :
      chartPiece ⊆
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
          (K := ℝ) W B U₀ hU₀) :
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀
    let d := paperEndpointFixedBaseDim W B U₀
    let S : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
    let sourceChart : TopologyTuple ρ κ' ℝ →
        (∀ p : Fin (M + 1),
          reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W B U₀ hU₀
    let c :=
      ((Measure.map
          (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
            W B U₀)
          m).addHaarScalarFactor (originalTupleVolume d))
    (Measure.map
        (fun z : TopologyTuple ρ κ' ℝ ↦
          sourceChart
            (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
        ((m.restrict S).withDensity
          (fun z : TopologyTuple ρ κ' ℝ ↦
            ENNReal.ofReal
              (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                (M := M) (ρ := ρ) (κ' := κ') z)))).restrict chartPiece =
      c •
        (originalEdgeFamilyVolume (V := reverseVertex W)
          (paperEndpointFixedBaseFinBasis W B U₀ hU₀)).restrict chartPiece := by
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  let d := paperEndpointFixedBaseDim W B U₀
  let S : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let sourceChart : TopologyTuple ρ κ' ℝ →
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
    paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
      (K := ℝ) W B U₀ hU₀
  let sourceSet : Set
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
    paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
      (K := ℝ) W B U₀ hU₀
  let c :=
    ((Measure.map
        (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
          W B U₀)
        m).addHaarScalarFactor (originalTupleVolume d))
  let volume :=
    originalEdgeFamilyVolume (V := reverseVertex W)
      (paperEndpointFixedBaseFinBasis W B U₀ hU₀)
  have _hchartPiece : MeasurableSet chartPiece := hchartPiece
  have hsub : chartPiece ⊆ sourceSet := by
    simpa [sourceSet] using hchartPiece_sub
  have hsourceSet :=
    map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_eq_smul_originalEdgeFamilyVolume_restrict_sourceEdgeFamilySet
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) m
  calc
    (Measure.map
        (fun z : TopologyTuple ρ κ' ℝ ↦
          sourceChart
            (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
        ((m.restrict S).withDensity
          (fun z : TopologyTuple ρ κ' ℝ ↦
            ENNReal.ofReal
              (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                (M := M) (ρ := ρ) (κ' := κ') z)))).restrict chartPiece =
        (c • volume.restrict sourceSet).restrict chartPiece := by
          simpa [S, sourceChart, sourceSet, c, volume, ρ, κ', d] using
            congrArg (fun μ ↦ μ.restrict chartPiece) hsourceSet
    _ = c • (volume.restrict sourceSet).restrict chartPiece := by
          rw [Measure.restrict_smul]
    _ = c • volume.restrict chartPiece := by
          rw [Measure.restrict_restrict_of_subset hsub]


set_option linter.style.longLine false in
/-- If the restricted original edge-family volume on a p.13 chart piece is
controlled by a source reference measure, then the formal-product p.13 chart
measure is controlled by the same source reference with the tuple-side Haar
scalar multiplied in front.

This only transfers a supplied restricted-volume domination through the
already-proved p.13 chart-piece measure equality.  It does not prove the
restricted-volume domination or identify the source reference with a
passive-theta source image. -/
theorem map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_le_smul_sourceMeasure_of_originalEdgeFamilyVolume_restrict_chartPiece_le_smul
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [BorelSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ))
    [m.IsAddHaarMeasure]
    {chartPiece : Set
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)}
    (hchartPiece : MeasurableSet chartPiece)
    (hchartPiece_sub :
      chartPiece ⊆
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
          (K := ℝ) W B U₀ hU₀)
    {sourceRef : Measure
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)}
    {D : ℝ≥0∞}
    (hvolume_source :
      (originalEdgeFamilyVolume (V := reverseVertex W)
        (paperEndpointFixedBaseFinBasis W B U₀ hU₀)).restrict chartPiece ≤
        D • sourceRef) :
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀
    let d := paperEndpointFixedBaseDim W B U₀
    let S : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
    let sourceChart : TopologyTuple ρ κ' ℝ →
        (∀ p : Fin (M + 1),
          reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W B U₀ hU₀
    let c :=
      ((Measure.map
          (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
            W B U₀)
          m).addHaarScalarFactor (originalTupleVolume d))
    (Measure.map
        (fun z : TopologyTuple ρ κ' ℝ ↦
          sourceChart
            (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
        ((m.restrict S).withDensity
          (fun z : TopologyTuple ρ κ' ℝ ↦
            ENNReal.ofReal
              (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                (M := M) (ρ := ρ) (κ' := κ') z)))).restrict chartPiece ≤
      (((c : ℝ≥0∞) * D) • sourceRef) := by
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  let d := paperEndpointFixedBaseDim W B U₀
  let S : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let sourceChart : TopologyTuple ρ κ' ℝ →
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
    paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
      (K := ℝ) W B U₀ hU₀
  let c :=
    ((Measure.map
        (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
          W B U₀)
        m).addHaarScalarFactor (originalTupleVolume d))
  let volume :=
    originalEdgeFamilyVolume (V := reverseVertex W)
      (paperEndpointFixedBaseFinBasis W B U₀ hU₀)
  let muP13 :=
    (Measure.map
      (fun z : TopologyTuple ρ κ' ℝ ↦
        sourceChart
          (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
      ((m.restrict S).withDensity
        (fun z : TopologyTuple ρ κ' ℝ ↦
          ENNReal.ofReal
            (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
              (M := M) (ρ := ρ) (κ' := κ') z)))).restrict chartPiece
  have hformal_eq : muP13 = c • volume.restrict chartPiece := by
    simpa [S, sourceChart, c, volume, muP13, ρ, κ', d] using
      map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_eq_smul_originalEdgeFamilyVolume_restrict_chartPiece
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) m
        hchartPiece hchartPiece_sub
  refine Measure.le_iff.2 ?_
  intro t _ht
  have hD := hvolume_source t
  simp only [Measure.smul_apply, smul_eq_mul] at hD
  calc
    muP13 t = (c • volume.restrict chartPiece) t := by rw [hformal_eq]
    _ = (c : ℝ≥0∞) * (volume.restrict chartPiece) t := by
      rw [Measure.coe_nnreal_smul_apply]
    _ ≤ (c : ℝ≥0∞) * (D * sourceRef t) :=
      mul_le_mul_right hD (c : ℝ≥0∞)
    _ = ((c : ℝ≥0∞) * D) * sourceRef t := by
      rw [mul_assoc]
    _ = (((c : ℝ≥0∞) * D) • sourceRef) t := by
      simp [Measure.smul_apply, smul_eq_mul]

set_option linter.style.longLine false in
/-- A bounded-density source-reference identification of the restricted
original edge-family volume on a p.13 chart piece gives domination of the
formal-product p.13 chart measure by the same source reference, with the
tuple-side Haar scalar multiplied into the density bound.

This is the forward source-image handoff: it is elementary measure
bookkeeping on top of the p.13 formal-product/original-volume comparison.  It
does not prove the original-volume/source-reference density identity, the
density bound, source coverage, or any normal-crossing/RLCT statement. -/
theorem map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_le_smul_sourceMeasure_of_originalEdgeFamilyVolume_restrict_chartPiece_eq_withDensity_bounded
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [BorelSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ))
    [m.IsAddHaarMeasure]
    {chartPiece : Set
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)}
    (hchartPiece : MeasurableSet chartPiece)
    (hchartPiece_sub :
      chartPiece ⊆
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
          (K := ℝ) W B U₀ hU₀)
    {sourceRef : Measure
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)}
    {volumeDensity :
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) → ℝ≥0∞}
    {D : ℝ≥0∞}
    (hvolume_eq :
      (originalEdgeFamilyVolume (V := reverseVertex W)
        (paperEndpointFixedBaseFinBasis W B U₀ hU₀)).restrict chartPiece =
        (sourceRef.withDensity volumeDensity).restrict chartPiece)
    (hvolumeDensity_le :
      ∀ᵐ E ∂sourceRef.restrict chartPiece, volumeDensity E ≤ D) :
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀
    let d := paperEndpointFixedBaseDim W B U₀
    let S : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
    let sourceChart : TopologyTuple ρ κ' ℝ →
        (∀ p : Fin (M + 1),
          reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W B U₀ hU₀
    let c :=
      ((Measure.map
          (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
            W B U₀)
          m).addHaarScalarFactor (originalTupleVolume d))
    (Measure.map
        (fun z : TopologyTuple ρ κ' ℝ ↦
          sourceChart
            (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
        ((m.restrict S).withDensity
          (fun z : TopologyTuple ρ κ' ℝ ↦
            ENNReal.ofReal
              (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                (M := M) (ρ := ρ) (κ' := κ') z)))).restrict chartPiece ≤
      (((c : ℝ≥0∞) * D) • sourceRef) := by
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  let d := paperEndpointFixedBaseDim W B U₀
  let S : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let sourceChart : TopologyTuple ρ κ' ℝ →
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
    paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
      (K := ℝ) W B U₀ hU₀
  let c :=
    ((Measure.map
        (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
          W B U₀)
        m).addHaarScalarFactor (originalTupleVolume d))
  let volume :=
    originalEdgeFamilyVolume (V := reverseVertex W)
      (paperEndpointFixedBaseFinBasis W B U₀ hU₀)
  have hvolume_source : volume.restrict chartPiece ≤ D • sourceRef := by
    calc
      volume.restrict chartPiece =
          (sourceRef.withDensity volumeDensity).restrict chartPiece := by
            simpa [volume] using hvolume_eq
      _ ≤ D • sourceRef := by
            exact restrict_withDensity_le_smul_of_ae_le (μ := sourceRef)
              (s := chartPiece) (f := volumeDensity) (c := D)
              hchartPiece hvolumeDensity_le
  simpa [S, sourceChart, c, volume, ρ, κ', d] using
    map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_le_smul_sourceMeasure_of_originalEdgeFamilyVolume_restrict_chartPiece_le_smul
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) m
      hchartPiece hchartPiece_sub hvolume_source


set_option linter.style.longLine false in
/-- Restricted original edge-family volume domination also supplies the p.13
formal readback measurability and domination assumptions, once the source
reference has the supplied readback pullback identity.

This composes the volume-to-source-reference domination bridge with the generic
readback handoff.  It does not prove the restricted-volume domination, identify
the source reference with a passive-theta source image, or prove any chart
coverage statement. -/
theorem map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_readback_le_smul_of_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceMeasure
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [BorelSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ))
    [m.IsAddHaarMeasure]
    {chartPiece : Set
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)}
    (hchartPiece : MeasurableSet chartPiece)
    (hchartPiece_sub :
      chartPiece ⊆
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
          (K := ℝ) W B U₀ hU₀)
    {Θ : Type*} [MeasurableSpace Θ]
    (readback :
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) → Θ)
    {sourceRef : Measure
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)}
    {thetaRef : Measure Θ} {D : ℝ≥0∞}
    (hreadback_source : AEMeasurable readback sourceRef)
    (hsource_pull : Measure.map readback sourceRef = thetaRef)
    (hvolume_source :
      (originalEdgeFamilyVolume (V := reverseVertex W)
        (paperEndpointFixedBaseFinBasis W B U₀ hU₀)).restrict chartPiece ≤
        D • sourceRef) :
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀
    let d := paperEndpointFixedBaseDim W B U₀
    let S : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
    let sourceChart : TopologyTuple ρ κ' ℝ →
        (∀ p : Fin (M + 1),
          reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W B U₀ hU₀
    let c :=
      ((Measure.map
          (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
            W B U₀)
          m).addHaarScalarFactor (originalTupleVolume d))
    let muP13 :=
      (Measure.map
        (fun z : TopologyTuple ρ κ' ℝ ↦
          sourceChart
            (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
        ((m.restrict S).withDensity
          (fun z : TopologyTuple ρ κ' ℝ ↦
            ENNReal.ofReal
              (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                (M := M) (ρ := ρ) (κ' := κ') z)))).restrict chartPiece
    AEMeasurable readback muP13 ∧
      Measure.map readback muP13 ≤ (((c : ℝ≥0∞) * D) • thetaRef) := by
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  let d := paperEndpointFixedBaseDim W B U₀
  let S : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let sourceChart : TopologyTuple ρ κ' ℝ →
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
    paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
      (K := ℝ) W B U₀ hU₀
  let c :=
    ((Measure.map
        (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
          W B U₀)
        m).addHaarScalarFactor (originalTupleVolume d))
  let muP13 :=
    (Measure.map
      (fun z : TopologyTuple ρ κ' ℝ ↦
        sourceChart
          (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
      ((m.restrict S).withDensity
        (fun z : TopologyTuple ρ κ' ℝ ↦
          ENNReal.ofReal
            (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
              (M := M) (ρ := ρ) (κ' := κ') z)))).restrict chartPiece
  have hformal_source : muP13 ≤ (((c : ℝ≥0∞) * D) • sourceRef) := by
    simpa [S, sourceChart, c, muP13, ρ, κ', d] using
      map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_le_smul_sourceMeasure_of_originalEdgeFamilyVolume_restrict_chartPiece_le_smul
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) m
        hchartPiece hchartPiece_sub hvolume_source
  exact
    readback_aemeasurable_and_map_le_smul_of_le_smul_source_measure
      (readback := readback) hreadback_source hsource_pull hformal_source

set_option linter.style.longLine false in
/-- Restricted original edge-family volume domination also supplies the p.13
formal readback measurability and domination assumptions when the source
reference itself pulls back only up to scalar domination.

This composes the volume-to-source-reference domination bridge with the generic
readback domination handoff.  It does not prove the restricted-volume
domination, identify the source reference with a passive-theta source image, or
prove any chart coverage statement. -/
theorem map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_readback_le_smul_of_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceMeasure_le
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [BorelSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ))
    [m.IsAddHaarMeasure]
    {chartPiece : Set
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)}
    (hchartPiece : MeasurableSet chartPiece)
    (hchartPiece_sub :
      chartPiece ⊆
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
          (K := ℝ) W B U₀ hU₀)
    {Θ : Type*} [MeasurableSpace Θ]
    (readback :
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) → Θ)
    {sourceRef : Measure
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)}
    {thetaRef : Measure Θ} {D Csource : ℝ≥0∞}
    (hreadback_source : AEMeasurable readback sourceRef)
    (hsource_pull_le : Measure.map readback sourceRef ≤ Csource • thetaRef)
    (hvolume_source :
      (originalEdgeFamilyVolume (V := reverseVertex W)
        (paperEndpointFixedBaseFinBasis W B U₀ hU₀)).restrict chartPiece ≤
        D • sourceRef) :
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀
    let d := paperEndpointFixedBaseDim W B U₀
    let S : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
    let sourceChart : TopologyTuple ρ κ' ℝ →
        (∀ p : Fin (M + 1),
          reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W B U₀ hU₀
    let c :=
      ((Measure.map
          (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
            W B U₀)
          m).addHaarScalarFactor (originalTupleVolume d))
    let muP13 :=
      (Measure.map
        (fun z : TopologyTuple ρ κ' ℝ ↦
          sourceChart
            (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
        ((m.restrict S).withDensity
          (fun z : TopologyTuple ρ κ' ℝ ↦
            ENNReal.ofReal
              (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                (M := M) (ρ := ρ) (κ' := κ') z)))).restrict chartPiece
    AEMeasurable readback muP13 ∧
      Measure.map readback muP13 ≤
        ((((c : ℝ≥0∞) * D) * Csource) • thetaRef) := by
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  let d := paperEndpointFixedBaseDim W B U₀
  let S : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let sourceChart : TopologyTuple ρ κ' ℝ →
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
    paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
      (K := ℝ) W B U₀ hU₀
  let c :=
    ((Measure.map
        (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
          W B U₀)
        m).addHaarScalarFactor (originalTupleVolume d))
  let muP13 :=
    (Measure.map
      (fun z : TopologyTuple ρ κ' ℝ ↦
        sourceChart
          (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
      ((m.restrict S).withDensity
        (fun z : TopologyTuple ρ κ' ℝ ↦
          ENNReal.ofReal
            (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
              (M := M) (ρ := ρ) (κ' := κ') z)))).restrict chartPiece
  have hformal_source : muP13 ≤ (((c : ℝ≥0∞) * D) • sourceRef) := by
    simpa [S, sourceChart, c, muP13, ρ, κ', d] using
      map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_le_smul_sourceMeasure_of_originalEdgeFamilyVolume_restrict_chartPiece_le_smul
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) m
        hchartPiece hchartPiece_sub hvolume_source
  simpa [S, sourceChart, c, muP13, ρ, κ', d] using
    readback_aemeasurable_and_map_le_smul_of_le_smul_source_measure_le
      (readback := readback) (C := ((c : ℝ≥0∞) * D))
      (Csource := Csource) hreadback_source hsource_pull_le hformal_source

set_option linter.style.longLine false in
/-- Inverse-scalar form of the formal-product p.13 chart-piece measure comparison. -/
theorem originalEdgeFamilyVolume_restrict_chartPiece_eq_inv_smul_map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [BorelSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ))
    [m.IsAddHaarMeasure]
    {chartPiece : Set
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)}
    (hchartPiece : MeasurableSet chartPiece)
    (hchartPiece_sub :
      chartPiece ⊆
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
          (K := ℝ) W B U₀ hU₀) :
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀
    let d := paperEndpointFixedBaseDim W B U₀
    let S : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
    let sourceChart : TopologyTuple ρ κ' ℝ →
        (∀ p : Fin (M + 1),
          reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W B U₀ hU₀
    let c :=
      ((Measure.map
          (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
            W B U₀)
          m).addHaarScalarFactor (originalTupleVolume d))
    (originalEdgeFamilyVolume (V := reverseVertex W)
      (paperEndpointFixedBaseFinBasis W B U₀ hU₀)).restrict chartPiece =
      c⁻¹ •
        (Measure.map
          (fun z : TopologyTuple ρ κ' ℝ ↦
            sourceChart
              (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
          ((m.restrict S).withDensity
            (fun z : TopologyTuple ρ κ' ℝ ↦
              ENNReal.ofReal
                (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                  (M := M) (ρ := ρ) (κ' := κ') z)))).restrict chartPiece := by
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  let d := paperEndpointFixedBaseDim W B U₀
  let S : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let sourceChart : TopologyTuple ρ κ' ℝ →
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
    paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
      (K := ℝ) W B U₀ hU₀
  let c :=
    ((Measure.map
        (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
          W B U₀)
        m).addHaarScalarFactor (originalTupleVolume d))
  let volume :=
    originalEdgeFamilyVolume (V := reverseVertex W)
      (paperEndpointFixedBaseFinBasis W B U₀ hU₀)
  let L : TopologyTuple ρ κ' ℝ ≃L[ℝ] Tuple (k := ℝ) d :=
    paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv W B U₀
  haveI : Measure.IsAddHaarMeasure (Measure.map L m) :=
    L.isAddHaarMeasure_map m
  haveI : Measure.IsAddHaarMeasure (originalTupleVolume d) :=
    isAddHaarMeasure_originalTupleVolume d
  have hc_pos : 0 < c := by
    simpa [c, L] using
      MeasureTheory.Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
        (Measure.map L m) (originalTupleVolume d)
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hchart :
      (Measure.map
        (fun z : TopologyTuple ρ κ' ℝ ↦
          sourceChart
            (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
        ((m.restrict S).withDensity
          (fun z : TopologyTuple ρ κ' ℝ ↦
            ENNReal.ofReal
              (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                (M := M) (ρ := ρ) (κ' := κ') z)))).restrict chartPiece =
        c • volume.restrict chartPiece := by
    simpa [S, sourceChart, c, volume, ρ, κ', d] using
      map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_eq_smul_originalEdgeFamilyVolume_restrict_chartPiece
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) m
        hchartPiece hchartPiece_sub
  simpa [S, sourceChart, c, volume, ρ, κ', d] using
    measure_eq_inv_smul_of_eq_nnreal_smul
      (μ := (Measure.map
        (fun z : TopologyTuple ρ κ' ℝ ↦
          sourceChart
            (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
        ((m.restrict S).withDensity
          (fun z : TopologyTuple ρ κ' ℝ ↦
            ENNReal.ofReal
              (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                (M := M) (ρ := ρ) (κ' := κ') z)))).restrict chartPiece)
      (ν := volume.restrict chartPiece) (c := c) hc_ne hchart


set_option linter.style.longLine false in
/-- The inverse-scalar p.13 formal-product comparison as a bounded-density
identity.

The density is the constant inverse of the tuple-side Haar scalar.  This is the
shape consumed by the source-image bounded-density sockets, but it is still a
formal-product p.13 chart measure statement: it does not identify that formal
measure with a passive-theta source-image reference. -/
theorem originalEdgeFamilyVolume_restrict_chartPiece_eq_withDensity_invHaar_formalProductAbsDet_restrict_chartPiece
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [BorelSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ))
    [m.IsAddHaarMeasure]
    {chartPiece : Set
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)}
    (hchartPiece : MeasurableSet chartPiece)
    (hchartPiece_sub :
      chartPiece ⊆
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
          (K := ℝ) W B U₀ hU₀) :
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀
    let d := paperEndpointFixedBaseDim W B U₀
    let S : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
    let sourceChart : TopologyTuple ρ κ' ℝ →
        (∀ p : Fin (M + 1),
          reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W B U₀ hU₀
    let c :=
      ((Measure.map
          (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
            W B U₀)
          m).addHaarScalarFactor (originalTupleVolume d))
    let formalProductMeasure : Measure
        (∀ p : Fin (M + 1),
          reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
      Measure.map
        (fun z : TopologyTuple ρ κ' ℝ ↦
          sourceChart
            (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
        ((m.restrict S).withDensity
          (fun z : TopologyTuple ρ κ' ℝ ↦
            ENNReal.ofReal
              (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                (M := M) (ρ := ρ) (κ' := κ') z)))
    let invHaarDensity :
        (∀ p : Fin (M + 1),
          reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) → ℝ≥0∞ :=
      fun _ ↦ ((c⁻¹ : NNReal) : ℝ≥0∞)
    (originalEdgeFamilyVolume (V := reverseVertex W)
      (paperEndpointFixedBaseFinBasis W B U₀ hU₀)).restrict chartPiece =
        (formalProductMeasure.withDensity invHaarDensity).restrict chartPiece ∧
      (∀ᵐ E ∂formalProductMeasure.restrict chartPiece,
        invHaarDensity E ≤ ((c⁻¹ : NNReal) : ℝ≥0∞)) := by
  intro ρ κ' d S sourceChart c formalProductMeasure invHaarDensity
  constructor
  · have hinv :=
      originalEdgeFamilyVolume_restrict_chartPiece_eq_inv_smul_map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) m
        hchartPiece hchartPiece_sub
    calc
      (originalEdgeFamilyVolume (V := reverseVertex W)
        (paperEndpointFixedBaseFinBasis W B U₀ hU₀)).restrict chartPiece =
          c⁻¹ • formalProductMeasure.restrict chartPiece := by
            simpa [ρ, κ', d, S, sourceChart, c, formalProductMeasure] using hinv
      _ = (formalProductMeasure.withDensity invHaarDensity).restrict chartPiece := by
            simp [invHaarDensity, withDensity_const, Measure.restrict_smul]
  · exact Filter.Eventually.of_forall fun _ ↦ le_rfl


set_option linter.style.longLine false in
/-- If the formal-product p.13 chart-piece measure is dominated by a source
reference measure, then the restricted original edge-family volume is dominated
by the same source reference with the inverse tuple-side Haar scalar multiplied
in front.

This is the converse direction to the existing `formalProduct <= c * original`
consumer bridge. It does not prove the supplied formal-product/source-reference
domination or identify the source reference with a passive-theta source image. -/
theorem originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceMeasure_of_map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_le_smul_sourceMeasure
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [BorelSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ))
    [m.IsAddHaarMeasure]
    {chartPiece : Set
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)}
    (hchartPiece : MeasurableSet chartPiece)
    (hchartPiece_sub :
      chartPiece ⊆
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
          (K := ℝ) W B U₀ hU₀)
    {sourceRef : Measure
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)}
    {D : ℝ≥0∞}
    (hformal_source :
      let ρ := Fin (Module.finrank ℝ U₀)
      let κ' :=
        throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀
      let S : Set (TopologyTuple ρ κ' ℝ) :=
        topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
      let sourceChart : TopologyTuple ρ κ' ℝ →
          (∀ p : Fin (M + 1),
            reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
        paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
          (K := ℝ) W B U₀ hU₀
      (Measure.map
          (fun z : TopologyTuple ρ κ' ℝ ↦
            sourceChart
              (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
          ((m.restrict S).withDensity
            (fun z : TopologyTuple ρ κ' ℝ ↦
              ENNReal.ofReal
                (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                  (M := M) (ρ := ρ) (κ' := κ') z)))).restrict chartPiece ≤
        D • sourceRef) :
    let d := paperEndpointFixedBaseDim W B U₀
    let c :=
      ((Measure.map
          (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
            W B U₀)
          m).addHaarScalarFactor (originalTupleVolume d))
    (originalEdgeFamilyVolume (V := reverseVertex W)
      (paperEndpointFixedBaseFinBasis W B U₀ hU₀)).restrict chartPiece ≤
      ((((c⁻¹ : NNReal) : ℝ≥0∞) * D) • sourceRef) := by
  intro d c
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  let S : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let sourceChart : TopologyTuple ρ κ' ℝ →
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
    paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
      (K := ℝ) W B U₀ hU₀
  let volume :=
    originalEdgeFamilyVolume (V := reverseVertex W)
      (paperEndpointFixedBaseFinBasis W B U₀ hU₀)
  let muP13 :=
    (Measure.map
      (fun z : TopologyTuple ρ κ' ℝ ↦
        sourceChart
          (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
      ((m.restrict S).withDensity
        (fun z : TopologyTuple ρ κ' ℝ ↦
          ENNReal.ofReal
            (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
              (M := M) (ρ := ρ) (κ' := κ') z)))).restrict chartPiece
  have hinv : volume.restrict chartPiece = c⁻¹ • muP13 := by
    simpa [S, sourceChart, c, volume, muP13, ρ, κ', d] using
      originalEdgeFamilyVolume_restrict_chartPiece_eq_inv_smul_map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) m
        hchartPiece hchartPiece_sub
  have hvolume_formal :
      volume.restrict chartPiece ≤ (((c⁻¹ : NNReal) : ℝ≥0∞) • muP13) := by
    rw [hinv]
    exact le_rfl
  have hformal_source' : muP13 ≤ D • sourceRef := by
    simpa [S, sourceChart, muP13, ρ, κ'] using hformal_source
  exact measure_le_smul_of_le_smul_of_le_smul hvolume_formal hformal_source'

set_option linter.style.longLine false in
/-- A bounded-density identification of the formal-product p.13 chart-piece
measure with a source reference measure implies source-reference domination of
the restricted original edge-family volume, with the inverse tuple-side Haar
scalar multiplying the density bound.

This is still conditional on the formal-product/source-reference density
identity and bound. It does not identify that source reference with a
passive-theta source image or prove source coverage. -/
theorem originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceMeasure_of_map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_eq_withDensity_bounded
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [BorelSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ))
    [m.IsAddHaarMeasure]
    {chartPiece : Set
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)}
    (hchartPiece : MeasurableSet chartPiece)
    (hchartPiece_sub :
      chartPiece ⊆
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
          (K := ℝ) W B U₀ hU₀)
    {sourceRef : Measure
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)}
    {formalDensity :
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) → ℝ≥0∞}
    {D : ℝ≥0∞}
    (hformal_eq :
      let ρ := Fin (Module.finrank ℝ U₀)
      let κ' :=
        throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀
      let S : Set (TopologyTuple ρ κ' ℝ) :=
        topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
      let sourceChart : TopologyTuple ρ κ' ℝ →
          (∀ p : Fin (M + 1),
            reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
        paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
          (K := ℝ) W B U₀ hU₀
      (Measure.map
          (fun z : TopologyTuple ρ κ' ℝ ↦
            sourceChart
              (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
          ((m.restrict S).withDensity
            (fun z : TopologyTuple ρ κ' ℝ ↦
              ENNReal.ofReal
                (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                  (M := M) (ρ := ρ) (κ' := κ') z)))).restrict chartPiece =
        (sourceRef.withDensity formalDensity).restrict chartPiece)
    (hformalDensity_le :
      ∀ᵐ E ∂sourceRef.restrict chartPiece, formalDensity E ≤ D) :
    let d := paperEndpointFixedBaseDim W B U₀
    let c :=
      ((Measure.map
          (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
            W B U₀)
          m).addHaarScalarFactor (originalTupleVolume d))
    (originalEdgeFamilyVolume (V := reverseVertex W)
      (paperEndpointFixedBaseFinBasis W B U₀ hU₀)).restrict chartPiece ≤
      ((((c⁻¹ : NNReal) : ℝ≥0∞) * D) • sourceRef) := by
  intro d c
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  let S : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let sourceChart : TopologyTuple ρ κ' ℝ →
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
    paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
      (K := ℝ) W B U₀ hU₀
  let muP13 :=
    (Measure.map
      (fun z : TopologyTuple ρ κ' ℝ ↦
        sourceChart
          (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
      ((m.restrict S).withDensity
        (fun z : TopologyTuple ρ κ' ℝ ↦
          ENNReal.ofReal
            (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
              (M := M) (ρ := ρ) (κ' := κ') z)))).restrict chartPiece
  have hformal_source : muP13 ≤ D • sourceRef := by
    calc
      muP13 = (sourceRef.withDensity formalDensity).restrict chartPiece := by
        simpa [S, sourceChart, muP13, ρ, κ'] using hformal_eq
      _ ≤ D • sourceRef := by
        exact restrict_withDensity_le_smul_of_ae_le (μ := sourceRef)
          (s := chartPiece) (f := formalDensity) (c := D)
          hchartPiece hformalDensity_le
  simpa [S, sourceChart, c, ρ, κ', d] using
    originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceMeasure_of_map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_le_smul_sourceMeasure
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) m
      hchartPiece hchartPiece_sub hformal_source

set_option linter.style.longLine false in
/-- A locally bounded original edge-family prior on a p.13 chart piece is
controlled by the formal-product p.13 chart measure, with the inverse Haar
scalar from the chart-piece measure comparison. -/
theorem originalEdgeFamilyPrior_restrict_chartPiece_le_smul_map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [BorelSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ))
    [m.IsAddHaarMeasure]
    {chartPiece : Set
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)}
    (hchartPiece : MeasurableSet chartPiece)
    (hchartPiece_sub :
      chartPiece ⊆
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
          (K := ℝ) W B U₀ hU₀)
    {density :
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) → ℝ}
    {K : ℝ}
    (hdensity :
      ∀ᵐ E ∂(originalEdgeFamilyVolume (V := reverseVertex W)
        (paperEndpointFixedBaseFinBasis W B U₀ hU₀)).restrict chartPiece,
        density E ≤ K) :
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀
    let d := paperEndpointFixedBaseDim W B U₀
    let S : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
    let sourceChart : TopologyTuple ρ κ' ℝ →
        (∀ p : Fin (M + 1),
          reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W B U₀ hU₀
    let c :=
      ((Measure.map
          (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
            W B U₀)
          m).addHaarScalarFactor (originalTupleVolume d))
    (originalEdgeFamilyPrior (V := reverseVertex W)
      (paperEndpointFixedBaseFinBasis W B U₀ hU₀) density).restrict chartPiece ≤
      (ENNReal.ofReal K * (((c⁻¹ : NNReal) : ℝ≥0∞))) •
        (Measure.map
          (fun z : TopologyTuple ρ κ' ℝ ↦
            sourceChart
              (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
          ((m.restrict S).withDensity
            (fun z : TopologyTuple ρ κ' ℝ ↦
              ENNReal.ofReal
                (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                  (M := M) (ρ := ρ) (κ' := κ') z)))).restrict chartPiece := by
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  let d := paperEndpointFixedBaseDim W B U₀
  let S : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let sourceChart : TopologyTuple ρ κ' ℝ →
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
    paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
      (K := ℝ) W B U₀ hU₀
  let c :=
    ((Measure.map
        (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
          W B U₀)
        m).addHaarScalarFactor (originalTupleVolume d))
  let volume :=
    originalEdgeFamilyVolume (V := reverseVertex W)
      (paperEndpointFixedBaseFinBasis W B U₀ hU₀)
  let muP13 :=
    (Measure.map
      (fun z : TopologyTuple ρ κ' ℝ ↦
        sourceChart
          (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
      ((m.restrict S).withDensity
        (fun z : TopologyTuple ρ κ' ℝ ↦
          ENNReal.ofReal
            (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
              (M := M) (ρ := ρ) (κ' := κ') z)))).restrict chartPiece
  have hprior :
      (originalEdgeFamilyPrior (V := reverseVertex W)
        (paperEndpointFixedBaseFinBasis W B U₀ hU₀) density).restrict chartPiece ≤
        ENNReal.ofReal K • volume.restrict chartPiece := by
    simpa [volume] using
      originalEdgeFamilyPrior_restrict_le_smul_of_ae_le
        (V := reverseVertex W)
        (paperEndpointFixedBaseFinBasis W B U₀ hU₀)
        (s := chartPiece) (K := K) hchartPiece hdensity
  have hinv : volume.restrict chartPiece = c⁻¹ • muP13 := by
    simpa [S, sourceChart, c, volume, muP13, ρ, κ', d] using
      originalEdgeFamilyVolume_restrict_chartPiece_eq_inv_smul_map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) m
        hchartPiece hchartPiece_sub
  calc
    (originalEdgeFamilyPrior (V := reverseVertex W)
      (paperEndpointFixedBaseFinBasis W B U₀ hU₀) density).restrict chartPiece ≤
        ENNReal.ofReal K • volume.restrict chartPiece := hprior
    _ = (ENNReal.ofReal K * (((c⁻¹ : NNReal) : ℝ≥0∞))) • muP13 := by
        rw [hinv]
        ext s
        simp [Measure.smul_apply, mul_assoc]

set_option linter.style.longLine false in
/-- If the formal-product p.13 chart measure is dominated after a supplied
readback, then the locally bounded original edge-family prior is dominated
after the same readback, with the density and inverse Haar scalars multiplied
in front.

This is a conditional consumer bridge.  It does not prove the readback
hypothesis, identify the formal p.13 chart measure with a passive-theta source
image measure, prove p.13 source containment, normalize the Haar scalar,
construct normal crossings, or extract an RLCT. -/
theorem originalEdgeFamilyPrior_map_readback_restrict_chartPiece_le_smul_of_formalProductAbsDet_map_readback_le_smul
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [BorelSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ))
    [m.IsAddHaarMeasure]
    {chartPiece : Set
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)}
    (hchartPiece : MeasurableSet chartPiece)
    (hchartPiece_sub :
      chartPiece ⊆
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
          (K := ℝ) W B U₀ hU₀)
    {density :
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) → ℝ}
    {K : ℝ}
    (hdensity :
      ∀ᵐ E ∂(originalEdgeFamilyVolume (V := reverseVertex W)
        (paperEndpointFixedBaseFinBasis W B U₀ hU₀)).restrict chartPiece,
        density E ≤ K)
    {Θ : Type*} [MeasurableSpace Θ]
    (readback :
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) → Θ)
    {thetaRef : Measure Θ} {Cformal : ℝ≥0∞} :
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀
    let d := paperEndpointFixedBaseDim W B U₀
    let S : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
    let sourceChart : TopologyTuple ρ κ' ℝ →
        (∀ p : Fin (M + 1),
          reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W B U₀ hU₀
    let c :=
      ((Measure.map
          (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
            W B U₀)
          m).addHaarScalarFactor (originalTupleVolume d))
    let muP13 :=
      (Measure.map
        (fun z : TopologyTuple ρ κ' ℝ ↦
          sourceChart
            (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
        ((m.restrict S).withDensity
          (fun z : TopologyTuple ρ κ' ℝ ↦
            ENNReal.ofReal
              (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                (M := M) (ρ := ρ) (κ' := κ') z)))).restrict chartPiece
    let originalPriorPiece :=
      (originalEdgeFamilyPrior (V := reverseVertex W)
        (paperEndpointFixedBaseFinBasis W B U₀ hU₀) density).restrict chartPiece
    AEMeasurable readback muP13 →
      Measure.map readback muP13 ≤ Cformal • thetaRef →
        AEMeasurable readback originalPriorPiece ∧
          Measure.map readback originalPriorPiece ≤
            ((ENNReal.ofReal K * (((c⁻¹ : NNReal) : ℝ≥0∞))) * Cformal) •
              thetaRef := by
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  let d := paperEndpointFixedBaseDim W B U₀
  let S : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let sourceChart : TopologyTuple ρ κ' ℝ →
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
    paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
      (K := ℝ) W B U₀ hU₀
  let c :=
    ((Measure.map
        (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
          W B U₀)
        m).addHaarScalarFactor (originalTupleVolume d))
  let muP13 :=
    (Measure.map
      (fun z : TopologyTuple ρ κ' ℝ ↦
        sourceChart
          (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
      ((m.restrict S).withDensity
        (fun z : TopologyTuple ρ κ' ℝ ↦
          ENNReal.ofReal
            (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
              (M := M) (ρ := ρ) (κ' := κ') z)))).restrict chartPiece
  let originalPriorPiece :=
    (originalEdgeFamilyPrior (V := reverseVertex W)
      (paperEndpointFixedBaseFinBasis W B U₀ hU₀) density).restrict chartPiece
  let alpha : ℝ≥0∞ := ENNReal.ofReal K * (((c⁻¹ : NNReal) : ℝ≥0∞))
  dsimp only
  intro hreadback_formal hformal_readback_dom
  have hprior_p13 : originalPriorPiece ≤ alpha • muP13 := by
    simpa [S, sourceChart, c, muP13, originalPriorPiece, alpha, ρ, κ', d] using
      originalEdgeFamilyPrior_restrict_chartPiece_le_smul_map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) m
        hchartPiece hchartPiece_sub hdensity
  have hprior_ac : originalPriorPiece ≪ muP13 :=
    Measure.absolutelyContinuous_of_le_smul hprior_p13
  have hreadback_prior : AEMeasurable readback originalPriorPiece :=
    hreadback_formal.mono_ac hprior_ac
  have hmap_to_formal :
      Measure.map readback originalPriorPiece ≤
        alpha • Measure.map readback muP13 :=
    map_le_smul_map_of_le_smul_aemeasurable hreadback_formal hprior_p13
  have hdom :
      Measure.map readback originalPriorPiece ≤
        (alpha * Cformal) • thetaRef :=
    measure_le_smul_of_le_smul_of_le_smul hmap_to_formal hformal_readback_dom
  exact ⟨hreadback_prior, by simpa [alpha] using hdom⟩


set_option linter.style.longLine false in
/-- If restricted original edge-family volume is dominated by a source
reference measure with a supplied readback pullback identity, then the locally
bounded original edge-family prior has the downstream readback domination.

This composes the formal-volume source-reference handoff with the existing
original-prior-to-formal-p.13 readback bridge.  It does not prove the
restricted-volume domination or identify the source reference with a
passive-theta source image. -/
theorem originalEdgeFamilyPrior_map_readback_restrict_chartPiece_le_smul_of_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceMeasure
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [BorelSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ))
    [m.IsAddHaarMeasure]
    {chartPiece : Set
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)}
    (hchartPiece : MeasurableSet chartPiece)
    (hchartPiece_sub :
      chartPiece ⊆
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
          (K := ℝ) W B U₀ hU₀)
    {density :
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) → ℝ}
    {K : ℝ}
    (hdensity :
      ∀ᵐ E ∂(originalEdgeFamilyVolume (V := reverseVertex W)
        (paperEndpointFixedBaseFinBasis W B U₀ hU₀)).restrict chartPiece,
        density E ≤ K)
    {Θ : Type*} [MeasurableSpace Θ]
    (readback :
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) → Θ)
    {sourceRef : Measure
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)}
    {thetaRef : Measure Θ} {D : ℝ≥0∞}
    (hreadback_source : AEMeasurable readback sourceRef)
    (hsource_pull : Measure.map readback sourceRef = thetaRef)
    (hvolume_source :
      (originalEdgeFamilyVolume (V := reverseVertex W)
        (paperEndpointFixedBaseFinBasis W B U₀ hU₀)).restrict chartPiece ≤
        D • sourceRef) :
    let d := paperEndpointFixedBaseDim W B U₀
    let c :=
      ((Measure.map
          (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
            W B U₀)
          m).addHaarScalarFactor (originalTupleVolume d))
    let originalPriorPiece :=
      (originalEdgeFamilyPrior (V := reverseVertex W)
        (paperEndpointFixedBaseFinBasis W B U₀ hU₀) density).restrict chartPiece
    let alpha : ℝ≥0∞ := ENNReal.ofReal K * (((c⁻¹ : NNReal) : ℝ≥0∞))
    AEMeasurable readback originalPriorPiece ∧
      Measure.map readback originalPriorPiece ≤
        (alpha * (((c : ℝ≥0∞) * D))) • thetaRef := by
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  let d := paperEndpointFixedBaseDim W B U₀
  let S : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let sourceChart : TopologyTuple ρ κ' ℝ →
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
    paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
      (K := ℝ) W B U₀ hU₀
  let c :=
    ((Measure.map
        (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
          W B U₀)
        m).addHaarScalarFactor (originalTupleVolume d))
  let muP13 :=
    (Measure.map
      (fun z : TopologyTuple ρ κ' ℝ ↦
        sourceChart
          (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
      ((m.restrict S).withDensity
        (fun z : TopologyTuple ρ κ' ℝ ↦
          ENNReal.ofReal
            (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
              (M := M) (ρ := ρ) (κ' := κ') z)))).restrict chartPiece
  let originalPriorPiece :=
    (originalEdgeFamilyPrior (V := reverseVertex W)
      (paperEndpointFixedBaseFinBasis W B U₀ hU₀) density).restrict chartPiece
  let alpha : ℝ≥0∞ := ENNReal.ofReal K * (((c⁻¹ : NNReal) : ℝ≥0∞))
  have hformal_readback :
      AEMeasurable readback muP13 ∧
        Measure.map readback muP13 ≤
          (((c : ℝ≥0∞) * D) • thetaRef) := by
    simpa [S, sourceChart, c, muP13, ρ, κ', d] using
      map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_readback_le_smul_of_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceMeasure
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) m
        hchartPiece hchartPiece_sub readback hreadback_source hsource_pull
        hvolume_source
  have hprior :=
    originalEdgeFamilyPrior_map_readback_restrict_chartPiece_le_smul_of_formalProductAbsDet_map_readback_le_smul
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) m
      hchartPiece hchartPiece_sub (density := density) (K := K)
      hdensity readback (thetaRef := thetaRef)
      (Cformal := ((c : ℝ≥0∞) * D))
  simpa [S, sourceChart, c, muP13, originalPriorPiece, alpha, ρ, κ', d] using
    hprior hformal_readback.1 hformal_readback.2

set_option linter.style.longLine false in
/-- Source-reference domination of the formal-product p.13 chart measure gives
the readback measurability and domination assumptions needed by downstream
finite-integral sockets.

This does not prove the source-reference domination or identify the source
reference with a passive-theta source image.  It only packages the elementary
readback handoff once those facts are supplied. -/
theorem map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_readback_le_smul_of_le_smul_sourceMeasure
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [BorelSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ))
    [m.IsAddHaarMeasure]
    {chartPiece : Set
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)}
    {Θ : Type*} [MeasurableSpace Θ]
    (readback :
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) → Θ)
    {sourceRef : Measure
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)}
    {thetaRef : Measure Θ} {Cformal : ℝ≥0∞} :
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀
    let S : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
    let sourceChart : TopologyTuple ρ κ' ℝ →
        (∀ p : Fin (M + 1),
          reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W B U₀ hU₀
    let muP13 :=
      (Measure.map
        (fun z : TopologyTuple ρ κ' ℝ ↦
          sourceChart
            (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
        ((m.restrict S).withDensity
          (fun z : TopologyTuple ρ κ' ℝ ↦
            ENNReal.ofReal
              (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                (M := M) (ρ := ρ) (κ' := κ') z)))).restrict chartPiece
    AEMeasurable readback sourceRef →
      Measure.map readback sourceRef = thetaRef →
        muP13 ≤ Cformal • sourceRef →
          AEMeasurable readback muP13 ∧
            Measure.map readback muP13 ≤ Cformal • thetaRef := by
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  let S : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let sourceChart : TopologyTuple ρ κ' ℝ →
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
    paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
      (K := ℝ) W B U₀ hU₀
  let muP13 :=
    (Measure.map
      (fun z : TopologyTuple ρ κ' ℝ ↦
        sourceChart
          (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
      ((m.restrict S).withDensity
        (fun z : TopologyTuple ρ κ' ℝ ↦
          ENNReal.ofReal
            (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
              (M := M) (ρ := ρ) (κ' := κ') z)))).restrict chartPiece
  dsimp only
  intro hreadback_source hsource_pull hformal_source_dom
  exact
    readback_aemeasurable_and_map_le_smul_of_le_smul_source_measure
      (readback := readback) hreadback_source hsource_pull hformal_source_dom


/-- The scalar produced by the p.13 original-prior volume-source-reference
readback domination is finite whenever the supplied restricted-volume scalar is
finite. -/
theorem originalEdgeFamilyPrior_p13VolumeReadbackDominationScalar_lt_top
    {K : ℝ} {c : NNReal} {D : ℝ≥0∞}
    (hD : D < ∞) :
    (ENNReal.ofReal K * (((c⁻¹ : NNReal) : ℝ≥0∞)) *
      (((c : ℝ≥0∞) * D))) < ∞ := by
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.coe_lt_top)
    (ENNReal.mul_lt_top ENNReal.coe_lt_top hD)

/-- The scalar produced by the p.13 original-prior readback domination is
finite whenever the supplied formal-product readback scalar is finite. -/
theorem originalEdgeFamilyPrior_p13ReadbackDominationScalar_lt_top
    {K : ℝ} {c : NNReal} {Cformal : ℝ≥0∞}
    (hCformal : Cformal < ∞) :
    (ENNReal.ofReal K * (((c⁻¹ : NNReal) : ℝ≥0∞)) * Cformal) < ∞ := by
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.coe_lt_top)
    hCformal

end P13SourceMeasureBridge

end Aoyagi
end DLN
end DLNFibre

end
