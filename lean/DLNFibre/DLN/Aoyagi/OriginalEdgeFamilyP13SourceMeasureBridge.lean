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
