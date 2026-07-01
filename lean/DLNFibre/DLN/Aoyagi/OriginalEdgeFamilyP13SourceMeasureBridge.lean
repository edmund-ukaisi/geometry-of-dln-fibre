import DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyRawOrderMeasureBridge
import DLNFibre.DLN.Aoyagi.RetainedPassiveLocalJacobianMeasure

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

end P13SourceMeasureBridge

end Aoyagi
end DLN
end DLNFibre

end
