import DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
import DLNFibre.DLN.Aoyagi.SelectedEntrySignedBoxMeasure

/-!
# Selected-entry chart-point measure bridge

This file relates the center-indexed signed-box coordinates used for the
selected-entry measure calculation to the chart-point coordinates used by the
finite normal-crossing microcertificate.  The bridge is only a change of
finite coordinate presentation.  It does not construct an analytic atlas,
prove source coverage, identify an original source prior, or extract an RLCT.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DLNFibre
namespace DLN
namespace Aoyagi

namespace SelectedEntrySignedBox
namespace CenterCoord

variable {ι : Type*} [DecidableEq ι]

/-- The syntactic chart-point type of the one-chart selected-entry
normal-crossing certificate.  This is definitionally the certificate field
`ChartPoint 0`, but keeping the product type visible gives Lean the standard
topological and measurable instances. -/
abbrev FormalChartPoint {center : Finset ι} (pivot : center) :=
  ℝ × ((center.erase pivot.1 : Finset ι) → ℝ)

/-- The normal-crossing chart point corresponding to center-indexed
selected-entry signed-box coordinates. -/
def chartPointAdapter {center : Finset ι} (pivot : center)
    (y : center → ℝ) : FormalChartPoint pivot :=
  selectedEntryCenterSqFormalJacobianChartCertificate.sourceChartPoint
    pivot (y pivot) (sourceResidual y)

/-- The selected-entry normal-crossing certificate chart map, with its product
chart-point type exposed syntactically. -/
def formalChartMap {center : Finset ι} (pivot : center)
    (x : FormalChartPoint pivot) : center → ℝ :=
  (selectedEntryCenterSqFormalJacobianChartCertificate
    (K := ℝ) pivot).chartMap (0 : Fin 1)
      (show (selectedEntryCenterSqFormalJacobianChartCertificate
        (K := ℝ) pivot).ChartPoint (0 : Fin 1) from x)

/-- Extend chart-point residual coordinates to the ambient center-index type. -/
def chartPointResidual {center : Finset ι} (pivot : center)
    (x : FormalChartPoint pivot) : ι → ℝ :=
  fun i ↦ if h : i ∈ center.erase pivot.1 then x.2 ⟨i, h⟩ else 0

/-- Rebuilding a chart point from its selected coordinate and visible residual
extension recovers the original chart point. -/
theorem sourceChartPoint_chartPointResidual_eq
    {center : Finset ι} (pivot : center) (x : FormalChartPoint pivot) :
    selectedEntryCenterSqFormalJacobianChartCertificate.sourceChartPoint
        pivot x.1 (chartPointResidual pivot x) =
      x := by
  cases x with
  | mk u residual =>
      simp [selectedEntryCenterSqFormalJacobianChartCertificate.sourceChartPoint,
        chartPointResidual]

/-- The exposed chart-point map has the selected-entry substitution formula. -/
theorem formalChartMap_eq_selectedEntryChartMap
    {center : Finset ι} (pivot : center) (x : FormalChartPoint pivot) :
    formalChartMap pivot x =
      fun i : center ↦ selectedEntryChartMap pivot.1 x.1
        (chartPointResidual pivot x) i.1 := by
  calc
    formalChartMap pivot x =
        (selectedEntryCenterSqFormalJacobianChartCertificate
          (K := ℝ) pivot).chartMap (0 : Fin 1)
          (selectedEntryCenterSqFormalJacobianChartCertificate.sourceChartPoint
            pivot x.1 (chartPointResidual pivot x)) := by
          rw [sourceChartPoint_chartPointResidual_eq pivot x]
          rfl
    _ = fun i : center ↦ selectedEntryChartMap pivot.1 x.1
        (chartPointResidual pivot x) i.1 :=
          selectedEntryCenterSqFormalJacobianChartCertificate.chartMap_sourceChartPoint_eq
            pivot x.1 (chartPointResidual pivot x)

/-- The chart-point adapter is continuous in the center-indexed signed-box
coordinates. -/
theorem continuous_chartPointAdapter {center : Finset ι} (pivot : center) :
    Continuous (chartPointAdapter pivot) := by
  unfold chartPointAdapter
  unfold selectedEntryCenterSqFormalJacobianChartCertificate.sourceChartPoint
  refine (continuous_apply pivot).prodMk ?_
  rw [continuous_pi_iff]
  intro p
  have hpcenter : p.1 ∈ center := (Finset.mem_erase.mp p.2).2
  simpa [sourceResidual, hpcenter] using
    (continuous_apply (⟨p.1, hpcenter⟩ : center) :
      Continuous fun y : center → ℝ => y ⟨p.1, hpcenter⟩)

/-- The chart-point adapter is measurable in the center-indexed signed-box
coordinates. -/
theorem measurable_chartPointAdapter {center : Finset ι} (pivot : center) :
    Measurable (chartPointAdapter pivot) :=
  (continuous_chartPointAdapter pivot).measurable

/-- The erased-center index type is equivalent to the non-pivot center subtype. -/
def erasePivotEquivCompl {center : Finset ι} (pivot : center) :
    (center.erase pivot.1 : Finset ι) ≃ {i : center // ¬ i = pivot} where
  toFun j :=
    ⟨⟨j.1, (Finset.mem_erase.mp j.2).2⟩, by
      intro h
      exact (Finset.mem_erase.mp j.2).1 (Subtype.ext_iff.mp h)⟩
  invFun i :=
    ⟨i.1.1, by
      rw [Finset.mem_erase]
      exact ⟨by
        intro h
        exact i.2 (Subtype.ext h), i.1.2⟩⟩
  left_inv j := by
    ext
    rfl
  right_inv i := by
    ext
    rfl

/-- Product box measure in chart-point coordinates. -/
def chartPointProductMeasure {center : Finset ι} (pivot : center)
    (R : center → ℝ) : Measure (FormalChartPoint pivot) :=
  (volume.restrict (Set.Ioo (-(R pivot)) (R pivot))).prod
    (Measure.pi fun i : (center.erase pivot.1 : Finset ι) =>
      volume.restrict
        (Set.Ioo (-(R ⟨i.1, (Finset.mem_erase.mp i.2).2⟩))
          (R ⟨i.1, (Finset.mem_erase.mp i.2).2⟩)))

/-- The measurable equivalence exposing `chartPointAdapter` as a finite product split. -/
def chartPointSplitEquiv {center : Finset ι} (pivot : center) :
    (center → ℝ) ≃ᵐ FormalChartPoint pivot :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : center => ℝ)
      (fun i : center => i = pivot)).trans
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.piUnique (fun _ : {i : center // i = pivot} => ℝ))
      (MeasurableEquiv.piCongrLeft
        (fun _ : (center.erase pivot.1 : Finset ι) => ℝ)
        (erasePivotEquivCompl pivot).symm))

/-- The first coordinate of the product-split equivalence is the pivot coordinate. -/
theorem chartPointSplitEquiv_fst {center : Finset ι} (pivot : center)
    (y : center → ℝ) :
    (chartPointSplitEquiv pivot y).1 = y pivot := by
  change
    (MeasurableEquiv.piUnique (fun _ : {i : center // i = pivot} => ℝ))
      (fun x : {i : center // i = pivot} => y x.1) =
      y pivot
  have hdef : ((default : {i : center // i = pivot}).1 : center) = pivot :=
    (default : {i : center // i = pivot}).2
  simp [MeasurableEquiv.piUnique, hdef]

/-- The residual coordinates of the product-split equivalence are the erased
non-pivot coordinates. -/
theorem chartPointSplitEquiv_snd {center : Finset ι} (pivot : center)
    (y : center → ℝ) (x : (center.erase pivot.1 : Finset ι)) :
    (chartPointSplitEquiv pivot y).2 x =
      y ⟨x.1, (Finset.mem_erase.mp x.2).2⟩ := by
  change
    (MeasurableEquiv.piCongrLeft
        (fun _ : (center.erase pivot.1 : Finset ι) => ℝ)
        (erasePivotEquivCompl pivot).symm)
      (fun z : {i : center // ¬i = pivot} => y z.1) x =
      y ⟨x.1, (Finset.mem_erase.mp x.2).2⟩
  have h :=
    MeasurableEquiv.piCongrLeft_apply_apply
      (e := (erasePivotEquivCompl pivot).symm)
      (β := fun _ : (center.erase pivot.1 : Finset ι) => ℝ)
      (fun z : {i : center // ¬i = pivot} => y z.1)
      ((erasePivotEquivCompl pivot) x)
  simpa [erasePivotEquivCompl] using h

/-- The finite product-split equivalence is the chart-point adapter. -/
theorem chartPointSplitEquiv_eq_chartPointAdapter {center : Finset ι}
    (pivot : center) :
    (chartPointSplitEquiv pivot : (center → ℝ) → FormalChartPoint pivot) =
      chartPointAdapter pivot := by
  funext y
  ext
  · exact chartPointSplitEquiv_fst pivot y
  · rename_i x
    rw [chartPointSplitEquiv_snd pivot y x]
    simp [chartPointAdapter,
      selectedEntryCenterSqFormalJacobianChartCertificate.sourceChartPoint,
      sourceResidual, (Finset.mem_erase.mp x.2).2]

/-- The product-split equivalence preserves the signed-box product measure. -/
theorem measurePreserving_chartPointSplitEquiv_signedBoxMeasure
    {center : Finset ι} (pivot : center) (R : center → ℝ) :
    MeasurePreserving (chartPointSplitEquiv pivot)
      (Measure.pi fun i : center => volume.restrict (Set.Ioo (-(R i)) (R i)))
      (chartPointProductMeasure pivot R) := by
  letI : Fintype {i : center // i = pivot} :=
    Subtype.fintype (p := fun i : center => i = pivot)
  letI : Unique {i : center // i = pivot} := Unique.subtypeEq pivot
  let μ : center → Measure ℝ := fun i =>
    volume.restrict (Set.Ioo (-(R i)) (R i))
  let μerase : (center.erase pivot.1 : Finset ι) → Measure ℝ := fun i =>
    volume.restrict
      (Set.Ioo (-(R ⟨i.1, (Finset.mem_erase.mp i.2).2⟩))
        (R ⟨i.1, (Finset.mem_erase.mp i.2).2⟩))
  have hsplit :=
    measurePreserving_piEquivPiSubtypeProd μ (fun i : center => i = pivot)
  have hpivot :
      MeasurePreserving
        (MeasurableEquiv.piUnique (fun _ : {i : center // i = pivot} => ℝ))
        (Measure.pi fun i : {i : center // i = pivot} => μ i)
        (volume.restrict (Set.Ioo (-(R pivot)) (R pivot))) := by
    have h :=
      measurePreserving_piUnique
        (μ := fun i : {i : center // i = pivot} => μ i)
        (X := fun _ : {i : center // i = pivot} => ℝ)
    simpa [μ] using h
  have hcompl :
      MeasurePreserving
        (MeasurableEquiv.piCongrLeft
          (fun _ : (center.erase pivot.1 : Finset ι) => ℝ)
          (erasePivotEquivCompl pivot).symm)
        (Measure.pi fun i : {i : center // ¬ i = pivot} => μ i)
        (Measure.pi μerase) := by
    have h :=
      measurePreserving_piCongrLeft
        (α := fun _ : (center.erase pivot.1 : Finset ι) => ℝ)
        (μ := μerase)
        (f := (erasePivotEquivCompl pivot).symm)
    simpa [μ, μerase, erasePivotEquivCompl] using h
  have hprod :
      MeasurePreserving
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.piUnique (fun _ : {i : center // i = pivot} => ℝ))
          (MeasurableEquiv.piCongrLeft
            (fun _ : (center.erase pivot.1 : Finset ι) => ℝ)
            (erasePivotEquivCompl pivot).symm))
        ((Measure.pi fun i : {i : center // i = pivot} => μ i).prod
          (Measure.pi fun i : {i : center // ¬ i = pivot} => μ i))
        (chartPointProductMeasure pivot R) := by
    simpa [chartPointProductMeasure, μerase] using hpivot.prod hcompl
  simpa [chartPointSplitEquiv, μ] using hsplit.trans hprod

/-- The chart-point adapter sends the center signed-box product measure to
the natural chart-point product box measure. -/
theorem map_chartPointAdapter_signedBoxMeasure_eq_chartPointProductMeasure
    {center : Finset ι} (pivot : center) (R : center → ℝ) :
    Measure.map (chartPointAdapter pivot)
        (Measure.pi fun i : center =>
          volume.restrict (Set.Ioo (-(R i)) (R i))) =
      chartPointProductMeasure pivot R := by
  rw [← chartPointSplitEquiv_eq_chartPointAdapter pivot]
  exact (measurePreserving_chartPointSplitEquiv_signedBoxMeasure pivot R).map_eq

/-- The one-chart selected-entry normal-crossing certificate chart map is
continuous as a map from chart-point coordinates to ambient center
coordinates. -/
theorem continuous_formalChartMap {center : Finset ι} (pivot : center) :
    Continuous (formalChartMap pivot) := by
  rw [continuous_pi_iff]
  intro i
  by_cases hi : i = pivot
  · subst i
    have hcomponent :
        (fun x : FormalChartPoint pivot ↦ formalChartMap pivot x pivot) =
          fun x : FormalChartPoint pivot ↦ x.1 := by
      funext x
      rw [formalChartMap_eq_selectedEntryChartMap]
      simp [selectedEntryChartMap]
    rw [hcomponent]
    simpa [FormalChartPoint] using
      (continuous_fst :
        Continuous fun x :
          ℝ × ((center.erase pivot.1 : Finset ι) → ℝ) => x.1)
  · have hi' : i.1 ≠ pivot.1 := by
      intro h
      exact hi (Subtype.ext h)
    have hmem : i.1 ∈ center.erase pivot.1 := by
      simp [Finset.mem_erase, hi', i.2]
    have hcomponent :
        (fun x :
            ℝ × ((center.erase pivot.1 : Finset ι) → ℝ) =>
          formalChartMap pivot x i) =
          fun x :
              ℝ × ((center.erase pivot.1 : Finset ι) → ℝ) =>
            x.1 * x.2 ⟨i.1, hmem⟩ := by
      funext x
      rw [formalChartMap_eq_selectedEntryChartMap]
      simp [selectedEntryChartMap, chartPointResidual, hi', hmem]
    rw [hcomponent]
    exact continuous_fst.mul
      ((continuous_apply (⟨i.1, hmem⟩ :
        (center.erase pivot.1 : Finset ι))).comp continuous_snd)

/-- The one-chart selected-entry normal-crossing certificate chart map is
measurable as a map from chart-point coordinates to ambient center
coordinates. -/
theorem measurable_formalChartMap {center : Finset ι} (pivot : center) :
    Measurable (formalChartMap pivot) :=
  (continuous_formalChartMap pivot).measurable

/-- Composing the finite normal-crossing chart map with the chart-point adapter
recovers the center-indexed selected-entry signed-box chart map. -/
theorem formalChartMap_chartPointAdapter_eq_chartMap
    {center : Finset ι} (pivot : center) (y : center → ℝ) :
    formalChartMap pivot (chartPointAdapter pivot y) =
      chartMap pivot y := by
  rw [formalChartMap, chartPointAdapter,
    selectedEntryCenterSqFormalJacobianChartCertificate.chartMap_sourceChartPoint_eq]
  rfl

/-- The adapter's normal-crossing coordinate is the selected pivot
coordinate. -/
theorem coord_chartPointAdapter_eq
    {center : Finset ι} (pivot : center) (y : center → ℝ) :
    (selectedEntryCenterSqFormalJacobianChartCertificate
      (K := ℝ) pivot).coord (0 : Fin 1) (chartPointAdapter pivot y)
        (0 : Fin 1) =
      y pivot := by
  simp [chartPointAdapter,
    selectedEntryCenterSqFormalJacobianChartCertificate.sourceChartPoint,
    selectedEntryCenterSqFormalJacobianChartCertificate]

/-- The adapter identifies the certificate loss unit with the center-coordinate
selected-entry residual unit. -/
theorem lossUnit_chartPointAdapter_eq_residualUnit
    {center : Finset ι} (pivot : center) (y : center → ℝ) :
    (selectedEntryCenterSqFormalJacobianChartCertificate
      (K := ℝ) pivot).lossUnit (0 : Fin 1) (chartPointAdapter pivot y) =
      residualUnit pivot y := by
  rw [chartPointAdapter, residualUnit]
  exact
    selectedEntryCenterSqFormalJacobianChartCertificate.lossUnit_sourceChartPoint_eq
      pivot (y pivot) (sourceResidual y)

/-- The adapter identifies the absolute certificate Jacobian/prior factor with
the center-coordinate source density. -/
theorem abs_jacobianPrior_chartPointAdapter_eq_sourceDensity
    {center : Finset ι} (pivot : center) (y : center → ℝ) :
    |(selectedEntryCenterSqFormalJacobianChartCertificate
      (K := ℝ) pivot).jacobianPrior (0 : Fin 1) (chartPointAdapter pivot y)| =
      sourceDensity pivot y := by
  rw [chartPointAdapter]
  rw [selectedEntryCenterSqFormalJacobianChartCertificate.jacobianPrior_sourceChartPoint_eq_det]
  exact (sourceDensity_eq_abs_pivotFirstJacobian_det pivot y).symm

/-- The signed-box measure pushforward through the chart-point composite is the
same Lebesgue restriction already proved for the center-indexed chart map. -/
theorem map_formalChartMap_comp_chartPointAdapter_weightedSignedBox_eq_restrict_image
    {center : Finset ι} (pivot : center) (R : center → ℝ) :
    Measure.map
        (fun y : center → ℝ =>
          formalChartMap pivot (chartPointAdapter pivot y))
        ((Measure.pi
          (fun i : center => volume.restrict (Set.Ioo (-(R i)) (R i)))).withDensity
          (fun y : center → ℝ => ENNReal.ofReal (sourceDensity pivot y))) =
      (volume : Measure (center → ℝ)).restrict
        (chartMap pivot '' signedBoxSet R) := by
  have hcomp :
      (fun y : center → ℝ =>
        formalChartMap pivot (chartPointAdapter pivot y)) =
        chartMap pivot := by
    funext y
    exact formalChartMap_chartPointAdapter_eq_chartMap pivot y
  rw [hcomp]
  exact map_chartMap_signedBoxMeasure_withDensity_sourceDensity_eq_restrict_image
    pivot R

/-- Two-stage version of the signed-box measure bridge through the
normal-crossing chart-point coordinates. -/
theorem map_formalChartMap_map_chartPointAdapter_weightedSignedBox_eq_restrict_image
    {center : Finset ι} (pivot : center) (R : center → ℝ) :
    Measure.map (formalChartMap pivot)
        (Measure.map (chartPointAdapter pivot)
          ((Measure.pi
            (fun i : center => volume.restrict (Set.Ioo (-(R i)) (R i)))).withDensity
            (fun y : center → ℝ => ENNReal.ofReal (sourceDensity pivot y)))) =
      (volume : Measure (center → ℝ)).restrict
        (chartMap pivot '' signedBoxSet R) := by
  rw [Measure.map_map (measurable_formalChartMap pivot)
    (measurable_chartPointAdapter pivot)]
  exact
    map_formalChartMap_comp_chartPointAdapter_weightedSignedBox_eq_restrict_image
      pivot R

/-- The chart-point adapter pushforward of the weighted signed-box measure is
nonzero when all source radii are positive. -/
theorem map_chartPointAdapter_weightedSignedBox_ne_zero
    {center : Finset ι} (pivot : center) {R : center → ℝ}
    (hR : ∀ i, 0 < R i) :
    Measure.map (chartPointAdapter pivot)
        ((Measure.pi
          (fun i : center => volume.restrict (Set.Ioo (-(R i)) (R i)))).withDensity
          (fun y : center → ℝ => ENNReal.ofReal (sourceDensity pivot y))) ≠ 0 := by
  exact
    (Measure.map_ne_zero_iff
      ((measurable_chartPointAdapter pivot).aemeasurable)).2
      (signedBoxMeasure_withDensity_sourceDensity_ne_zero pivot hR)

/-- The two-stage chart-point selected-entry pushforward is nonzero when all
source radii are positive. -/
theorem map_formalChartMap_map_chartPointAdapter_weightedSignedBox_ne_zero
    {center : Finset ι} (pivot : center) {R : center → ℝ}
    (hR : ∀ i, 0 < R i) :
    Measure.map (formalChartMap pivot)
        (Measure.map (chartPointAdapter pivot)
          ((Measure.pi
            (fun i : center => volume.restrict (Set.Ioo (-(R i)) (R i)))).withDensity
            (fun y : center → ℝ => ENNReal.ofReal (sourceDensity pivot y)))) ≠ 0 := by
  rw [map_formalChartMap_map_chartPointAdapter_weightedSignedBox_eq_restrict_image
    pivot R]
  exact volume_restrict_chartMap_image_signedBoxSet_ne_zero pivot hR

end CenterCoord
end SelectedEntrySignedBox

end Aoyagi
end DLN
end DLNFibre
