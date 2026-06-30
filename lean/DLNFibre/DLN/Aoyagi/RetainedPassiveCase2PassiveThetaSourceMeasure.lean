import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSector
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSelectedEntrySourceMeasure

/-!
# Case 2 passive theta source-measure adapter

This file specializes the passive selected-entry source-measure support theorem
to the concrete full theta coordinate domain.  It proves support and residual
readout for chart-produced measures on a local punctured theta sector.  It does
not identify determinant-chart Haar measure, source-prior measure, normal
crossings, pole order, or RLCT.
-/

noncomputable section

open MeasureTheory

namespace DLNFibre
namespace DLN
namespace Aoyagi

open ChartLocalSuffixState
open ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData

namespace PaperEndpointFixedBaseRegularCoordinateSourceData

universe v

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The fixed-base p.13 source edge-family chart attached to a concrete
Case 2 passive theta coordinate. -/
def case2PassiveThetaEndpointSourceChart
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂)))
    [DecidableEq (Fin (Module.finrank ℝ U₀))]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (theta :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :
    ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ :=
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W₂ B₂ U₀ hU₀
    (case2PassiveThetaEndpointRetainedData
      (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext theta eNext e)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The residual-block coordinate equivalence used by the concrete Case 2
passive theta endpoint source chart. -/
def case2PassiveThetaEndpointResidualCoordEquiv
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    {τ : Type} (n : ℕ → ℕ) {S J : ℕ}
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q) :
    AoyagiResidualBlockCoordinateIndex
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0) ≃
      Case2PassiveTheta.Center n S J :=
  case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
    n S (J + 1) (e (Fin.last 2)).symm ((e 0).symm.trans eNext)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The selected-entry inverse residual readout attached to the concrete
Case 2 passive theta endpoint source chart. -/
def case2PassiveThetaEndpointInverseReadout
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂)))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q) :
    (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
      Case2PassiveTheta.Center n S J → ℝ :=
  let residualCoordEquiv :=
    case2PassiveThetaEndpointResidualCoordEquiv W₂ B₂ n eNext e
  fun X ↦
    SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero
      (case2PassiveThetaPivotNext n hS hnext)
      (fun i : Case2PassiveTheta.Center n S J ↦
        paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W₂ B₂ U₀ hU₀
          (fun E :
              ∀ p : Fin 2,
                reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ ↦ E)
          X (residualCoordEquiv.symm i))

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The generic passive selected-entry source-measure theorem, specialized to
the concrete full `Case2PassiveTheta` coordinate domain.

The source-domain measure is arbitrary and is restricted to the local open
punctured determinant sector produced by the theorem.  The conclusion is only
support of the chart-produced source measure and exact recovery of the
selected residual `yNext` marginal.  It is not determinant-chart Haar
transport, source-prior transport, a passive-sector pushforward theorem,
normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_measure_map_case2PassiveThetaEndpointSourceChart_puncturedSector_inverseReadout_eq_yNext
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
      (Case2PassiveTheta.PassiveFields
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta.PassiveFields
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
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
    (sourceMeasure :
      Measure
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun theta ↦
        case2PassiveThetaEndpointRetainedData
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext theta eNext e
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      fun theta ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
          W₂ B₂ U₀ hU₀ (retainedData theta)
    let residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0) ≃ center :=
      case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
        n S (J + 1) (e (Fin.last 2)).symm ((e 0).symm.trans eNext)
    let inverseReadout : EdgeFamily → center → ℝ :=
      fun X ↦
        SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero pivotNext
          (fun i : center ↦
            paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) X
              (residualCoordEquiv.symm i))
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧
        (∀ z ∈ V,
          sourceChart z ∈
              paperEndpointFixedBaseRetainedPassiveP13LocalSource
                W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) ∧
            (let E :=
              paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
                (fun p : Fin 2 ↦
                  (sourceChart z p :
                    reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
            sourceReadback (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) E =
              retainedData z) ∧
            inverseReadout (sourceChart z) = z.yNext) ∧
        ∀ [MeasurableSpace EdgeFamily] [OpensMeasurableSpace EdgeFamily]
          [BorelSpace EdgeFamily],
            let μ := Measure.map sourceChart (sourceMeasure.restrict V)
            let localSource :=
              paperEndpointFixedBaseRetainedPassiveP13LocalSource
                W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
            μ.restrict localSource = μ ∧
              Measure.map inverseReadout μ =
                Measure.map Case2PassiveTheta.yNext (sourceMeasure.restrict V) := by
  intro center pivotNext EdgeFamily retainedData sourceChart residualCoordEquiv
    inverseReadout
  let ρ := Fin (Module.finrank ℝ U₀)
  let η : Type :=
    Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J
  let A1passive : η → Fin 1 → Matrix ρ ρ ℝ := fun passive ↦ passive.1
  let F2 : η → ∀ p : Fin 2,
      Matrix ρ (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ :=
    fun passive ↦ passive.2.1
  let A3passive : η → ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ ℝ :=
    fun passive ↦ passive.2.2.1
  let Ctop : η → Matrix ρ ρ ℝ := fun passive ↦ passive.2.2.2.1
  let F3 : η →
      Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ ℝ :=
    fun passive ↦ passive.2.2.2.2
  have hA1passive_cont : Continuous A1passive := by
    simpa [A1passive] using (continuous_fst : Continuous (fun passive : η ↦ passive.1))
  have hF2_cont : Continuous F2 := by
    simpa [F2] using
      (continuous_fst.comp continuous_snd :
        Continuous (fun passive : η ↦ passive.2.1))
  have hA3passive_cont : Continuous A3passive := by
    simpa [A3passive] using
      (continuous_fst.comp (continuous_snd.comp continuous_snd) :
        Continuous (fun passive : η ↦ passive.2.2.1))
  have hCtop_cont : Continuous Ctop := by
    simpa [Ctop] using
      (continuous_fst.comp
        (continuous_snd.comp (continuous_snd.comp continuous_snd)) :
        Continuous (fun passive : η ↦ passive.2.2.2.1))
  have hF3_cont : Continuous F3 := by
    simpa [F3] using
      (continuous_snd.comp
        (continuous_snd.comp (continuous_snd.comp continuous_snd)) :
        Continuous (fun passive : η ↦ passive.2.2.2.2))
  have hdet₀' :
      IsUnit (z₀.Ctop.det) ∧
        ∀ p : Fin 1, IsUnit ((z₀.A1passive p).det) := by
    simpa [case2PassiveThetaDetSector] using hdet₀
  have hCtop₀ : IsUnit ((Ctop z₀.1).det) := by
    simpa [Ctop, Case2PassiveTheta.Ctop] using hdet₀'.1
  have hA1passive₀ : ∀ p : Fin 1, IsUnit ((A1passive z₀.1 p).det) := by
    intro p
    simpa [A1passive, Case2PassiveTheta.A1passive] using hdet₀'.2 p
  have hpivot₀' :
      z₀.2
        (⟨(J + 2, J + 2),
          case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hnext⟩ :
          {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)}) ≠ 0 := by
    simpa [case2PassiveThetaPivotNonzero, case2PassiveThetaPivotNext,
      Case2PassiveTheta.yNext] using hpivot₀
  simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart,
    residualCoordEquiv, inverseReadout, case2PassiveThetaEndpointRetainedData,
    case2PassiveThetaRetainedData, Case2PassiveTheta.A1passive,
    Case2PassiveTheta.F2, Case2PassiveTheta.A3passive,
    Case2PassiveTheta.Ctop, Case2PassiveTheta.F3, Case2PassiveTheta.yNext,
    A1passive, F2, A3passive, Ctop, F3, η, ρ] using
    exists_open_measure_map_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_eq_snd
      W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
      A1passive F2 A3passive Ctop F3
      hA1passive_cont hF2_cont hA3passive_cont hCtop_cont hF3_cont
      z₀ hCtop₀ hA1passive₀ hpivot₀' sourceMeasure

end PaperEndpointFixedBaseRegularCoordinateSourceData

end Aoyagi
end DLN
end DLNFibre
