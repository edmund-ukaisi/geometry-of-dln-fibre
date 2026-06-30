import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceMeasure
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff

/-!
# Case 2 passive theta product-measure residual-source adapter

This file specializes the passive-product selected-entry residual-source
theorem to the concrete full theta coordinate domain.  The theorem uses the
domination of the restricted `yNext` marginal by finite passive mass times the
selected-entry weighted box.  It does not assert exact restricted marginal
equality, determinant-chart Haar transport, source-prior transport, normal
crossings, pole order, or RLCT.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

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
/-- The concrete `Case2PassiveTheta` passive-product selected-entry measure
discharges the retained-passive residual-source hypotheses on the local
punctured determinant sector.

The source-domain measure is
`passiveMeasure.prod weightedBox` on
`Case2PassiveTheta = Case2PassiveTheta.PassiveFields × Center`.  The proof
uses finite passive mass and the selected-entry critical inequality to
dominate the restricted `yNext` marginal by
`passiveMeasure Set.univ • weightedBox`.  It is not exact restricted marginal
equality, determinant-chart Haar transport, source-prior transport, normal
crossings, pole order, or RLCT extraction. -/
theorem exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_passiveProductMeasure_finiteMass
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
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hpassive_lt_top : passiveMeasure Set.univ < ∞)
    {t : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (ht : 0 ≤ t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      Measure.pi
        (fun i : Case2PassiveTheta.Center n S J =>
          volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      signedBox.withDensity
        (fun y : Case2PassiveTheta.Center n S J → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let sourceMeasure :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveMeasure.prod weightedBox
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧
        ∀ [MeasurableSpace EdgeFamily] [OpensMeasurableSpace EdgeFamily]
          [BorelSpace EdgeFamily],
            let μ := Measure.map sourceChart (sourceMeasure.restrict V)
            let localSource :=
              paperEndpointFixedBaseRetainedPassiveP13LocalSource
                W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
            μ.restrict localSource = μ ∧
              (∀ᵐ E ∂ μ.restrict localSource,
                  0 < aoyagiCoordinateSquareSum
                    (paperEndpointFixedBaseResidualBlockCoordinateMap
                      (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) E)) ∧
                residualNegPowerIntegrableOn
                  (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
                  (fun E : EdgeFamily ↦ E) localSource μ t := by
  intro center pivotNext signedBox weightedBox sourceMeasure EdgeFamily sourceChart
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
  simpa [center, pivotNext, signedBox, weightedBox, sourceMeasure,
    EdgeFamily, sourceChart, case2PassiveThetaEndpointSourceChart,
    case2PassiveThetaEndpointRetainedData, case2PassiveThetaRetainedData,
    Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
    Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
    Case2PassiveTheta.F3, Case2PassiveTheta.yNext, A1passive, F2,
    A3passive, Ctop, F3, η, ρ] using
    exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_passiveProductMeasure_finiteMass
      W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
      A1passive F2 A3passive Ctop F3
      hA1passive_cont hF2_cont hA3passive_cont hCtop_cont hF3_cont
      z₀ hCtop₀ hA1passive₀ hpivot₀' passiveMeasure hpassive_lt_top
      Rres ht hRres hcrit

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- A local finite-scalar domination by the concrete passive-product theta
measure is enough to discharge the retained-passive residual-source
hypotheses for an arbitrary theta-domain source measure.

The domination assumption is explicit and local to the returned punctured
sector.  This is not exact restricted marginal equality, determinant-chart
Haar transport, source-prior transport, normal crossings, pole order, or RLCT
extraction. -/
theorem exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_of_restrict_le_smul_passiveProductMeasure_finiteMass
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
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hpassive_lt_top : passiveMeasure Set.univ < ∞)
    {t : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (ht : 0 ≤ t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      Measure.pi
        (fun i : Case2PassiveTheta.Center n S J =>
          volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      signedBox.withDensity
        (fun y : Case2PassiveTheta.Center n S J → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let passiveSource :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveMeasure.prod weightedBox
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧
        ∀ [MeasurableSpace EdgeFamily] [OpensMeasurableSpace EdgeFamily]
          [BorelSpace EdgeFamily],
            let μ := Measure.map sourceChart (sourceMeasure.restrict V)
            let localSource :=
              paperEndpointFixedBaseRetainedPassiveP13LocalSource
                W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
            μ.restrict localSource = μ ∧
              ∀ {c : ℝ≥0∞},
                c < ∞ →
                  sourceMeasure.restrict V ≤ c • passiveSource →
                    (∀ᵐ E ∂ μ.restrict localSource,
                        0 < aoyagiCoordinateSquareSum
                          (paperEndpointFixedBaseResidualBlockCoordinateMap
                            (K := ℝ) W₂ B₂ U₀ hU₀
                            (fun E : EdgeFamily ↦ E) E)) ∧
                      residualNegPowerIntegrableOn
                        (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
                        (fun E : EdgeFamily ↦ E) localSource μ t := by
  intro center pivotNext signedBox weightedBox passiveSource EdgeFamily sourceChart
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
  simpa [center, pivotNext, signedBox, weightedBox, passiveSource,
    EdgeFamily, sourceChart, case2PassiveThetaEndpointSourceChart,
    case2PassiveThetaEndpointRetainedData, case2PassiveThetaRetainedData,
    Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
    Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
    Case2PassiveTheta.F3, Case2PassiveTheta.yNext, A1passive, F2,
    A3passive, Ctop, F3, η, ρ] using
    exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_of_restrict_le_smul_passiveProductMeasure_finiteMass
      W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
      A1passive F2 A3passive Ctop F3
      hA1passive_cont hF2_cont hA3passive_cont hCtop_cont hF3_cont
      z₀ hCtop₀ hA1passive₀ hpivot₀' sourceMeasure passiveMeasure
      hpassive_lt_top Rres ht hRres hcrit

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- A local bounded density over the concrete passive-product theta measure
discharges the retained-passive residual-source hypotheses.

The local bound is an explicit a.e. hypothesis on the returned punctured
sector.  This is not a construction of an original source-prior density, exact
restricted marginal equality, determinant-chart Haar transport, normal
crossings, pole order, or RLCT extraction. -/
theorem exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_of_withDensity_ae_le_const_passiveProductMeasure_finiteMass
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
    (sourceDensity :
      Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
        ℝ≥0∞)
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hpassive_lt_top : passiveMeasure Set.univ < ∞)
    {t : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (ht : 0 ≤ t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      Measure.pi
        (fun i : Case2PassiveTheta.Center n S J =>
          volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      signedBox.withDensity
        (fun y : Case2PassiveTheta.Center n S J → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let passiveSource :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveMeasure.prod weightedBox
    let density :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceDensity z
    let sourceMeasure :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveSource.withDensity density
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧
        ∀ [MeasurableSpace EdgeFamily] [OpensMeasurableSpace EdgeFamily]
          [BorelSpace EdgeFamily],
            let μ := Measure.map sourceChart (sourceMeasure.restrict V)
            let localSource :=
              paperEndpointFixedBaseRetainedPassiveP13LocalSource
                W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
            μ.restrict localSource = μ ∧
              ∀ {c : ℝ≥0∞},
                c < ∞ →
                  (∀ᵐ z ∂passiveSource.restrict V, density z ≤ c) →
                    (∀ᵐ E ∂ μ.restrict localSource,
                        0 < aoyagiCoordinateSquareSum
                          (paperEndpointFixedBaseResidualBlockCoordinateMap
                            (K := ℝ) W₂ B₂ U₀ hU₀
                            (fun E : EdgeFamily ↦ E) E)) ∧
                      residualNegPowerIntegrableOn
                        (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
                        (fun E : EdgeFamily ↦ E) localSource μ t := by
  intro center pivotNext signedBox weightedBox passiveSource density sourceMeasure
    EdgeFamily sourceChart
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
  simpa [center, pivotNext, signedBox, weightedBox, passiveSource,
    density, sourceMeasure, EdgeFamily, sourceChart,
    case2PassiveThetaEndpointSourceChart, case2PassiveThetaEndpointRetainedData,
    case2PassiveThetaRetainedData, Case2PassiveTheta.A1passive,
    Case2PassiveTheta.F2, Case2PassiveTheta.A3passive,
    Case2PassiveTheta.Ctop, Case2PassiveTheta.F3, Case2PassiveTheta.yNext,
    A1passive, F2, A3passive, Ctop, F3, η, ρ] using
    exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_of_withDensity_ae_le_const_passiveProductMeasure_finiteMass
      W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
      A1passive F2 A3passive Ctop F3
      hA1passive_cont hF2_cont hA3passive_cont hCtop_cont hF3_cont
      z₀ hCtop₀ hA1passive₀ hpivot₀' sourceDensity passiveMeasure
      hpassive_lt_top Rres ht hRres hcrit

end PaperEndpointFixedBaseRegularCoordinateSourceData

end Aoyagi
end DLN
end DLNFibre
