import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaProductMeasure
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSector

/-!
# Case 2 passive theta Jacobian-measure adapter

This file specializes the passive-parameter retained-passive raw-order
Jacobian bounded-unit sandwich to the concrete full theta coordinate domain
`Case2PassiveTheta`.

It is only a chart-domain Jacobian comparison over a passive-product coordinate
measure.  It does not identify determinant-chart Haar measure, raw-order Haar
measure, an original source-prior measure, normal crossings, pole order, or
RLCT.
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

set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The concrete `Case2PassiveTheta` passive-product selected-entry measure
has a local two-sided `withDensity` sandwich by the retained-passive raw-order
Jacobian product factor.

The source-domain measure is
`passiveMeasure.prod weightedBox` on
`Case2PassiveTheta = Case2PassiveTheta.PassiveFields × Center`, and the
Jacobian factor is read from
`case2PassiveThetaEndpointTopologyTuple`.  This is only local chart-domain
Jacobian-unit bookkeeping: it does not prove determinant-chart Haar transport,
raw-order Haar transport, source-prior transport, exact passive-sector
pushforward, normal crossings, pole order, or RLCT extraction. -/
theorem exists_pos_open_withDensity_sandwich_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2PassiveThetaEndpointTopologyTuple_passiveProductMeasure
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type}
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
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
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (Rres : Case2PassiveTheta.Center n S J → ℝ) :
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
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    ∃ ε K : ℝ, 0 < ε ∧ 0 < K ∧
      ∃ U :
        Set
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
        IsOpen U ∧ z₀ ∈ U ∧
          ENNReal.ofReal ε • sourceMeasure.restrict U ≤
              (sourceMeasure.restrict U).withDensity
                (fun z ↦
                  ENNReal.ofReal
                    (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                      (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
                      (κ' := throughSubspaceEndpointComplementIndex
                        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))) ∧
            (sourceMeasure.restrict U).withDensity
                (fun z ↦
                  ENNReal.ofReal
                    (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                      (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
                      (κ' := throughSubspaceEndpointComplementIndex
                        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))) ≤
              ENNReal.ofReal K • sourceMeasure.restrict U := by
  intro center pivotNext signedBox weightedBox sourceMeasure Y
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
  simpa [center, pivotNext, signedBox, weightedBox, sourceMeasure, Y,
    case2PassiveThetaEndpointTopologyTuple, case2PassiveThetaEndpointRetainedData,
    case2PassiveThetaRetainedData, Case2PassiveTheta.A1passive,
    Case2PassiveTheta.F2, Case2PassiveTheta.A3passive,
    Case2PassiveTheta.Ctop, Case2PassiveTheta.F3, Case2PassiveTheta.yNext,
    A1passive, F2, A3passive, Ctop, F3, η, ρ] using
    exists_pos_open_withDensity_sandwich_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2EndpointTransport_withPassive_passiveProductMeasure
      W₂ B₂ n hS hcont hnext (U₀ := U₀) eNext e
      A1passive F2 A3passive Ctop F3
      hA1passive_cont hF2_cont hA3passive_cont hCtop_cont hF3_cont
      passiveMeasure Rres z₀ hCtop₀ hA1passive₀

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- A local theta-domain source measure obtained by weighting the concrete
passive-product selected-entry measure by the retained-passive raw-order
Jacobian factor discharges the retained-passive residual-source hypotheses.

The theorem first restricts the passive-product measure to a small open
Jacobian-unit neighborhood `U`, then applies the Jacobian `withDensity`
factor.  A second open neighborhood `V` comes from the residual-source socket.
This is only local domination bookkeeping; it does not identify
determinant-chart Haar measure, raw-order Haar measure, source-prior measure,
an exact passive-sector pushforward, normal crossings, pole order, or RLCT. -/
theorem exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_passiveProductMeasure_withDensity_jacobian_finiteMass
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
    let passiveSource :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveMeasure.prod weightedBox
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let jacobianDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    ∃ U :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen U ∧ z₀ ∈ U ∧
        ∃ V :
          Set
            (Case2PassiveTheta
              (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
          IsOpen V ∧ z₀ ∈ V ∧
            ∀ [MeasurableSpace EdgeFamily] [OpensMeasurableSpace EdgeFamily]
              [BorelSpace EdgeFamily],
                let sourceMeasure := (passiveSource.restrict U).withDensity jacobianDensity
                let μ := Measure.map sourceChart (sourceMeasure.restrict V)
                let localSource :=
                  paperEndpointFixedBaseRetainedPassiveP13LocalSource
                    W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
                μ.restrict localSource = μ ∧
                  (∀ᵐ E ∂ μ.restrict localSource,
                      0 < aoyagiCoordinateSquareSum
                        (paperEndpointFixedBaseResidualBlockCoordinateMap
                          (K := ℝ) W₂ B₂ U₀ hU₀
                          (fun E : EdgeFamily ↦ E) E)) ∧
                    residualNegPowerIntegrableOn
                      (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
                      (fun E : EdgeFamily ↦ E) localSource μ t := by
  intro center pivotNext signedBox weightedBox passiveSource Y jacobianDensity
    EdgeFamily sourceChart
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource, Y,
          jacobianDensity] using
          exists_pos_open_withDensity_sandwich_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2PassiveThetaEndpointTopologyTuple_passiveProductMeasure
            W₂ B₂ n hS hcont hnext (U₀ := U₀) eNext e
            z₀ hdet₀ passiveMeasure Rres) with
    ⟨ε, hε_pos, K, hK_pos, U, hUopen, hz₀U, _hlower, hupper⟩
  let sourceMeasure :
      Measure
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
    (passiveSource.restrict U).withDensity jacobianDensity
  have hsource_le_global : sourceMeasure ≤ ENNReal.ofReal K • passiveSource := by
    have hsource_le_restrict :
        sourceMeasure ≤ ENNReal.ofReal K • passiveSource.restrict U := by
      simpa [sourceMeasure, center, pivotNext, signedBox, weightedBox,
        passiveSource, Y, jacobianDensity] using hupper
    exact measure_le_smul_of_le_smul_restrict hsource_le_restrict
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource,
          EdgeFamily, sourceChart, sourceMeasure] using
          exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_of_restrict_le_smul_passiveProductMeasure_finiteMass
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceMeasure passiveMeasure hpassive_lt_top
            Rres ht hRres hcrit) with
    ⟨V, hVopen, hz₀V, hV⟩
  refine ⟨U, hUopen, hz₀U, V, hVopen, hz₀V, ?_⟩
  intro _ _ _ sourceMeasure' μ localSource
  have hV' := hV
  have hsource_restrict_le :
      sourceMeasure.restrict V ≤ ENNReal.ofReal K • passiveSource :=
    le_trans Measure.restrict_le_self hsource_le_global
  have hconcl :
      μ.restrict localSource = μ ∧
        (∀ᵐ E ∂ μ.restrict localSource,
            0 < aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W₂ B₂ U₀ hU₀
                (fun E : EdgeFamily ↦ E) E)) ∧
          residualNegPowerIntegrableOn
            (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
            (fun E : EdgeFamily ↦ E) localSource μ t := by
    simpa [center, pivotNext, signedBox, weightedBox, passiveSource,
      EdgeFamily, sourceChart, sourceMeasure, sourceMeasure', μ, localSource] using
      ⟨hV'.1,
        hV'.2 ENNReal.ofReal_lt_top hsource_restrict_le⟩
  exact hconcl

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The globally Jacobian-weighted passive-product theta measure satisfies the
retained-passive residual-source hypotheses after restricting to one open
neighborhood.

This repackages
`exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_passiveProductMeasure_withDensity_jacobian_finiteMass`:
the old two-open formulation used
`((passiveSource.restrict U).withDensity jacobianDensity).restrict V`, while
this theorem uses `(passiveSource.withDensity jacobianDensity).restrict (U ∩ V)`.
It is only restriction/`withDensity` bookkeeping, not determinant-chart Haar
transport, source-prior transport, normal crossings, pole order, or RLCT. -/
theorem exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_passiveProductMeasure_globalWithDensity_jacobian_finiteMass
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
    let passiveSource :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveMeasure.prod weightedBox
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let jacobianDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    ∃ W :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen W ∧ z₀ ∈ W ∧
        ∀ [MeasurableSpace EdgeFamily] [OpensMeasurableSpace EdgeFamily]
          [BorelSpace EdgeFamily],
            let sourceMeasure := passiveSource.withDensity jacobianDensity
            let μ := Measure.map sourceChart (sourceMeasure.restrict W)
            let localSource :=
              paperEndpointFixedBaseRetainedPassiveP13LocalSource
                W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
            μ.restrict localSource = μ ∧
              (∀ᵐ E ∂ μ.restrict localSource,
                  0 < aoyagiCoordinateSquareSum
                    (paperEndpointFixedBaseResidualBlockCoordinateMap
                      (K := ℝ) W₂ B₂ U₀ hU₀
                      (fun E : EdgeFamily ↦ E) E)) ∧
                residualNegPowerIntegrableOn
                  (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
                  (fun E : EdgeFamily ↦ E) localSource μ t := by
  intro center pivotNext signedBox weightedBox passiveSource Y jacobianDensity
    EdgeFamily sourceChart
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource, Y,
          jacobianDensity, EdgeFamily, sourceChart] using
          exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_passiveProductMeasure_withDensity_jacobian_finiteMass
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ passiveMeasure hpassive_lt_top Rres ht hRres hcrit) with
    ⟨U, hUopen, hz₀U, V, hVopen, hz₀V, hUV⟩
  refine ⟨U ∩ V, hUopen.inter hVopen, ⟨hz₀U, hz₀V⟩, ?_⟩
  intro _ _ _ sourceMeasure' μ localSource
  have hrestrict_eq :
      (passiveSource.withDensity jacobianDensity).restrict (U ∩ V) =
        ((passiveSource.restrict U).withDensity jacobianDensity).restrict V := by
    rw [restrict_withDensity (hUopen.measurableSet.inter hVopen.measurableSet),
      restrict_withDensity hVopen.measurableSet]
    rw [Measure.restrict_restrict hVopen.measurableSet]
    rw [Set.inter_comm V U]
  have hconcl := hUV
  simpa [center, pivotNext, signedBox, weightedBox, passiveSource, Y,
    jacobianDensity, EdgeFamily, sourceChart, sourceMeasure', μ, localSource,
    hrestrict_eq] using hconcl

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- A theta-domain source measure locally dominated by the globally
Jacobian-weighted passive-product theta measure satisfies the retained-passive
residual-source hypotheses on a smaller punctured sector.

The domination hypothesis is explicit and local to the returned open set.  The
proof only uses the local upper bound on the raw-order Jacobian density to
reduce to the passive-product domination socket.  It does not construct an
original source prior, identify determinant-chart Haar measure, prove an exact
passive-sector pushforward, prove source-image equality or source-rank
coverage, construct normal crossings, compute pole order, or extract RLCT. -/
theorem exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_of_restrict_le_smul_globalWithDensity_jacobian_passiveProductMeasure_finiteMass
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
    (candidateMeasure :
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
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let jacobianDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    ∃ W :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen W ∧ z₀ ∈ W ∧
        ∀ [MeasurableSpace EdgeFamily] [OpensMeasurableSpace EdgeFamily]
          [BorelSpace EdgeFamily],
            let μ := Measure.map sourceChart (candidateMeasure.restrict W)
            let localSource :=
              paperEndpointFixedBaseRetainedPassiveP13LocalSource
                W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
            μ.restrict localSource = μ ∧
              ∀ {c : ℝ≥0∞},
                c < ∞ →
                  candidateMeasure.restrict W ≤
                    c • (passiveSource.withDensity jacobianDensity).restrict W →
                    (∀ᵐ E ∂ μ.restrict localSource,
                        0 < aoyagiCoordinateSquareSum
                          (paperEndpointFixedBaseResidualBlockCoordinateMap
                            (K := ℝ) W₂ B₂ U₀ hU₀
                            (fun E : EdgeFamily ↦ E) E)) ∧
                      residualNegPowerIntegrableOn
                        (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
                        (fun E : EdgeFamily ↦ E) localSource μ t := by
  intro center pivotNext signedBox weightedBox passiveSource Y jacobianDensity
    EdgeFamily sourceChart
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource, Y,
          jacobianDensity] using
          exists_pos_open_withDensity_sandwich_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2PassiveThetaEndpointTopologyTuple_passiveProductMeasure
            W₂ B₂ n hS hcont hnext (U₀ := U₀) eNext e
            z₀ hdet₀ passiveMeasure Rres) with
    ⟨ε, hε_pos, K, hK_pos, U, hUopen, hz₀U, _hlower, hupper⟩
  let restrictedCandidate :
      Measure
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
    candidateMeasure.restrict U
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource,
          EdgeFamily, sourceChart, restrictedCandidate] using
          exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_of_restrict_le_smul_passiveProductMeasure_finiteMass
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ restrictedCandidate passiveMeasure hpassive_lt_top
            Rres ht hRres hcrit) with
    ⟨V, hVopen, hz₀V, hV⟩
  refine ⟨U ∩ V, hUopen.inter hVopen, ⟨hz₀U, hz₀V⟩, ?_⟩
  intro _ _ _ μ localSource
  have hcandidate_restrict_eq :
      (candidateMeasure.restrict U).restrict V =
        candidateMeasure.restrict (U ∩ V) := by
    rw [Measure.restrict_restrict hVopen.measurableSet]
    rw [Set.inter_comm V U]
  have hjacobian_restrict_eq :
      (passiveSource.withDensity jacobianDensity).restrict (U ∩ V) =
        ((passiveSource.restrict U).withDensity jacobianDensity).restrict V := by
    rw [restrict_withDensity (hUopen.measurableSet.inter hVopen.measurableSet),
      restrict_withDensity hVopen.measurableSet]
    rw [Measure.restrict_restrict hVopen.measurableSet]
    rw [Set.inter_comm V U]
  have hV' := hV
  refine ⟨?_, ?_⟩
  · simpa [center, pivotNext, signedBox, weightedBox, passiveSource,
      EdgeFamily, sourceChart, restrictedCandidate, μ, localSource,
      hcandidate_restrict_eq] using hV'.1
  · intro c hc hdom
    have hdom_local :
        (candidateMeasure.restrict U).restrict V ≤
          c • (((passiveSource.restrict U).withDensity jacobianDensity).restrict V) := by
      simpa [hcandidate_restrict_eq, hjacobian_restrict_eq] using hdom
    have hweighted_global :
        (passiveSource.restrict U).withDensity jacobianDensity ≤
          ENNReal.ofReal K • passiveSource := by
      have hweighted_restrict :
          (passiveSource.restrict U).withDensity jacobianDensity ≤
            ENNReal.ofReal K • passiveSource.restrict U := by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource, Y,
          jacobianDensity] using hupper
      exact measure_le_smul_of_le_smul_restrict hweighted_restrict
    have hweightedV_global :
        ((passiveSource.restrict U).withDensity jacobianDensity).restrict V ≤
          ENNReal.ofReal K • passiveSource :=
      le_trans Measure.restrict_le_self hweighted_global
    have hsource_le_passive :
        (candidateMeasure.restrict U).restrict V ≤
          (c * ENNReal.ofReal K) • passiveSource := by
      calc
        (candidateMeasure.restrict U).restrict V ≤
            c • (((passiveSource.restrict U).withDensity jacobianDensity).restrict V) :=
          hdom_local
        _ ≤ c • (ENNReal.ofReal K • passiveSource) := by
          exact Measure.le_iff.2 fun s hs ↦ by
            rw [Measure.smul_apply, Measure.smul_apply]
            exact mul_le_mul_right (hweightedV_global s) c
        _ = (c * ENNReal.ofReal K) • passiveSource := by
          rw [smul_smul]
    have hcK : c * ENNReal.ofReal K < ∞ :=
      ENNReal.mul_lt_top hc ENNReal.ofReal_lt_top
    have htail := hV'.2 hcK hsource_le_passive
    simpa [center, pivotNext, signedBox, weightedBox, passiveSource,
      EdgeFamily, sourceChart, restrictedCandidate, μ, localSource,
      hcandidate_restrict_eq] using htail

end PaperEndpointFixedBaseRegularCoordinateSourceData

end Aoyagi
end DLN
end DLNFibre
