import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaProductMeasure
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSector
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceMeasure

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

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- For the enlarged following-factor theta source, the retained-passive
raw-order Jacobian density has a finite eventual upper bound after composing
with the endpoint topology-tuple map.

This is the pointwise neighborhood version of the upper side of the local
Jacobian-unit sandwich.  It only supplies the `jacobianDensity` eventual bound
needed by the coordinate-source handoff; it does not construct or bound the
source-image density. -/
theorem exists_finite_eventually_le_jacobianDensity_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ q, Fintype (κ' q)] [∀ q, DecidableEq (κ' q)]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (z₀ : Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := ρ) (τ := τ) n S J) :
    let Y :
        Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
          TopologyTuple ρ κ' ℝ :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext z eNext e
    let jacobianDensity :
        Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J → ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := ρ) (κ' := κ') (Y z))
    ∃ CJ : ℝ≥0∞, CJ < ∞ ∧
      ∀ᶠ z in nhds z₀, jacobianDensity z ≤ CJ := by
  intro Y jacobianDensity
  have hYcont : Continuous Y := by
    change Continuous
      (fun z : Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext z eNext e)
    exact
      continuous_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
        (ρ := ρ) n hS hcont hnext eNext e
  have hY₀ :
      Y z₀ ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') := by
    simpa [Y] using
      case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_mem_detChartSet
        (ρ := ρ) n hS hcont hnext z₀ eNext e hdet₀
  rcases
      exists_pos_eventually_bounds_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_comp
        (M := 1) (ρ := ρ) (κ' := κ') (Y := Y) (a₀ := z₀)
        hYcont.continuousAt hY₀ with
    ⟨ε, K, hε_pos, hK_pos, hbounds⟩
  refine ⟨ENNReal.ofReal K, ENNReal.ofReal_lt_top, ?_⟩
  filter_upwards [hbounds] with z hz
  exact ENNReal.ofReal_le_ofReal hz.2

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- For the enlarged following-factor theta source, the retained-passive
raw-order Jacobian factor is a local positive bounded unit after composing
with the endpoint topology-tuple map.

This is deliberately only the raw-order determinant factor for
`topologyTupleEdgeRawOrder` after the enlarged source has already been mapped
to topology-tuple coordinates.  It does not prove the selected-entry
source-side change of variables for `Y`, does not prove raw-map Haar
transport, and does not compare to the original source prior, normal
crossings, pole order, or RLCT. -/
theorem exists_pos_open_withDensity_sandwich_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_sourceMeasure
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
    [MeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (sourceMeasure :
      Measure
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)) :
    let Y :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    ∃ ε K : ℝ, 0 < ε ∧ 0 < K ∧
      ∃ U :
        Set
          (Case2PassiveThetaWithFollowingFactor
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
  intro Y
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' : Fin 3 → Type :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  have hYcont : Continuous Y := by
    change Continuous
      (fun z : Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext z eNext e)
    exact
      continuous_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
        (ρ := ρ) n hS hcont hnext eNext e
  have hY₀ :
      Y z₀ ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') := by
    simpa [Y, ρ, κ'] using
      case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_mem_detChartSet
        (ρ := ρ) n hS hcont hnext z₀ eNext e hdet₀
  rcases
      exists_pos_eventually_bounds_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_comp
        (M := 1) (ρ := ρ) (κ' := κ') (Y := Y) (a₀ := z₀)
        hYcont.continuousAt hY₀ with
    ⟨ε, K, hε_pos, hK_pos, hbounds⟩
  rcases
      exists_open_ae_restrict_of_eventually_nhds
        (μ := sourceMeasure) (x₀ := z₀) hbounds with
    ⟨U, hUopen, hz₀U, hU_bounds⟩
  have hlower :
      ∀ᵐ z ∂ sourceMeasure.restrict U,
        ε ≤
          retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := ρ) (κ' := κ') (Y z) :=
    hU_bounds.mono fun _ hz ↦ hz.1
  have hupper :
      ∀ᵐ z ∂ sourceMeasure.restrict U,
        retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := ρ) (κ' := κ') (Y z) ≤ K :=
    hU_bounds.mono fun _ hz ↦ hz.2
  rcases
      withDensity_ofReal_sandwich_of_ae_bounds
        (μ := sourceMeasure.restrict U)
        (f := fun z ↦
          retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := ρ) (κ' := κ') (Y z))
        (ε := ε) (K := K) hlower hupper with
    ⟨hlower_measure, hupper_measure⟩
  exact ⟨ε, K, hε_pos, hK_pos, U, hUopen, hz₀U,
    hlower_measure, hupper_measure⟩

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

set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The local upper side of the concrete `Case2PassiveTheta` Jacobian
sandwich gives endpoint-sector pushforward domination for the
Jacobian-weighted passive-product theta measure.

The endpoint sector image measurability remains an explicit local hypothesis.
This theorem instantiates the conditional endpoint-sector domination transfer
with the concrete retained-passive formal raw-order Jacobian density; it still
does not identify determinant-chart Haar measure, raw-order Haar measure, a
source prior, exact passive-sector pushforward, source-image equality,
source-rank coverage, normal crossings, pole order, or RLCT. -/
theorem exists_pos_open_measure_map_case2PassiveThetaEndpointTopologyTuple_withDensity_jacobian_restrict_endpointSectorSet_le_smul_passiveProductMeasure
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
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
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
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (hY :
      Measurable
        (fun z :
            Case2PassiveTheta
              (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J ↦
          case2PassiveThetaEndpointTopologyTuple
            (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e)) :
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
    let jacobianDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J → ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    ∃ K : ℝ, 0 < K ∧
      ∃ U :
        Set
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
        IsOpen U ∧ z₀ ∈ U ∧
          (MeasurableSet
              (case2PassiveThetaEndpointSectorSet
                (ρ := Fin (Module.finrank ℝ U₀))
                n hS hcont hnext eNext e U) →
            let sectorSet :
                Set
                  (TopologyTuple (Fin (Module.finrank ℝ U₀))
                    (throughSubspaceEndpointComplementIndex
                      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ) :=
              case2PassiveThetaEndpointSectorSet
                (ρ := Fin (Module.finrank ℝ U₀))
                n hS hcont hnext eNext e U
            (Measure.map Y ((sourceMeasure.withDensity jacobianDensity).restrict U)).restrict
                sectorSet ≤
              ENNReal.ofReal K •
                (Measure.map Y (sourceMeasure.restrict U)).restrict sectorSet) := by
  intro center pivotNext signedBox weightedBox sourceMeasure Y jacobianDensity
  rcases
      exists_pos_open_withDensity_sandwich_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2PassiveThetaEndpointTopologyTuple_passiveProductMeasure
        W₂ B₂ n hS hcont hnext eNext e z₀ hdet₀ passiveMeasure Rres with
    ⟨ε, K, hε, hK, U, hUopen, hz₀U, hlower, hupper⟩
  refine ⟨K, hK, U, hUopen, hz₀U, ?_⟩
  intro hsector sectorSet
  have hdom :
      (sourceMeasure.withDensity jacobianDensity).restrict U ≤
        ENNReal.ofReal K • sourceMeasure.restrict U := by
    rw [restrict_withDensity hUopen.measurableSet]
    exact hupper
  simpa [sectorSet, Y, jacobianDensity] using
    measure_map_case2PassiveThetaEndpointTopologyTuple_restrict_endpointSectorSet_le_smul
      (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ)
      (κ' := throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
      n hS hcont hnext eNext e
      (sourceMeasure.withDensity jacobianDensity) sourceMeasure U
      hUopen.measurableSet hsector hY hdom

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- After shrinking to a local endpoint image-measurable sector, the upper side
of the concrete `Case2PassiveTheta` Jacobian sandwich gives endpoint-sector
pushforward domination without an external sector-measurability argument.

The theorem adds the standard local image-measurability hypotheses
(`PolishSpace`/`BorelSpace` on the theta domain and opens-measurable/T2 target)
and a nonzero selected pivot at the base point.  It is still local
finite-scalar domination, not determinant-chart Haar transport, raw-order Haar
transport, source-prior comparison, source-image equality, normal crossings,
pole order, or RLCT extraction. -/
theorem exists_pos_open_measurableSet_measure_map_case2PassiveThetaEndpointTopologyTuple_withDensity_jacobian_restrict_endpointSectorSet_le_smul_passiveProductMeasure
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
    [OpensMeasurableSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
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
    let jacobianDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J → ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    ∃ K : ℝ, 0 < K ∧
      ∃ V :
        Set
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
        IsOpen V ∧ z₀ ∈ V ∧
          MeasurableSet
            (case2PassiveThetaEndpointSectorSet
              (ρ := Fin (Module.finrank ℝ U₀))
              n hS hcont hnext eNext e V) ∧
            (let sectorSet :
                Set
                  (TopologyTuple (Fin (Module.finrank ℝ U₀))
                    (throughSubspaceEndpointComplementIndex
                      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ) :=
              case2PassiveThetaEndpointSectorSet
                (ρ := Fin (Module.finrank ℝ U₀))
                n hS hcont hnext eNext e V
            (Measure.map Y ((sourceMeasure.withDensity jacobianDensity).restrict V)).restrict
                sectorSet ≤
              ENNReal.ofReal K •
                (Measure.map Y (sourceMeasure.restrict V)).restrict sectorSet) := by
  intro center pivotNext signedBox weightedBox sourceMeasure Y jacobianDensity
  rcases
      exists_pos_open_withDensity_sandwich_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2PassiveThetaEndpointTopologyTuple_passiveProductMeasure
        W₂ B₂ n hS hcont hnext (U₀ := U₀) eNext e z₀ hdet₀ passiveMeasure Rres with
    ⟨ε, K, hε, hK, U, hUopen, hz₀U, _hlower, hupper⟩
  rcases
      exists_open_subset_measurableSet_case2PassiveThetaEndpointSectorSet
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ U hUopen hz₀U with
    ⟨V, hVopen, hz₀V, hVU, hsector⟩
  refine ⟨K, hK, V, hVopen, hz₀V, hsector, ?_⟩
  intro sectorSet
  have hY :
      Measurable Y := by
    simpa [Y] using
      (continuous_case2PassiveThetaEndpointTopologyTuple
        (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext eNext e).measurable
  have hweighted_restrict :
      ((sourceMeasure.restrict U).withDensity jacobianDensity).restrict V ≤
        (ENNReal.ofReal K • sourceMeasure.restrict U).restrict V := by
    exact Measure.restrict_mono Set.Subset.rfl hupper
  have hrestrict_eq :
      (sourceMeasure.withDensity jacobianDensity).restrict V =
        ((sourceMeasure.restrict U).withDensity jacobianDensity).restrict V := by
    rw [restrict_withDensity hVopen.measurableSet,
      restrict_withDensity hVopen.measurableSet]
    rw [Measure.restrict_restrict_of_subset hVU]
  have hdom :
      (sourceMeasure.withDensity jacobianDensity).restrict V ≤
        ENNReal.ofReal K • sourceMeasure.restrict V := by
    calc
      (sourceMeasure.withDensity jacobianDensity).restrict V =
          ((sourceMeasure.restrict U).withDensity jacobianDensity).restrict V :=
        hrestrict_eq
      _ ≤ (ENNReal.ofReal K • sourceMeasure.restrict U).restrict V :=
        hweighted_restrict
      _ = ENNReal.ofReal K • sourceMeasure.restrict V := by
        rw [Measure.restrict_smul]
        rw [Measure.restrict_restrict_of_subset hVU]
  simpa [sectorSet, Y, jacobianDensity] using
    measure_map_case2PassiveThetaEndpointTopologyTuple_restrict_endpointSectorSet_le_smul
      (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ)
      (κ' := throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
      n hS hcont hnext eNext e
      (sourceMeasure.withDensity jacobianDensity) sourceMeasure V
      hVopen.measurableSet hsector hY hdom

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

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- A locally bounded density over the globally Jacobian-weighted
passive-product theta measure discharges the retained-passive residual-source
hypotheses.

The returned open set is the one from the arbitrary-candidate domination
socket.  On that set, the caller supplies the a.e. upper bound for the extra
source density; `withDensity` monotonicity converts it to the required local
finite-scalar domination.  This is bounded-density bookkeeping only: it does
not identify determinant-chart Haar measure, raw-order Haar measure, an
original source prior, exact passive-sector pushforward, source-image
equality, normal crossings, pole order, or RLCT. -/
theorem exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_of_withDensity_ae_le_const_globalWithDensity_jacobian_passiveProductMeasure_finiteMass
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
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J → ℝ≥0∞)
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
    let baseJ :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveSource.withDensity jacobianDensity
    let sourceMeasure :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      baseJ.withDensity sourceDensity
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
            let μ := Measure.map sourceChart (sourceMeasure.restrict W)
            let localSource :=
              paperEndpointFixedBaseRetainedPassiveP13LocalSource
                W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
            ∀ {Csrc : ℝ≥0∞},
              (∀ᵐ z ∂ baseJ.restrict W, sourceDensity z ≤ Csrc) →
                Csrc < ∞ →
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
    baseJ sourceMeasure EdgeFamily sourceChart
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource, Y,
          jacobianDensity, baseJ, sourceMeasure, EdgeFamily, sourceChart] using
          exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_of_restrict_le_smul_globalWithDensity_jacobian_passiveProductMeasure_finiteMass
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceMeasure passiveMeasure hpassive_lt_top
            Rres ht hRres hcrit) with
    ⟨W, hWopen, hz₀W, hW⟩
  refine ⟨W, hWopen, hz₀W, ?_⟩
  intro _ _ _ μ localSource Csrc hsourceDensity_le hCsrc
  have hdom :
      sourceMeasure.restrict W ≤ Csrc • baseJ.restrict W := by
    have hlocal :
        (baseJ.withDensity sourceDensity).restrict W ≤ Csrc • baseJ.restrict W := by
      rw [restrict_withDensity hWopen.measurableSet]
      rw [← withDensity_const (μ := baseJ.restrict W) Csrc]
      exact withDensity_mono hsourceDensity_le
    simpa [sourceMeasure] using hlocal
  have hsocket :
      μ.restrict localSource = μ ∧
        ∀ {c : ℝ≥0∞},
          c < ∞ →
            sourceMeasure.restrict W ≤ c • baseJ.restrict W →
              (∀ᵐ E ∂ μ.restrict localSource,
                  0 < aoyagiCoordinateSquareSum
                    (paperEndpointFixedBaseResidualBlockCoordinateMap
                      (K := ℝ) W₂ B₂ U₀ hU₀
                      (fun E : EdgeFamily ↦ E) E)) ∧
                residualNegPowerIntegrableOn
                  (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
                  (fun E : EdgeFamily ↦ E) localSource μ t := by
    simpa [center, pivotNext, signedBox, weightedBox, passiveSource, Y,
      jacobianDensity, baseJ, sourceMeasure, EdgeFamily, sourceChart, μ,
      localSource] using hW
  exact ⟨hsocket.1, hsocket.2 hCsrc hdom⟩

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Source-stratum finite-integral handoff for a bounded-density source over
the globally Jacobian-weighted passive-product theta measure.

This removes the caller-supplied local domination field from the arbitrary
candidate theorem in the important prior-shaped case
`(passiveSource.withDensity jacobianDensity).withDensity sourceDensity`.
The only new analytic input is the local a.e. upper bound for `sourceDensity`
on the returned open sector.  It does not identify determinant-chart Haar
measure, raw-order Haar measure, an original DLN source prior, exact
passive-sector pushforward, source-image equality, source-rank coverage,
normal crossings, pole order, or RLCT. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_of_withDensity_ae_le_const_globalWithDensity_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
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
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin 2 → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W₂ B₂ U₀ hU₀
        ((fun p : Fin 2 ↦
          LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)) :
          ∀ p : Fin 2,
            reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)
        (fun E :
            (∀ p : Fin 2,
              reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ↦ E)
        H r rEdge)
    (sourceDensity :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J → ℝ≥0∞)
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hpassive_lt_top : passiveMeasure Set.univ < ∞)
    {ν :
      Measure
        (EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {loss density :
      (∀ p : Fin 2,
        reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ×
        EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)) → ℝ}
    {t R c C : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (hR : 0 < R) (hc : 0 < c) (hC : 0 ≤ C) (ht : 0 < t)
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
    let baseJ :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveSource.withDensity jacobianDensity
    let sourceMeasure :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      baseJ.withDensity sourceDensity
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    let base : EdgeFamily :=
      fun p : Fin 2 ↦ LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)
    let ρreg :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
    (∀ᶠ x in nhdsWithin base sourceStratum,
      ∀ u : EuclideanSpace ℝ ρreg,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
          c * (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) x) +
            aoyagiCoordinateSquareSum (fun i ↦ u i)) ≤ loss (x, u)) →
    (∀ᶠ x in nhdsWithin base sourceStratum,
      ∀ u : EuclideanSpace ℝ ρreg,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
          0 ≤ density (x, u)) →
    (∀ᶠ x in nhdsWithin base sourceStratum,
      ∀ u : EuclideanSpace ℝ ρreg,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
          density (x, u) ≤ C) →
    ∃ W :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen W ∧ z₀ ∈ W ∧
        ∀ [MeasurableSpace EdgeFamily] [OpensMeasurableSpace EdgeFamily]
          [BorelSpace EdgeFamily],
            ∀ {Csrc : ℝ≥0∞},
              (∀ᵐ z ∂ baseJ.restrict W, sourceDensity z ≤ Csrc) →
                Csrc < ∞ →
                  let μ := Measure.map sourceChart (sourceMeasure.restrict W)
                  ∃ U : Set EdgeFamily, IsOpen U ∧ base ∈ U ∧
                    (∫⁻ z : EdgeFamily × EuclideanSpace ℝ ρreg,
                      ENNReal.ofReal
                        ((Metric.ball (0 : EuclideanSpace ℝ ρreg) R).indicator
                          (fun u ↦
                            (loss (z.1, u)) ^
                                (-(t +
                                  (aoyagiTheorem2RegularVariableCount 2 H r : ℝ) / 2)) *
                              density (z.1, u)) z.2) ∂
                    (μ.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
  intro center pivotNext signedBox weightedBox passiveSource Y jacobianDensity
    baseJ sourceMeasure EdgeFamily sourceChart base ρreg sourceStratum
    hloss hdensity_nonneg hdensity_le
  let localSource :=
    paperEndpointFixedBaseRetainedPassiveP13LocalSource W₂ B₂ U₀ hU₀
      (fun E : EdgeFamily ↦ E)
  rcases
      exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_of_withDensity_ae_le_const_globalWithDensity_jacobian_passiveProductMeasure_finiteMass
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ sourceDensity passiveMeasure hpassive_lt_top
        Rres (le_of_lt ht) hRres hcrit with
    ⟨W, hWopen, hz₀W, hresidual⟩
  refine ⟨W, hWopen, hz₀W, ?_⟩
  intro _ _ _ Csrc hsourceDensity_le hCsrc μ
  haveI : IsFiniteMeasure passiveMeasure := ⟨hpassive_lt_top⟩
  haveI : SFinite μ := inferInstance
  have hsocket :
      μ.restrict localSource = μ ∧
        (∀ᵐ E ∂ μ.restrict localSource,
            0 < aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) E)) ∧
          residualNegPowerIntegrableOn
            (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
            (fun E : EdgeFamily ↦ E) localSource μ t := by
    simpa [center, pivotNext, signedBox, weightedBox, passiveSource, Y,
      jacobianDensity, baseJ, sourceMeasure, EdgeFamily, sourceChart, μ,
      localSource] using
      hresidual (Csrc := Csrc) hsourceDensity_le hCsrc
  have hsource_meas : MeasurableSet sourceStratum := by
    dsimp [sourceStratum]
    exact
      measurableSet_paperEndpointFixedBaseSourceRankStratum_of_continuous
        (W := W₂) (B := B₂) (Cedge := fun E : EdgeFamily ↦ E)
        (r := r) (rEdge := rEdge)
        (by simpa [EdgeFamily] using
          (continuous_id : Continuous (fun E : EdgeFamily ↦ E)))
  rcases exists_open_paperEndpointFixedBaseRetainedPassiveP13LocalSource_coverage_of_selfBase
      (K := ℝ) (W := W₂) (B := B₂) (x₀ := base)
      U₀ hU₀ (fun E : EdgeFamily ↦ E) r rEdge
      (by
        simpa [EdgeFamily] using
          (continuous_id : Continuous (fun E : EdgeFamily ↦ E)).continuousAt)
      (by rfl) with
    ⟨Ulocal, hUlocal_open, hbaseUlocal, _hUlocal_sub, hcoverage⟩
  simpa [EdgeFamily, base, localSource, ρreg, sourceStratum] using
    exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_bounds_locally_subset_localSource
      (W := W₂) (B := B₂) sourceData
      (localSource := localSource) (μ := μ) (ν := ν)
      (loss := loss) (density := density)
      (t := t) (R := R) (c := c) (C := C)
      hR hc hC ht
      hsource_meas Ulocal hUlocal_open hbaseUlocal
      (by simpa [EdgeFamily, localSource, sourceStratum] using hcoverage)
      hsocket.2.1 hsocket.2.2 hloss hdensity_nonneg hdensity_le

end PaperEndpointFixedBaseRegularCoordinateSourceData

end Aoyagi
end DLN
end DLNFibre
