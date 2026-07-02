import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaCoordinateInventory

/-!
# Case 2 passive-theta active C-field readout

This file records the two active retained-passive `C` factors produced by the
Case 2 passive-theta source.  The head factor is the displayed free-following
factor and the tail factor is the displayed post-pivot residual block.  These
are finite coordinate readouts only: no source-image coverage, measure
transport, Jacobian formula, normal-crossing statement, pole order, or RLCT
extraction is proved.
-/

noncomputable section

namespace DLNFibre
namespace DLN
namespace Aoyagi

open ChartLocalSuffixState
open ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData

namespace Case2PassiveTheta

set_option linter.style.longLine false in
/-- The tail active `C 1` factor of the endpoint-transported passive-theta
retained data is the displayed post-pivot residual block after reindexing by
the forward endpoint equivalences. -/
theorem endpointRetainedData_C_one_submatrix_eq_displayedPostPivotResidualBlock
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (theta : Case2PassiveTheta (ρ := ρ) (τ := τ) n S J)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q) :
    (show Matrix (κ' (Fin.last 2)) (κ' (1 : Fin 3)) ℝ from
      by
        simpa using
          (case2PassiveThetaEndpointRetainedData
            (ρ := ρ) n hS hcont hnext theta eNext e).C
            (1 : Fin 2)).submatrix (e (Fin.last 2)) (e (1 : Fin 3)) =
      case2DisplayedPostPivotResidualBlock n hS hcont
        (case2SuccessorSelectedEntrySourceResidual
          n hS hnext theta.yNext eNext) := by
  simpa [case2PassiveThetaEndpointRetainedData,
    case2PassiveThetaRetainedData,
    case2PostPivotSelectedEntryRetainedPassiveDataWithPassive,
    case2PostPivotSelectedEntryRetainedPassiveData,
    case2PostPivotRetainedPassiveData] using
    case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_C_one_submatrix_eq_displayedPostPivotResidualBlock
      (ρ := ρ) n hS hcont hnext theta.yNext eNext e

set_option linter.style.longLine false in
/-- The head active `C 0` factor of the endpoint-transported passive-theta
retained data is the displayed free following factor after reindexing by the
forward endpoint equivalences. -/
theorem endpointRetainedData_C_zero_submatrix_eq_displayedPostPivotFreeFollowingFactor
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (theta : Case2PassiveTheta (ρ := ρ) (τ := τ) n S J)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q) :
    (show Matrix (κ' (1 : Fin 3)) (κ' 0) ℝ from
      by
        simpa using
          (case2PassiveThetaEndpointRetainedData
            (ρ := ρ) n hS hcont hnext theta eNext e).C
            (0 : Fin 2)).submatrix (e (1 : Fin 3)) (e 0) =
      case2DisplayedPostPivotFreeFollowingFactor n hS hcont
        (case2SuccessorSelectedEntrySourceCprime
          n hS hcont hnext theta.yNext eNext) := by
  simpa [case2PassiveThetaEndpointRetainedData,
    case2PassiveThetaRetainedData,
    case2PostPivotSelectedEntryRetainedPassiveDataWithPassive,
    case2PostPivotSelectedEntryRetainedPassiveData,
    case2PostPivotRetainedPassiveData] using
    case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_C_zero_submatrix_eq_displayedPostPivotFreeFollowingFactor
      (ρ := ρ) n hS hcont hnext theta.yNext eNext e

end Case2PassiveTheta

namespace Case2PassiveThetaWithFollowingFactor

set_option linter.style.longLine false in
/-- The tail active `C 1` factor of the endpoint-transported enlarged
passive-theta retained data is the displayed post-pivot residual block after
reindexing by the forward endpoint equivalences. -/
theorem endpointRetainedData_C_one_submatrix_eq_displayedPostPivotResidualBlock
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (z : Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q) :
    (show Matrix (κ' (Fin.last 2)) (κ' (1 : Fin 3)) ℝ from
      by
        simpa using
          (case2PassiveThetaWithFollowingFactorEndpointRetainedData
            (ρ := ρ) n hS hcont hnext z eNext e).C
            (1 : Fin 2)).submatrix (e (Fin.last 2)) (e (1 : Fin 3)) =
      case2DisplayedPostPivotResidualBlock n hS hcont
        (case2SuccessorSelectedEntrySourceResidual
          n hS hnext z.1.yNext eNext) := by
  change
    (((case2PassiveThetaWithFollowingFactorRetainedData
          (ρ := ρ) n hS hcont hnext z eNext).C
        (1 : Fin 2)).submatrix (e (Fin.last 2)).symm (e (1 : Fin 3)).symm).submatrix
      (e (Fin.last 2)) (e (1 : Fin 3)) =
      case2DisplayedPostPivotResidualBlock n hS hcont
        (case2SuccessorSelectedEntrySourceResidual n hS hnext z.1.yNext eNext)
  have hcancel :=
    matrix_submatrix_equiv_symm_submatrix_equiv
      ((case2PassiveThetaWithFollowingFactorRetainedData
        (ρ := ρ) n hS hcont hnext z eNext).C (1 : Fin 2))
      (e (Fin.last 2)) (e (1 : Fin 3))
  have hbase :
      (case2PassiveThetaWithFollowingFactorRetainedData
        (ρ := ρ) n hS hcont hnext z eNext).C (1 : Fin 2) =
        case2DisplayedPostPivotResidualBlock n hS hcont
          (case2SuccessorSelectedEntrySourceResidual
            n hS hnext z.1.yNext eNext) := by
    change
      case2PostPivotFreeTwoEdgeFactorFamily n hS hcont
          (case2SuccessorSelectedEntrySourceResidual n hS hnext z.1.yNext eNext)
          (case2DisplayedPostPivotFreeCprimeOfFollowingFactor
            n hS hcont z.2)
          (1 : Fin 2) =
        case2DisplayedPostPivotResidualBlock n hS hcont
          (case2SuccessorSelectedEntrySourceResidual
            n hS hnext z.1.yNext eNext)
    rfl
  exact hcancel.trans hbase

set_option linter.style.longLine false in
/-- The head active `C 0` factor of the endpoint-transported enlarged
passive-theta retained data is the independently supplied following-factor
matrix after reindexing by the forward endpoint equivalences. -/
theorem endpointRetainedData_C_zero_submatrix_eq_followingFactor
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (z : Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q) :
    (show Matrix (κ' (1 : Fin 3)) (κ' 0) ℝ from
      by
        simpa using
          (case2PassiveThetaWithFollowingFactorEndpointRetainedData
            (ρ := ρ) n hS hcont hnext z eNext e).C
            (0 : Fin 2)).submatrix (e (1 : Fin 3)) (e 0) =
      z.2 := by
  change
    (((case2PassiveThetaWithFollowingFactorRetainedData
          (ρ := ρ) n hS hcont hnext z eNext).C
        (0 : Fin 2)).submatrix (e (1 : Fin 3)).symm (e 0).symm).submatrix
      (e (1 : Fin 3)) (e 0) =
      z.2
  have hcancel :=
    matrix_submatrix_equiv_symm_submatrix_equiv
      ((case2PassiveThetaWithFollowingFactorRetainedData
        (ρ := ρ) n hS hcont hnext z eNext).C (0 : Fin 2))
      (e (1 : Fin 3)) (e 0)
  have hbase :
      (case2PassiveThetaWithFollowingFactorRetainedData
        (ρ := ρ) n hS hcont hnext z eNext).C (0 : Fin 2) =
        z.2 := by
    change
      case2PostPivotFreeTwoEdgeFactorFamily n hS hcont
          (case2SuccessorSelectedEntrySourceResidual n hS hnext z.1.yNext eNext)
          (case2DisplayedPostPivotFreeCprimeOfFollowingFactor
            n hS hcont z.2)
          (0 : Fin 2) =
        z.2
    exact
      case2DisplayedPostPivotFreeFollowingFactor_freeCprimeOfFollowingFactor
        n hS hcont z.2
  exact hcancel.trans hbase

set_option linter.style.longLine false in
/-- Read the active selected-entry chart coordinates directly from an
endpoint topology tuple.

The `C 1` block is read as the already-charted successor selected-entry
coordinate function, and the `C 0` block is read as the independent following
factor.  This is a pointwise finite-coordinate readout, not a measure
transport or determinant-Haar statement. -/
noncomputable def endpointTopologyTupleActiveReadout
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    (n : ℕ → ℕ) {S J : ℕ}
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q) :
    TopologyTuple ρ κ' ℝ →
      Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J :=
  let residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
          (Case2ResidualRowIndex n S (J + 1))
          (Case2ResidualColIndex n S (J + 1)) ≃
        Case2PassiveTheta.Center n S J :=
    case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
      n S (J + 1) (Equiv.refl _) (Equiv.refl _)
  fun T ↦
    let data :=
      ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') T
    let rawData := data.endpointTransport (fun q ↦ (e q).symm)
    let yChart : Case2PassiveTheta.Center n S J → ℝ :=
      fun i ↦
        AoyagiResidualBlockCoordinateIndex.value
          (show
            Matrix (Case2ResidualRowIndex n S (J + 1))
              (Case2ResidualColIndex n S (J + 1)) ℝ from
            by
              simpa [case2PostPivotTwoEdgeDomain] using rawData.C (1 : Fin 2))
          (residualCoordEquiv.symm i)
    let F : Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ :=
      show Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ from
        by
          simpa [case2PostPivotTwoEdgeDomain] using rawData.C (0 : Fin 2)
    Case2PassiveThetaWithFollowingFactor.mk
      (ρ := ρ) (τ := τ) (n := n) (S := S) (J := J)
      rawData.A1passive rawData.F2 rawData.A3passive rawData.Ctop rawData.F3
      yChart F

set_option linter.style.longLine false in
/-- Raw retained-passive data written from charted active Case 2 coordinates.

The input center coordinate is interpreted as the already-charted active
`C 1` block, while the following factor supplies the active `C 0` block. -/
noncomputable def endpointTopologyTupleActiveWritebackRawData
    {ρ : Type*} {τ : Type}
    (n : ℕ → ℕ) {S J : ℕ}
    (z : Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :
    RetainedPassiveNonredundantCoordinateData
      (K := ℝ) (ρ := ρ) (case2PostPivotTwoEdgeDomain n S J τ) :=
  let residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
          (Case2ResidualRowIndex n S (J + 1))
          (Case2ResidualColIndex n S (J + 1)) ≃
        Case2PassiveTheta.Center n S J :=
    case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
      n S (J + 1) (Equiv.refl _) (Equiv.refl _)
  { A1passive := z.1.A1passive
    F2 := z.1.F2
    A3passive := z.1.A3passive
    C := fun p ↦ by
      classical
      by_cases hp : p = 0
      · subst p
        simpa [case2PostPivotTwoEdgeDomain] using z.2
      · have hp1 : p = 1 := Fin.eq_one_of_ne_zero p hp
        subst p
        exact
          AoyagiResidualBlockCoordinateIndex.matrix
            (fun c ↦ z.1.yNext (residualCoordEquiv c))
    Ctop := z.1.Ctop
    F3 := z.1.F3 }

set_option linter.style.longLine false in
/-- Write charted active Case 2 coordinates back into endpoint topology-tuple
coordinates.

This is the inverse coordinate map to `endpointTopologyTupleActiveReadout`.
It is linear finite-coordinate repacking; it is not the nonlinear inverse of
the selected-entry chart on original uncharted center coordinates. -/
noncomputable def endpointTopologyTupleActiveWriteback
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    (n : ℕ → ℕ) {S J : ℕ}
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q) :
    Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
      TopologyTuple ρ κ' ℝ :=
  fun z ↦
    topologyTuple
      ((endpointTopologyTupleActiveWritebackRawData
        (ρ := ρ) (τ := τ) n z).endpointTransport e)

set_option linter.style.longLine false in
/-- Reading out after writing back charted active coordinates is the identity. -/
theorem endpointTopologyTupleActiveReadout_writeback
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    (n : ℕ → ℕ) {S J : ℕ}
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (z : Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :
    endpointTopologyTupleActiveReadout (ρ := ρ) (τ := τ) n e
      (endpointTopologyTupleActiveWriteback (ρ := ρ) (τ := τ) n e z) = z := by
  classical
  dsimp [endpointTopologyTupleActiveReadout, endpointTopologyTupleActiveWriteback]
  simp [endpointTopologyTupleActiveWritebackRawData,
    Case2PassiveThetaWithFollowingFactor.mk, Case2PassiveTheta.mk,
    AoyagiResidualBlockCoordinateIndex.value, AoyagiResidualBlockCoordinateIndex.matrix,
    Equiv.apply_symm_apply,
    Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
    Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
    Case2PassiveTheta.F3, Case2PassiveTheta.yNext]

set_option linter.style.longLine false in
/-- Writing back after reading active coordinates from an endpoint tuple is the
identity. -/
theorem endpointTopologyTupleActiveWriteback_readout
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    (n : ℕ → ℕ) {S J : ℕ}
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (T : TopologyTuple ρ κ' ℝ) :
    endpointTopologyTupleActiveWriteback (ρ := ρ) (τ := τ) n e
      (endpointTopologyTupleActiveReadout (ρ := ρ) (τ := τ) n e T) = T := by
  classical
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') T
  let raw := data.endpointTransport (fun q ↦ (e q).symm)
  have hraw :
      endpointTopologyTupleActiveWritebackRawData
          (ρ := ρ) (τ := τ) n
          (endpointTopologyTupleActiveReadout (ρ := ρ) (τ := τ) n e T) =
        raw := by
    apply ext_fields
    · rfl
    · funext p
      rfl
    · funext p
      rfl
    · funext p
      ext i j
      fin_cases p
      · simp [endpointTopologyTupleActiveReadout, endpointTopologyTupleActiveWritebackRawData,
          raw, data, RetainedPassiveNonredundantCoordinateData.endpointTransport,
          Matrix.submatrix_apply, Case2PassiveThetaWithFollowingFactor.mk,
          Case2PassiveTheta.mk]
      · simp [endpointTopologyTupleActiveReadout, endpointTopologyTupleActiveWritebackRawData,
          raw, data, RetainedPassiveNonredundantCoordinateData.endpointTransport,
          Matrix.submatrix_apply, AoyagiResidualBlockCoordinateIndex.value,
          AoyagiResidualBlockCoordinateIndex.matrix,
          Case2PassiveThetaWithFollowingFactor.mk, Case2PassiveTheta.mk,
          Case2PassiveTheta.yNext]
    · rfl
    · rfl
  calc
    endpointTopologyTupleActiveWriteback (ρ := ρ) (τ := τ) n e
        (endpointTopologyTupleActiveReadout (ρ := ρ) (τ := τ) n e T)
        = topologyTuple (raw.endpointTransport e) := by
          simp [endpointTopologyTupleActiveWriteback, hraw, raw]
    _ = topologyTuple data := by
          rw [show raw.endpointTransport e = data by
            simpa [raw] using
              endpointTransport_symm_endpointTransport
                (K := ℝ) (ρ := ρ) (fun q ↦ (e q).symm) data]
    _ = T := by
          simp [data]

set_option linter.style.longLine false in
/-- The active-coordinate readout from endpoint topology tuples is continuous.

This is only continuity of finite coordinate projections and endpoint
reindexing. -/
theorem continuous_endpointTopologyTupleActiveReadout
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    (n : ℕ → ℕ) {S J : ℕ}
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q) :
    Continuous
      (endpointTopologyTupleActiveReadout
        (ρ := ρ) (τ := τ) n e) := by
  let residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
          (Case2ResidualRowIndex n S (J + 1))
          (Case2ResidualColIndex n S (J + 1)) ≃
        Case2PassiveTheta.Center n S J :=
    case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
      n S (J + 1) (Equiv.refl _) (Equiv.refl _)
  let raw :
      TopologyTuple ρ κ' ℝ →
        RetainedPassiveNonredundantCoordinateData
          (K := ℝ) (ρ := ρ) (case2PostPivotTwoEdgeDomain n S J τ) :=
    fun T ↦
      (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') T).endpointTransport
        (fun q ↦ (e q).symm)
  let C1read :
      TopologyTuple ρ κ' ℝ →
        Matrix (Case2ResidualRowIndex n S (J + 1))
          (Case2ResidualColIndex n S (J + 1)) ℝ :=
    fun T ↦
      show Matrix (Case2ResidualRowIndex n S (J + 1))
          (Case2ResidualColIndex n S (J + 1)) ℝ from
        by
          simpa [case2PostPivotTwoEdgeDomain] using (raw T).C (1 : Fin 2)
  let yRead :
      TopologyTuple ρ κ' ℝ →
        Case2PassiveTheta.Center n S J → ℝ :=
    fun T i ↦
      AoyagiResidualBlockCoordinateIndex.value (C1read T)
        (residualCoordEquiv.symm i)
  let Fread :
      TopologyTuple ρ κ' ℝ →
        Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ :=
    fun T ↦
      show Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ from
        by
          simpa [case2PostPivotTwoEdgeDomain] using (raw T).C (0 : Fin 2)
  have hraw : Continuous raw := by
    exact
      (continuous_endpointTransport
        (K := ℝ) (ρ := ρ) (κ := κ')
        (κ' := case2PostPivotTwoEdgeDomain n S J τ)
        (fun q ↦ (e q).symm)).comp
        (continuous_ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ'))
  have hA1 : Continuous (fun T ↦ (raw T).A1passive) :=
    continuous_pi (fun p ↦
      (continuous_A1passive (K := ℝ) (ρ := ρ)
        (κ' := case2PostPivotTwoEdgeDomain n S J τ) p).comp hraw)
  have hF2 : Continuous (fun T ↦ (raw T).F2) :=
    continuous_pi (fun p ↦
      (continuous_F2 (K := ℝ) (ρ := ρ)
        (κ' := case2PostPivotTwoEdgeDomain n S J τ) p).comp hraw)
  have hA3 : Continuous (fun T ↦ (raw T).A3passive) :=
    continuous_pi (fun p ↦
      (continuous_A3passive (K := ℝ) (ρ := ρ)
        (κ' := case2PostPivotTwoEdgeDomain n S J τ) p).comp hraw)
  have hCtop : Continuous (fun T ↦ (raw T).Ctop) :=
    (continuous_Ctop (K := ℝ) (ρ := ρ)
      (κ' := case2PostPivotTwoEdgeDomain n S J τ)).comp hraw
  have hF3 : Continuous (fun T ↦ (raw T).F3) :=
    (continuous_F3 (K := ℝ) (ρ := ρ)
      (κ' := case2PostPivotTwoEdgeDomain n S J τ)).comp hraw
  have hC1 : Continuous C1read := by
    simpa [C1read, case2PostPivotTwoEdgeDomain] using
      (continuous_C (K := ℝ) (ρ := ρ)
        (κ' := case2PostPivotTwoEdgeDomain n S J τ) (1 : Fin 2)).comp hraw
  have hy : Continuous yRead := by
    refine continuous_pi ?_
    intro i
    let c := residualCoordEquiv.symm i
    simpa [yRead, AoyagiResidualBlockCoordinateIndex.value, c] using
      ((continuous_apply c.2).comp ((continuous_apply c.1).comp hC1))
  have hF : Continuous Fread := by
    simpa [Fread, case2PostPivotTwoEdgeDomain] using
      (continuous_C (K := ℝ) (ρ := ρ)
        (κ' := case2PostPivotTwoEdgeDomain n S J τ) (0 : Fin 2)).comp hraw
  have hpassive :
      Continuous (fun T ↦ ((raw T).A1passive,
        ((raw T).F2, ((raw T).A3passive, ((raw T).Ctop, (raw T).F3))))) :=
    hA1.prodMk (hF2.prodMk (hA3.prodMk (hCtop.prodMk hF3)))
  have htarget :
      Continuous (fun T ↦ ((((raw T).A1passive,
        ((raw T).F2, ((raw T).A3passive, ((raw T).Ctop, (raw T).F3)))),
        yRead T), Fread T)) :=
    (hpassive.prodMk hy).prodMk hF
  change Continuous (fun T : TopologyTuple ρ κ' ℝ ↦ ((((raw T).A1passive,
    ((raw T).F2, ((raw T).A3passive, ((raw T).Ctop, (raw T).F3)))),
    yRead T), Fread T))
  exact htarget

set_option linter.style.longLine false in
/-- The active-coordinate writeback to endpoint topology tuples is continuous.

This is only continuity of finite coordinate repacking and endpoint reindexing;
it is not a determinant-Haar transport theorem. -/
theorem continuous_endpointTopologyTupleActiveWriteback
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    (n : ℕ → ℕ) {S J : ℕ}
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q) :
    Continuous
      (endpointTopologyTupleActiveWriteback
        (ρ := ρ) (τ := τ) n e) := by
  classical
  let residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
          (Case2ResidualRowIndex n S (J + 1))
          (Case2ResidualColIndex n S (J + 1)) ≃
        Case2PassiveTheta.Center n S J :=
    case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
      n S (J + 1) (Equiv.refl _) (Equiv.refl _)
  let raw :
      Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
        RetainedPassiveNonredundantCoordinateData
          (K := ℝ) (ρ := ρ) (case2PostPivotTwoEdgeDomain n S J τ) :=
    endpointTopologyTupleActiveWritebackRawData (ρ := ρ) (τ := τ) n
  have htheta :
      Continuous (fun z :
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J ↦
        z.1) :=
    continuous_fst
  have hpassive :
      Continuous (fun z :
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J ↦
        z.1.1) :=
    continuous_fst.comp htheta
  have hpassiveTail :
      Continuous (fun z :
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J ↦
        z.1.1.2) :=
    continuous_snd.comp hpassive
  have hpassiveTailTail :
      Continuous (fun z :
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J ↦
        z.1.1.2.2) :=
    continuous_snd.comp hpassiveTail
  have hCtopF3 :
      Continuous (fun z :
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J ↦
        z.1.1.2.2.2) :=
    continuous_snd.comp hpassiveTailTail
  have hA1 :
      Continuous (fun z :
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J ↦
        z.1.A1passive) := by
    simpa [Case2PassiveTheta.A1passive] using continuous_fst.comp hpassive
  have hF2 :
      Continuous (fun z :
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J ↦
        z.1.F2) := by
    simpa [Case2PassiveTheta.F2] using continuous_fst.comp hpassiveTail
  have hA3 :
      Continuous (fun z :
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J ↦
        z.1.A3passive) := by
    simpa [Case2PassiveTheta.A3passive] using
      continuous_fst.comp hpassiveTailTail
  have hCtop :
      Continuous (fun z :
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J ↦
        z.1.Ctop) := by
    simpa [Case2PassiveTheta.Ctop] using continuous_fst.comp hCtopF3
  have hF3 :
      Continuous (fun z :
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J ↦
        z.1.F3) := by
    simpa [Case2PassiveTheta.F3] using continuous_snd.comp hCtopF3
  have hy :
      Continuous (fun z :
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J ↦
        z.1.yNext) := by
    simpa [Case2PassiveTheta.yNext] using continuous_snd.comp htheta
  have hC :
      Continuous (fun z :
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J ↦
        (raw z).C) := by
    refine continuous_pi ?_
    intro p
    by_cases hp : p = 0
    · subst p
      simpa [raw, endpointTopologyTupleActiveWritebackRawData,
        case2PostPivotTwoEdgeDomain] using
        (continuous_snd :
          Continuous (fun z :
            Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J ↦ z.2))
    · have hp1 : p = 1 := Fin.eq_one_of_ne_zero p hp
      subst p
      refine continuous_pi ?_
      intro i
      refine continuous_pi ?_
      intro j
      let c :
          AoyagiResidualBlockCoordinateIndex
            (Case2ResidualRowIndex n S (J + 1))
            (Case2ResidualColIndex n S (J + 1)) := ⟨i, j⟩
      have hcoord :
          Continuous (fun z :
              Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J ↦
            z.1.yNext (residualCoordEquiv c)) :=
        (continuous_apply (residualCoordEquiv c)).comp hy
      simpa [raw, endpointTopologyTupleActiveWritebackRawData,
        AoyagiResidualBlockCoordinateIndex.matrix, c] using hcoord
  have hraw : Continuous raw := by
    apply continuous_induced_rng.2
    change Continuous (fun z :
        Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J ↦
      ((raw z).A1passive, ((raw z).F2, ((raw z).A3passive,
        ((raw z).C, ((raw z).Ctop, (raw z).F3))))))
    exact hA1.prodMk (hF2.prodMk (hA3.prodMk (hC.prodMk (hCtop.prodMk hF3))))
  simpa [endpointTopologyTupleActiveWriteback, raw] using
    (continuous_topologyTuple
      (K := ℝ) (ρ := ρ) (κ' := κ')).comp
      ((continuous_endpointTransport
        (K := ℝ) (ρ := ρ)
        (κ := case2PostPivotTwoEdgeDomain n S J τ) (κ' := κ') e).comp hraw)

set_option linter.style.longLine false in
/-- The endpoint topology tuple of an enlarged passive-theta coordinate reads
back to the active selected-entry source chart: passive coordinates are
unchanged, the active `C 1` coordinates are `chartMap pivotNext z.1.yNext`,
and the active `C 0` coordinates are the supplied following factor `z.2`.

This is a pointwise finite-coordinate bridge.  It does not identify endpoint
image measure with Haar measure and does not assert any raw-map pushforward. -/
theorem endpointTopologyTupleActiveReadout_endpointTopologyTuple_eq_activeSelectedEntryChart
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (z : Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q) :
    endpointTopologyTupleActiveReadout n e
        (case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext z eNext e) =
      ((z.1.1,
        SelectedEntrySignedBox.CenterCoord.chartMap
          (case2PassiveThetaPivotNext n hS hnext) z.1.yNext), z.2) := by
  let pivotNext := case2PassiveThetaPivotNext n hS hnext
  let residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
          (Case2ResidualRowIndex n S (J + 1))
          (Case2ResidualColIndex n S (J + 1)) ≃
        Case2PassiveTheta.Center n S J :=
    case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
      n S (J + 1) (Equiv.refl _) (Equiv.refl _)
  let rawData :=
    case2PassiveThetaWithFollowingFactorRetainedData
      (ρ := ρ) n hS hcont hnext z eNext
  have hdata :
      (ofTopologyTuple
        (K := ℝ) (ρ := ρ) (κ' := κ')
        (case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext z eNext e)).endpointTransport
          (fun q ↦ (e q).symm) =
        rawData := by
    simp [rawData, case2PassiveThetaWithFollowingFactorEndpointTopologyTuple,
      case2PassiveThetaWithFollowingFactorEndpointRetainedData]
  have hy :
      (fun i : Case2PassiveTheta.Center n S J ↦
        AoyagiResidualBlockCoordinateIndex.value
          (show
            Matrix (Case2ResidualRowIndex n S (J + 1))
              (Case2ResidualColIndex n S (J + 1)) ℝ from
            by
              simpa [case2PostPivotTwoEdgeDomain] using rawData.C (1 : Fin 2))
          (residualCoordEquiv.symm i)) =
        SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext := by
    funext i
    let D :
        Matrix (Case2ResidualRowIndex n S (J + 1))
          (Case2ResidualColIndex n S (J + 1)) ℝ :=
      show
        Matrix (Case2ResidualRowIndex n S (J + 1))
          (Case2ResidualColIndex n S (J + 1)) ℝ from
        by
          simpa [rawData, case2PostPivotTwoEdgeDomain] using
            (case2PassiveThetaWithFollowingFactorRetainedData
              (ρ := ρ) n hS hcont hnext z eNext).C (1 : Fin 2)
    have hC1 :
        D =
          (case2SuccessorSelectedEntryMatrix n hS hnext z.1.yNext eNext).submatrix
            id eNext.symm := by
      change
        case2DisplayedPostPivotResidualBlock n hS hcont
            (case2SuccessorSelectedEntrySourceResidual n hS hnext z.1.yNext eNext) =
          (case2SuccessorSelectedEntryMatrix n hS hnext z.1.yNext eNext).submatrix
            id eNext.symm
      simp [case2SuccessorSelectedEntrySourceResidual,
        case2DisplayedPostPivotSourceResidualOfMatrix,
        case2DisplayedPostPivotResidualBlock_sourceResidualBlockExtension]
    let c :
        AoyagiResidualBlockCoordinateIndex
            (Case2ResidualRowIndex n S (J + 1))
            (Case2ResidualColIndex n S (J + 1)) :=
      residualCoordEquiv.symm i
    have hcoord :
        case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
            n S (J + 1) (Equiv.refl (Case2ResidualRowIndex n S (J + 1))) eNext
            (c.1, eNext.symm c.2) = i := by
      apply Subtype.ext
      change (c.1.1, (eNext (eNext.symm c.2)).1) = i.1
      rw [Equiv.apply_symm_apply]
      exact congrArg Subtype.val (Equiv.apply_symm_apply residualCoordEquiv i)
    change AoyagiResidualBlockCoordinateIndex.value D (residualCoordEquiv.symm i) =
      SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext i
    rw [hC1]
    change
      case2SuccessorSelectedEntryMatrix n hS hnext z.1.yNext eNext
          (residualCoordEquiv.symm i).1 (eNext.symm (residualCoordEquiv.symm i).2) =
        SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext i
    change
      SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext
          (case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
            n S (J + 1) (Equiv.refl (Case2ResidualRowIndex n S (J + 1))) eNext
            (c.1, eNext.symm c.2)) =
        SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext i
    rw [hcoord]
  have hF :
      (show Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ from
        by
          simpa [rawData, case2PostPivotTwoEdgeDomain] using rawData.C (0 : Fin 2)) =
        z.2 := by
    change
      case2DisplayedPostPivotFreeFollowingFactor n hS hcont
          (case2DisplayedPostPivotFreeCprimeOfFollowingFactor n hS hcont z.2) =
        z.2
    exact
      case2DisplayedPostPivotFreeFollowingFactor_freeCprimeOfFollowingFactor
        n hS hcont z.2
  change
    Case2PassiveThetaWithFollowingFactor.mk
        (ρ := ρ) (τ := τ) (n := n) (S := S) (J := J)
        ((ofTopologyTuple
          (K := ℝ) (ρ := ρ) (κ' := κ')
          (case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
            (ρ := ρ) n hS hcont hnext z eNext e)).endpointTransport
            (fun q ↦ (e q).symm)).A1passive
        ((ofTopologyTuple
          (K := ℝ) (ρ := ρ) (κ' := κ')
          (case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
            (ρ := ρ) n hS hcont hnext z eNext e)).endpointTransport
            (fun q ↦ (e q).symm)).F2
        ((ofTopologyTuple
          (K := ℝ) (ρ := ρ) (κ' := κ')
          (case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
            (ρ := ρ) n hS hcont hnext z eNext e)).endpointTransport
            (fun q ↦ (e q).symm)).A3passive
        ((ofTopologyTuple
          (K := ℝ) (ρ := ρ) (κ' := κ')
          (case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
            (ρ := ρ) n hS hcont hnext z eNext e)).endpointTransport
            (fun q ↦ (e q).symm)).Ctop
        ((ofTopologyTuple
          (K := ℝ) (ρ := ρ) (κ' := κ')
          (case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
            (ρ := ρ) n hS hcont hnext z eNext e)).endpointTransport
            (fun q ↦ (e q).symm)).F3
        (fun i : Case2PassiveTheta.Center n S J ↦
          AoyagiResidualBlockCoordinateIndex.value
            (show
              Matrix (Case2ResidualRowIndex n S (J + 1))
                (Case2ResidualColIndex n S (J + 1)) ℝ from
              by
                simpa [case2PostPivotTwoEdgeDomain] using
                  ((ofTopologyTuple
                    (K := ℝ) (ρ := ρ) (κ' := κ')
                    (case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
                      (ρ := ρ) n hS hcont hnext z eNext e)).endpointTransport
                      (fun q ↦ (e q).symm)).C (1 : Fin 2))
            (residualCoordEquiv.symm i))
        (show Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ from
          by
            simpa [case2PostPivotTwoEdgeDomain] using
              ((ofTopologyTuple
                (K := ℝ) (ρ := ρ) (κ' := κ')
                (case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
                  (ρ := ρ) n hS hcont hnext z eNext e)).endpointTransport
                  (fun q ↦ (e q).symm)).C (0 : Fin 2)) =
      ((z.1.1,
        SelectedEntrySignedBox.CenterCoord.chartMap
          (case2PassiveThetaPivotNext n hS hnext) z.1.yNext), z.2)
  rw [hdata, hy]
  cases z with
  | mk theta F =>
    cases theta
    apply Prod.ext
    · rfl
    · simpa [rawData, case2PassiveThetaWithFollowingFactorRetainedData,
        case2PostPivotSelectedEntryRetainedPassiveDataWithPassiveFollowingFactor,
        Case2PassiveThetaWithFollowingFactor.mk] using hF

set_option linter.style.longLine false in
/-- The enlarged Case 2 endpoint topology tuple is exactly the active
writeback of the selected-entry active chart.

This packages the endpoint map as a linear finite-coordinate repacking after
the nonlinear selected-entry source chart.  It is a pointwise factorization,
not a determinant-Haar or raw-map pushforward theorem. -/
theorem case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_eq_activeWriteback_activeSelectedEntryChart
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (z : Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q) :
    let pivotNext := case2PassiveThetaPivotNext n hS hnext
    let activeChart :
        Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J :=
      fun z ↦
        ((z.1.1, SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext), z.2)
    let Y :
        Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
          TopologyTuple ρ κ' ℝ :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext z eNext e
    Y z = endpointTopologyTupleActiveWriteback n e (activeChart z) := by
  intro pivotNext activeChart Y
  calc
    Y z =
        endpointTopologyTupleActiveWriteback n e
          (endpointTopologyTupleActiveReadout n e (Y z)) := by
      exact
        (endpointTopologyTupleActiveWriteback_readout
          (ρ := ρ) (τ := τ) n e (Y z)).symm
    _ = endpointTopologyTupleActiveWriteback n e (activeChart z) := by
      rw [show endpointTopologyTupleActiveReadout n e (Y z) = activeChart z by
        simpa [Y, activeChart, pivotNext] using
          endpointTopologyTupleActiveReadout_endpointTopologyTuple_eq_activeSelectedEntryChart
            (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext z eNext e]

set_option linter.style.longLine false in
/-- The enlarged Case 2 endpoint topology-tuple map is injective on the locus
where the successor selected-entry pivot coordinate is nonzero.

The proof is pointwise: active readout recovers the passive fields, the
selected-entry chart image of the successor center coordinates, and the
following factor.  The selected-entry chart is injective away from the pivot
hyperplane.  No measure transport or Jacobian statement is proved here. -/
theorem case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_injOn_pivotNonzero
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q) :
    Set.InjOn
      (fun z : Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J =>
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext z eNext e)
      {z | case2PassiveThetaPivotNonzero (ρ := ρ) (τ := τ) n hS hnext z.1} := by
  intro z hz w hw hY
  let pivotNext := case2PassiveThetaPivotNext n hS hnext
  let Y :
      Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
        TopologyTuple ρ κ' ℝ :=
    fun u ↦
      case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
        (ρ := ρ) n hS hcont hnext u eNext e
  have hread :
      ((z.1.1, SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext), z.2) =
        ((w.1.1, SelectedEntrySignedBox.CenterCoord.chartMap pivotNext w.1.yNext), w.2) := by
    calc
      ((z.1.1, SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext), z.2) =
          endpointTopologyTupleActiveReadout n e (Y z) := by
        rw [endpointTopologyTupleActiveReadout_endpointTopologyTuple_eq_activeSelectedEntryChart]
      _ = endpointTopologyTupleActiveReadout n e (Y w) := by
        exact congrArg (endpointTopologyTupleActiveReadout n e) hY
      _ = ((w.1.1, SelectedEntrySignedBox.CenterCoord.chartMap pivotNext w.1.yNext), w.2) := by
        rw [endpointTopologyTupleActiveReadout_endpointTopologyTuple_eq_activeSelectedEntryChart]
  have hpassive : z.1.1 = w.1.1 :=
    congrArg (fun q ↦ q.1.1) hread
  have hchart :
      SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext =
        SelectedEntrySignedBox.CenterCoord.chartMap pivotNext w.1.yNext :=
    congrArg (fun q ↦ q.1.2) hread
  have hfollowing : z.2 = w.2 :=
    congrArg (fun q ↦ q.2) hread
  have hzPivot : z.1.yNext ∈ {y : Case2PassiveTheta.Center n S J → ℝ |
      y pivotNext ≠ 0} := by
    simpa [pivotNext, case2PassiveThetaPivotNonzero] using hz
  have hwPivot : w.1.yNext ∈ {y : Case2PassiveTheta.Center n S J → ℝ |
      y pivotNext ≠ 0} := by
    simpa [pivotNext, case2PassiveThetaPivotNonzero] using hw
  have hyNext : z.1.yNext = w.1.yNext :=
    SelectedEntrySignedBox.CenterCoord.injOn_chartMap_pivot_ne_zero pivotNext
      hzPivot hwPivot hchart
  have htheta : z.1 = w.1 := by
    apply Prod.ext
    · exact hpassive
    · simpa [Case2PassiveTheta.yNext] using hyNext
  exact Prod.ext htheta hfollowing

set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- A measurable source subset contained in the selected-pivot-nonzero locus
has a measurable image under the enlarged Case 2 endpoint topology-tuple map.

This is only the measurable-image consequence of continuity and pivot-nonzero
injectivity.  It does not identify the image measure with Haar measure and does
not prove a Jacobian change-of-variables formula. -/
theorem measurableSet_case2PassiveThetaWithFollowingFactorEndpointSectorSet_of_subset_pivotNonzero
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ}
    [MeasurableSpace
      (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [OpensMeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [T2Space (TopologyTuple ρ κ' ℝ)]
    (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (Ω :
      Set (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J))
    (hΩ : MeasurableSet Ω)
    (hΩpivot :
      Ω ⊆ {z |
        case2PassiveThetaPivotNonzero (ρ := ρ) (τ := τ) n hS hnext z.1}) :
    MeasurableSet
      (case2PassiveThetaWithFollowingFactorEndpointSectorSet
        (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e Ω) := by
  let Y :
      Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
        TopologyTuple ρ κ' ℝ :=
    fun z ↦
      case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
        (ρ := ρ) n hS hcont hnext z eNext e
  have hYglobal : Continuous Y := by
    simpa [Y] using
      continuous_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
        (ρ := ρ) n hS hcont hnext eNext e
  have hYcont : ContinuousOn Y Ω := hYglobal.continuousOn
  have hYinj_pivot :
      Set.InjOn Y
        {z : Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J |
          case2PassiveThetaPivotNonzero (ρ := ρ) (τ := τ) n hS hnext z.1} := by
    simpa [Y] using
      case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_injOn_pivotNonzero
        (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e
  have hYinj : Set.InjOn Y Ω := by
    intro z hz w hw hYeq
    exact hYinj_pivot (hΩpivot hz) (hΩpivot hw) hYeq
  have himage : MeasurableSet (Y '' Ω) :=
    hΩ.image_of_continuousOn_injOn hYcont hYinj
  simpa [Y, case2PassiveThetaWithFollowingFactorEndpointSectorSet] using himage

set_option linter.style.longLine false in
/-- The active endpoint readout sends the actual enlarged endpoint image of a
source set to the active selected-entry source-chart image of the same source
set.

This is only an image-level finite-coordinate statement.  It does not compare
the endpoint image measure to determinant Haar and does not assert any raw-map
pushforward. -/
theorem endpointTopologyTupleActiveReadout_image_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_image_eq_activeSelectedEntryChart_image
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (Ω : Set (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)) :
    let pivotNext := case2PassiveThetaPivotNext n hS hnext
    let Y :
        Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
          TopologyTuple ρ κ' ℝ :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext z eNext e
    let activeReadout :
        TopologyTuple ρ κ' ℝ →
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J :=
      endpointTopologyTupleActiveReadout n e
    let activeChart :
        Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J :=
      fun z ↦ ((z.1.1, SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext), z.2)
    activeReadout '' (Y '' Ω) = activeChart '' Ω := by
  intro pivotNext Y activeReadout activeChart
  ext x
  constructor
  · rintro ⟨T, ⟨z, hzΩ, rfl⟩, rfl⟩
    refine ⟨z, hzΩ, ?_⟩
    simpa [activeReadout, activeChart, Y, pivotNext] using
      (endpointTopologyTupleActiveReadout_endpointTopologyTuple_eq_activeSelectedEntryChart
        (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext z eNext e
      ).symm
  · rintro ⟨z, hzΩ, rfl⟩
    refine ⟨Y z, ⟨z, hzΩ, rfl⟩, ?_⟩
    simpa [activeReadout, activeChart, Y, pivotNext] using
      endpointTopologyTupleActiveReadout_endpointTopologyTuple_eq_activeSelectedEntryChart
        (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext z eNext e

set_option linter.style.longLine false in
/-- On the actual enlarged endpoint image of any source set contained in the
nonzero-pivot locus, the active endpoint readout is injective.

This is the local-image form of the elementary Case 2 selected-entry
calculation: the active readout recovers passive fields, selected-entry
charted center coordinates, and the following factor; the selected-entry chart
is injective away from the pivot hyperplane.  No determinant-Haar transport or
raw-map pushforward is proved here. -/
theorem endpointTopologyTupleActiveReadout_injOn_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_image_of_subset_pivotNonzero
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (Ω : Set (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J))
    (hΩpivot :
      Ω ⊆ {z |
        case2PassiveThetaPivotNonzero (ρ := ρ) (τ := τ) n hS hnext z.1}) :
    let Y :
        Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
          TopologyTuple ρ κ' ℝ :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext z eNext e
    let activeReadout :
        TopologyTuple ρ κ' ℝ →
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J :=
      endpointTopologyTupleActiveReadout n e
    Set.InjOn activeReadout (Y '' Ω) := by
  intro Y activeReadout T hT T' hT' hread
  rcases hT with ⟨z, hzΩ, rfl⟩
  rcases hT' with ⟨w, hwΩ, rfl⟩
  let pivotNext := case2PassiveThetaPivotNext n hS hnext
  have hactive :
      ((z.1.1, SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext), z.2) =
        ((w.1.1, SelectedEntrySignedBox.CenterCoord.chartMap pivotNext w.1.yNext), w.2) := by
    calc
      ((z.1.1, SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext), z.2) =
          activeReadout (Y z) := by
            simpa [activeReadout, Y, pivotNext] using
              (endpointTopologyTupleActiveReadout_endpointTopologyTuple_eq_activeSelectedEntryChart
                (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext z eNext e).symm
      _ = activeReadout (Y w) := hread
      _ = ((w.1.1, SelectedEntrySignedBox.CenterCoord.chartMap pivotNext w.1.yNext), w.2) := by
            simpa [activeReadout, Y, pivotNext] using
              endpointTopologyTupleActiveReadout_endpointTopologyTuple_eq_activeSelectedEntryChart
                (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext w eNext e
  have hpassive : z.1.1 = w.1.1 :=
    congrArg (fun q ↦ q.1.1) hactive
  have hchart :
      SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext =
        SelectedEntrySignedBox.CenterCoord.chartMap pivotNext w.1.yNext :=
    congrArg (fun q ↦ q.1.2) hactive
  have hfollowing : z.2 = w.2 :=
    congrArg (fun q ↦ q.2) hactive
  have hzPivot : z.1.yNext ∈ {y : Case2PassiveTheta.Center n S J → ℝ |
      y pivotNext ≠ 0} := by
    simpa [pivotNext, case2PassiveThetaPivotNonzero] using hΩpivot hzΩ
  have hwPivot : w.1.yNext ∈ {y : Case2PassiveTheta.Center n S J → ℝ |
      y pivotNext ≠ 0} := by
    simpa [pivotNext, case2PassiveThetaPivotNonzero] using hΩpivot hwΩ
  have hyNext : z.1.yNext = w.1.yNext :=
    SelectedEntrySignedBox.CenterCoord.injOn_chartMap_pivot_ne_zero pivotNext
      hzPivot hwPivot hchart
  have htheta : z.1 = w.1 := by
    apply Prod.ext
    · exact hpassive
    · simpa [Case2PassiveTheta.yNext] using hyNext
  have hzw : z = w := Prod.ext htheta hfollowing
  exact congrArg Y hzw

end Case2PassiveThetaWithFollowingFactor

end Aoyagi
end DLN
end DLNFibre
