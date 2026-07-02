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

end Case2PassiveThetaWithFollowingFactor

end Aoyagi
end DLN
end DLNFibre
