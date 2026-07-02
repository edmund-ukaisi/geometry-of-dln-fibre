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

end Aoyagi
end DLN
end DLNFibre
