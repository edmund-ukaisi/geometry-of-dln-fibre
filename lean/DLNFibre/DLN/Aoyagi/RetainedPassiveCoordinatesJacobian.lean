import DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative
import DLNFibre.DLN.Aoyagi.RetainedPassiveFormalRawOrder

/-!
# Retained-passive raw-order Jacobian bridge scaffold

This file is a leaf bridge between the analytic retained-passive raw-order
derivative API and the formal retained-passive raw-order determinant core.

The formal map below is the determinant-bearing raw-order formal Jacobian
specialized at a retained-passive tuple.  It is not asserted to be the Frechet
derivative of `topologyTupleEdgeRawOrder`; the missing comparison is a future
triangular/shear factorization.
-/

noncomputable section

namespace DLNFibre
namespace DLN
namespace Aoyagi

open ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData

/-- The determinant-bearing retained-passive formal raw-order Jacobian
specialized at a tuple point.

The parameters are read from the retained-passive coordinate reconstruction:
the first top block uses the passive `A1` tail, the edge-local blocks use the
solved `A1`, shifted `F2`, and solved `A3` families, and the terminal right
factor is the final solved `A1` block. -/
abbrev retainedPassiveFormalRawOrderJacobianAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    RetainedPassiveRawTopologyTuple ρ κ' ℝ →ₗ[ℝ]
      RetainedPassiveRawTopologyTuple ρ κ' ℝ :=
  let data :
      ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
        (K := ℝ) (ρ := ρ) κ' :=
    ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.ofTopologyTuple
      (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord :
      ChartLocalSuffixState.RetainedPassiveCoordinateData
        (K := ℝ) (ρ := ρ) κ' :=
    data.toCoordinateData
  retainedPassiveFormalRawOrderJacobian
    (ρ := ρ) (κ' := κ') (K := ℝ)
    (ChartLocalSuffixState.retainedPassiveA1TailAfterFirst
      (K := ℝ) (ρ := ρ) data.A1seed)
    (fun p : Fin (M + 1) => coord.solvedA1 p)
    (fun p : Fin (M + 1) => coord.F2 p.succ)
    (fun p : Fin (M + 1) => coord.solvedA3 p)
    (coord.solvedA1 (Fin.last M))

/-- The determinant formula for the point-specialized formal raw-order
Jacobian. -/
theorem retainedPassiveFormalRawOrderJacobianAt_det_eq
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    let data :
        ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
          (K := ℝ) (ρ := ρ) κ' :=
      ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.ofTopologyTuple
        (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord :
        ChartLocalSuffixState.RetainedPassiveCoordinateData
          (K := ℝ) (ρ := ρ) κ' :=
      data.toCoordinateData
    LinearMap.det
        (retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) =
      ((ChartLocalSuffixState.retainedPassiveA1TailAfterFirst
          (K := ℝ) (ρ := ρ) data.A1seed)⁻¹).det ^ Fintype.card ρ *
        (∏ p : Fin (M + 1),
          (-(coord.solvedA1 p)).det ^ Fintype.card (κ' p.castSucc)) *
          (-(coord.solvedA1 (Fin.last M))).det ^
            Fintype.card (κ' (Fin.last (M + 1))) := by
  dsimp [retainedPassiveFormalRawOrderJacobianAt]
  rw [retainedPassiveFormalRawOrderJacobian_det_eq]

/-- The point-specialized formal raw-order determinant is a unit on the
retained-passive determinant chart. -/
theorem retainedPassiveFormalRawOrderJacobianAt_det_isUnit_of_mem_topologyTupleDetChartSet
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈
      ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.topologyTupleDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')) :
    IsUnit
      (LinearMap.det
        (retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z)) := by
  simpa [retainedPassiveFormalRawOrderJacobianAt] using
    retainedPassiveFormalRawOrderJacobian_det_isUnit_of_mem_topologyTupleDetChartSet
      (M := M) (ρ := ρ) (κ' := κ') (K := ℝ) z hz

/-- The absolute determinant of the point-specialized formal raw-order
Jacobian. -/
def retainedPassiveFormalRawOrderJacobianAbsDetAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) : ℝ :=
  |LinearMap.det
    (retainedPassiveFormalRawOrderJacobianAt
      (ρ := ρ) (κ' := κ') z)|

/-- The point-specialized formal raw-order absolute determinant is positive on
the retained-passive determinant chart. -/
theorem retainedPassiveFormalRawOrderJacobianAbsDetAt_pos_of_mem_topologyTupleDetChartSet
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈
      ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.topologyTupleDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')) :
    0 < retainedPassiveFormalRawOrderJacobianAbsDetAt
      (ρ := ρ) (κ' := κ') z := by
  have hunit :=
    retainedPassiveFormalRawOrderJacobianAt_det_isUnit_of_mem_topologyTupleDetChartSet
      (ρ := ρ) (κ' := κ') hz
  rw [retainedPassiveFormalRawOrderJacobianAbsDetAt]
  exact abs_pos.mpr (isUnit_iff_ne_zero.mp hunit)

/-- On the retained-passive determinant chart, both the analytic raw-order
Frechet derivative determinant and the point-specialized formal raw-order
determinant are units.

This is a side-by-side bridge scaffold.  It is not an equality between the two
determinants. -/
theorem topologyTupleEdgeRawOrder_fderiv_det_and_formal_det_isUnit_of_mem_topologyTupleDetChartSet
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    IsUnit
        (LinearMap.det
          ((fderiv ℝ
            (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')) z :
              RetainedPassiveRawTopologyTuple ρ κ' ℝ →L[ℝ]
                RetainedPassiveRawTopologyTuple ρ κ' ℝ) :
            RetainedPassiveRawTopologyTuple ρ κ' ℝ →ₗ[ℝ]
              RetainedPassiveRawTopologyTuple ρ κ' ℝ)) ∧
      IsUnit
        (LinearMap.det
          (retainedPassiveFormalRawOrderJacobianAt
            (ρ := ρ) (κ' := κ') z)) := by
  exact
    ⟨fderiv_topologyTupleEdgeRawOrder_det_isUnit_of_mem_topologyTupleDetChartSet
          (ρ := ρ) (κ' := κ') hz,
      retainedPassiveFormalRawOrderJacobianAt_det_isUnit_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') hz⟩

end Aoyagi
end DLN
end DLNFibre
