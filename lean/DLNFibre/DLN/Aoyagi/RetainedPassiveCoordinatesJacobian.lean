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

open scoped Matrix.Norms.Operator

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

/-- The point-specialized formal edge-pair equivalence on separated raw-order
`(F2,C)` families. -/
def retainedPassiveFormalRawF2CLinearEquivAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    ((∀ p : Fin (M + 1), Matrix ρ (κ' p.castSucc) ℝ) ×
        (∀ p : Fin (M + 1), Matrix (κ' p.succ) (κ' p.castSucc) ℝ)) ≃ₗ[ℝ]
      ((∀ p : Fin (M + 1), Matrix ρ (κ' p.castSucc) ℝ) ×
        (∀ p : Fin (M + 1), Matrix (κ' p.succ) (κ' p.castSucc) ℝ)) :=
  let data :
      ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
        (K := ℝ) (ρ := ρ) κ' :=
    ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.ofTopologyTuple
      (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord :
      ChartLocalSuffixState.RetainedPassiveCoordinateData
        (K := ℝ) (ρ := ρ) κ' :=
    data.toCoordinateData
  let hA : ∀ p : Fin (M + 1), IsUnit (coord.solvedA1 p).det := by
    intro p
    have hdet : data.detChart := hz
    simpa [coord, data] using
      solvedA1_det_isUnit_of_detChart
        (K := ℝ) (ρ := ρ) data hdet p
  retainedPassiveFormalRawF2CLinearEquiv
    (ρ := ρ) (κ' := κ') (K := ℝ)
    (fun p : Fin (M + 1) => coord.solvedA1 p)
    (fun p : Fin (M + 1) => coord.F2 p.succ)
    (fun p : Fin (M + 1) => coord.solvedA3 p)
    hA

/-- The point-specialized formal edge-pair equivalence sends the source
`(F2,C)` families to the `(F2,C)` families of the formal raw-order output. -/
theorem retainedPassiveFormalRawF2CLinearEquivAt_apply_sourcePair
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    retainedPassiveFormalRawF2CLinearEquivAt (ρ := ρ) (κ' := κ') hz
        (v.2.1, v.2.2.2.1) =
      (((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.1,
        ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.1) := by
  dsimp [retainedPassiveFormalRawF2CLinearEquivAt,
    retainedPassiveFormalRawOrderJacobianAt]
  rw [retainedPassiveFormalRawF2CLinearEquiv_apply]
  rw [retainedPassiveFormalRawOrderJacobian_apply]

/-- Inverse formula for the point-specialized formal edge-pair equivalence. -/
theorem retainedPassiveFormalRawF2CLinearEquivAt_symm_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (u :
      (∀ p : Fin (M + 1), Matrix ρ (κ' p.castSucc) ℝ) ×
        (∀ p : Fin (M + 1), Matrix (κ' p.succ) (κ' p.castSucc) ℝ)) :
    let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
    (retainedPassiveFormalRawF2CLinearEquivAt (ρ := ρ) (κ' := κ') hz).symm u =
      (fun p : Fin (M + 1) =>
          (coord.solvedA1 p)⁻¹ * (coord.F2 p.succ * u.2 p - u.1 p),
        fun p : Fin (M + 1) =>
          u.2 p + coord.solvedA3 p *
            ((coord.solvedA1 p)⁻¹ * (coord.F2 p.succ * u.2 p - u.1 p))) := by
  dsimp [retainedPassiveFormalRawF2CLinearEquivAt]
  rw [retainedPassiveFormalRawF2CLinearEquiv_symm_apply]

/-- The inverse point-specialized edge-pair equivalence recovers the source
`(F2,C)` families from the formal raw-order output. -/
theorem retainedPassiveFormalRawF2CLinearEquivAt_symm_recovers_sourcePair
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    (retainedPassiveFormalRawF2CLinearEquivAt (ρ := ρ) (κ' := κ') hz).symm
        (((retainedPassiveFormalRawOrderJacobianAt
            (ρ := ρ) (κ' := κ') z) v).2.1,
          ((retainedPassiveFormalRawOrderJacobianAt
            (ρ := ρ) (κ' := κ') z) v).2.2.2.1) =
      (v.2.1, v.2.2.2.1) := by
  have h :=
    retainedPassiveFormalRawF2CLinearEquivAt_apply_sourcePair
      (ρ := ρ) (κ' := κ') hz v
  rw [← h]
  exact
    (retainedPassiveFormalRawF2CLinearEquivAt
      (ρ := ρ) (κ' := κ') hz).left_inv (v.2.1, v.2.2.2.1)

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

/-- Absolute-value product formula for the point-specialized formal raw-order
Jacobian.

This is a formal determinant formula only.  It does not identify this formal
absolute determinant with `topologyTupleEdgeRawOrderFDerivAbsDet`. -/
theorem retainedPassiveFormalRawOrderJacobianAbsDetAt_eq
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
    retainedPassiveFormalRawOrderJacobianAbsDetAt
        (ρ := ρ) (κ' := κ') z =
      |((ChartLocalSuffixState.retainedPassiveA1TailAfterFirst
          (K := ℝ) (ρ := ρ) data.A1seed)⁻¹).det| ^ Fintype.card ρ *
        (∏ p : Fin (M + 1),
          |(coord.solvedA1 p).det| ^ Fintype.card (κ' p.castSucc)) *
          |(coord.solvedA1 (Fin.last M)).det| ^
            Fintype.card (κ' (Fin.last (M + 1))) := by
  dsimp [retainedPassiveFormalRawOrderJacobianAbsDetAt,
    retainedPassiveFormalRawOrderJacobianAt]
  rw [retainedPassiveFormalRawOrderJacobian_abs_det_eq]

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

/-- The passive lower-left component of the actual raw-order Frechet
derivative agrees with the point-specialized formal raw-order map. -/
theorem rawEdgeTupleA3_fderiv_topologyTupleEdgeRawOrder_castSucc_eq_formalRawOrderJacobianAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) (p : Fin M) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ')
        ((fderiv ℝ raw z) v) p.castSucc =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.1 p := by
  change rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ')
        ((fderiv ℝ
          (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')) z) v)
        p.castSucc =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.1 p
  rw [rawEdgeTupleA3_castSucc]
  change ((fderiv ℝ
          (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')) z) v).2.2.1 p =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.1 p
  rw [fderiv_topologyTupleEdgeRawOrder_A3passive_apply
    (ρ := ρ) (κ' := κ') hz v p]
  dsimp [retainedPassiveFormalRawOrderJacobianAt]
  rw [retainedPassiveFormalRawOrderJacobian_apply]

/-- After the lower-left target shear, the `C` component of the actual
raw-order Frechet derivative agrees with the point-specialized formal
raw-order map. -/
theorem C_unshear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) (p : Fin (M + 1)) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
    ((fderiv ℝ raw z) v).2.2.2.1 p
      + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') ((fderiv ℝ raw z) v) p *
        coord.F2 p.castSucc =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.1 p := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
  have hC :=
    fderiv_topologyTupleEdgeRawOrder_C_unshear_apply
      (ρ := ρ) (κ' := κ') hz v p
  change ((fderiv ℝ raw z) v).2.2.2.1 p
      + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') ((fderiv ℝ raw z) v) p *
        coord.F2 p.castSucc =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.1 p
  rw [hC]
  dsimp [retainedPassiveFormalRawOrderJacobianAt]
  rw [retainedPassiveFormalRawOrderJacobian_apply]
  simpa [coord, sub_eq_add_neg, neg_mul] using
    (add_comm (v.2.2.2.1 p) (-(coord.solvedA3 p * v.2.1 p)))

/-- After the top-left and successor-`F2` shear corrections, the `F2`
component of the actual raw-order Frechet derivative agrees with the
point-specialized formal raw-order map. -/
theorem F2_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) (p : Fin (M + 1)) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
    ((fderiv ℝ raw z) v).2.1 p
      + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') ((fderiv ℝ raw z) v) p *
        coord.F2 p.castSucc
      - (fderiv ℝ
          (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
              p.succ) z) v *
        coord.C p =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.1 p := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
  have hF2 :=
    fderiv_topologyTupleEdgeRawOrder_F2_shear_apply
      (ρ := ρ) (κ' := κ') hz v p
  change ((fderiv ℝ raw z) v).2.1 p
      + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') ((fderiv ℝ raw z) v) p *
        coord.F2 p.castSucc
      - (fderiv ℝ
          (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
              p.succ) z) v *
        coord.C p =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.1 p
  rw [hF2]
  dsimp [retainedPassiveFormalRawOrderJacobianAt]
  rw [retainedPassiveFormalRawOrderJacobian_apply]

/-- The terminal extended `F2` coordinate is the constant zero map, so its
Frechet derivative vanishes. -/
theorem fderiv_retainedPassive_toCoordinateData_F2_last_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    (z v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    (fderiv ℝ
      (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
          (Fin.last (M + 1))) z) v = 0 := by
  have hfun :
      (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
          (Fin.last (M + 1))) =
        fun _ : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
          (0 : Matrix ρ (κ' (Fin.last (M + 1))) ℝ) := by
    funext y
    simp [ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.toCoordinateData]
  rw [hfun]
  simp

set_option linter.style.longLine false in
/-- At a nonterminal edge, the extended successor `F2` coordinate is the
stored source `F2` coordinate at the successor retained edge, up to the
dependent-index cast. -/
theorem fderiv_retainedPassive_toCoordinateData_F2_nonterminal_succ_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Finite ρ] [∀ j, Finite (κ' j)]
    (z v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) (p : Fin M) :
    (fderiv ℝ
      (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
          p.castSucc.succ) z) v =
      (LinearEquiv.cast (R := ℝ)
        (M := fun i : Fin (M + 2) ↦ Matrix ρ (κ' i) ℝ)
        (Fin.succ_castSucc p).symm) (v.2.1 p.succ) := by
  let h : p.castSucc.succ = p.succ.castSucc := Fin.succ_castSucc p
  let e : Matrix ρ (κ' p.succ.castSucc) ℝ ≃ₗ[ℝ]
      Matrix ρ (κ' p.castSucc.succ) ℝ :=
    LinearEquiv.cast (R := ℝ)
      (M := fun i : Fin (M + 2) ↦ Matrix ρ (κ' i) ℝ) h.symm
  have hfun :
      (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
          p.castSucc.succ) =
        fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦ e (y.2.1 p.succ) := by
    funext y
    have hsnoc :
        (@Fin.snoc (n := M + 1)
          (α := fun i : Fin (M + 2) ↦ Matrix ρ (κ' i) ℝ)
          (fun r : Fin (M + 1) ↦ y.2.1 r)
          (0 : Matrix ρ (κ' (Fin.last (M + 1))) ℝ)) p.succ.castSucc =
          y.2.1 p.succ :=
      @Fin.snoc_castSucc (n := M + 1)
        (α := fun i : Fin (M + 2) ↦ Matrix ρ (κ' i) ℝ)
        (0 : Matrix ρ (κ' (Fin.last (M + 1))) ℝ)
        (fun r : Fin (M + 1) ↦ y.2.1 r) p.succ
    change (@Fin.snoc (n := M + 1)
          (α := fun i : Fin (M + 2) ↦ Matrix ρ (κ' i) ℝ)
          (fun r : Fin (M + 1) ↦ y.2.1 r)
          (0 : Matrix ρ (κ' (Fin.last (M + 1))) ℝ)) p.castSucc.succ =
        e (y.2.1 p.succ)
    cases h
    simpa [e] using hsnoc
  let LF : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →L[ℝ]
      Matrix ρ (κ' p.succ.castSucc) ℝ :=
    { toLinearMap :=
        { toFun := fun y ↦ y.2.1 p.succ
          map_add' := by
            intro x y
            rfl
          map_smul' := by
            intro a y
            rfl }
      cont := by fun_prop }
  let Le : Matrix ρ (κ' p.succ.castSucc) ℝ →L[ℝ]
      Matrix ρ (κ' p.castSucc.succ) ℝ :=
    LinearMap.toContinuousLinearMap e.toLinearMap
  let L : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →L[ℝ]
      Matrix ρ (κ' p.castSucc.succ) ℝ := Le.comp LF
  rw [hfun]
  have hL :
      fderiv ℝ
          (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
            e (y.2.1 p.succ)) z =
        L := by
    exact L.hasFDerivAt.fderiv
  rw [hL]
  rfl

/-- At the terminal edge, the successor-`F2` derivative term in the actual
`F2` shear vanishes by the retained-passive terminal zero convention. -/
theorem F2_terminal_target_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
    let p : Fin (M + 1) := Fin.last M
    ((fderiv ℝ raw z) v).2.1 p
      + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') ((fderiv ℝ raw z) v) p *
        coord.F2 p.castSucc =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.1 p := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
  let p : Fin (M + 1) := Fin.last M
  have hzero :
      (fderiv ℝ
        (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
            p.succ) z) v = 0 := by
    simpa [p] using
      fderiv_retainedPassive_toCoordinateData_F2_last_apply
        (ρ := ρ) (κ' := κ') z v
  have hF2 :=
    F2_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (ρ := ρ) (κ' := κ') hz v p
  change ((fderiv ℝ raw z) v).2.1 p
      + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') ((fderiv ℝ raw z) v) p *
        coord.F2 p.castSucc
      - (fderiv ℝ
          (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
              p.succ) z) v *
        coord.C p =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.1 p at hF2
  rw [hzero] at hF2
  have hmul : (0 : Matrix ρ (κ' p.succ) ℝ) * coord.C p = 0 := by
    ext i j
    simp [Matrix.mul_apply]
  rw [hmul, sub_zero] at hF2
  exact hF2

/-- After the successor-`F2`/lower-left product corrections, the passive
top-left component of the actual raw-order Frechet derivative agrees with the
point-specialized formal raw-order map. -/
theorem A1passive_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) (p : Fin M) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
    ((fderiv ℝ raw z) v).1 p
      - (fderiv ℝ
          (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
              p.succ.succ) z) v *
          coord.solvedA3 p.succ
      - coord.F2 p.succ.succ *
          (fderiv ℝ
            (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.solvedA3
                p.succ) z) v =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).1 p := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
  have hA1 :=
    fderiv_topologyTupleEdgeRawOrder_A1passive_shear_apply
      (ρ := ρ) (κ' := κ') hz v p
  change ((fderiv ℝ raw z) v).1 p
      - (fderiv ℝ
          (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
              p.succ.succ) z) v *
          coord.solvedA3 p.succ
      - coord.F2 p.succ.succ *
          (fderiv ℝ
            (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.solvedA3
                p.succ) z) v =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).1 p
  rw [hA1]
  dsimp [retainedPassiveFormalRawOrderJacobianAt]
  rw [retainedPassiveFormalRawOrderJacobian_apply]

/-- After the successor-`F2`/lower-left product corrections and the
passive-tail inverse correction, the first top-left `Ctop` component of the
actual raw-order Frechet derivative agrees with the point-specialized formal
raw-order map. -/
theorem Ctop_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    ((fderiv ℝ raw z) v).2.2.2.2.1
      - (fderiv ℝ
          (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
              (0 : Fin (M + 1)).succ) z) v *
          coord.solvedA3 0
      - coord.F2 (0 : Fin (M + 1)).succ *
          (fderiv ℝ
            (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.solvedA3
                0) z) v
      - (fderiv ℝ
          (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
            (ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed)⁻¹) z) v *
          coord.Ctop =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.1 := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  have hCtop :=
    fderiv_topologyTupleEdgeRawOrder_Ctop_shear_apply
      (ρ := ρ) (κ' := κ') hz v
  change ((fderiv ℝ raw z) v).2.2.2.2.1
      - (fderiv ℝ
          (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
              (0 : Fin (M + 1)).succ) z) v *
          coord.solvedA3 0
      - coord.F2 (0 : Fin (M + 1)).succ *
          (fderiv ℝ
            (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.solvedA3
                0) z) v
      - (fderiv ℝ
          (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
            (ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed)⁻¹) z) v *
          coord.Ctop =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.1
  rw [hCtop]
  dsimp [retainedPassiveFormalRawOrderJacobianAt]
  rw [retainedPassiveFormalRawOrderJacobian_apply]

/-- After the terminal lower-left shear, the terminal `F3` component of the
actual raw-order Frechet derivative agrees with the point-specialized formal
raw-order map. -/
theorem F3_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let A1fun : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →
        Fin (M + 1) → Matrix ρ ρ ℝ :=
      fun y p ↦
        ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p
    let Earlyfun : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →
        Matrix (κ' (Fin.last (M + 1))) ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
          (K := ℝ) (ρ := ρ) (κ := κ')
          (A1fun y)
          (ChartLocalSuffixState.retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
          0 (Nat.zero_le (M + 1))
    let Lastfun : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct
          (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          (A1fun y) (Fin.last (M + 1)) (Fin.last M).castSucc
            (Fin.last M).castSucc.le_last
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    ((fderiv ℝ raw z) v).2.2.2.2.2
      - (fderiv ℝ Earlyfun z) v * Lastfun z
      + (coord.F3 - Earlyfun z) * (fderiv ℝ Lastfun z) v =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.2 := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
  have hF3 :=
    fderiv_topologyTupleEdgeRawOrder_F3_shear_apply
      (ρ := ρ) (κ' := κ') hz v
  change ((fderiv ℝ raw z) v).2.2.2.2.2
      - (fderiv ℝ
          (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
            ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
              (K := ℝ) (ρ := ρ) (κ := κ')
              (fun p : Fin (M + 1) ↦
                ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p)
              (ChartLocalSuffixState.retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
                (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed)
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
              0 (Nat.zero_le (M + 1))) z) v *
          (ChartLocalSuffixState.residualFactorProduct
            (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
            (fun p : Fin (M + 1) ↦
              ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
            (Fin.last (M + 1)) (Fin.last M).castSucc
              (Fin.last M).castSucc.le_last)
      + (((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).F3 -
          ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
            (K := ℝ) (ρ := ρ) (κ := κ')
            (fun p : Fin (M + 1) ↦
              ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
            (ChartLocalSuffixState.retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed)
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
            0 (Nat.zero_le (M + 1))) *
          (fderiv ℝ
            (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
              ChartLocalSuffixState.residualFactorProduct
                (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
                (fun p : Fin (M + 1) ↦
                  ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p)
                (Fin.last (M + 1)) (Fin.last M).castSucc
                  (Fin.last M).castSucc.le_last) z) v =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.2
  rw [hF3]
  dsimp [retainedPassiveFormalRawOrderJacobianAt]
  rw [retainedPassiveFormalRawOrderJacobian_apply]
  rw [retainedPassiveLastTopResidualFactorProduct_eq]

/-- The actual retained-passive raw-order Frechet derivative after all
component-level shear corrections.

This is a tuple-level packaging of the landed component identities.  It is not
itself a determinant-one linear shear factorization, because the displayed
corrections still use source-side Frechet derivatives such as `d(Early)` and
`d(LastTop)`. -/
def shearedTopologyTupleEdgeRawOrderFDerivAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    RetainedPassiveRawTopologyTuple ρ κ' ℝ :=
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  let A1fun : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →
      Fin (M + 1) → Matrix ρ ρ ℝ :=
    fun y p ↦
      ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p
  let Earlyfun : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →
      Matrix (κ' (Fin.last (M + 1))) ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
        (K := ℝ) (ρ := ρ) (κ := κ')
        (A1fun y)
        (ChartLocalSuffixState.retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
        0 (Nat.zero_le (M + 1))
  let Lastfun : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct
        (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
        (A1fun y) (Fin.last (M + 1)) (Fin.last M).castSucc
          (Fin.last M).castSucc.le_last
  (fun p : Fin M ↦
      Dzv.1 p
        - (fderiv ℝ
            (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
                p.succ.succ) z) v *
            coord.solvedA3 p.succ
        - coord.F2 p.succ.succ *
            (fderiv ℝ
              (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
                (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.solvedA3
                  p.succ) z) v,
    (fun p : Fin (M + 1) ↦
        Dzv.2.1 p
          + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv p *
            coord.F2 p.castSucc
          - (fderiv ℝ
              (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
                (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
                  p.succ) z) v *
            coord.C p,
      (Dzv.2.2.1,
        (fun p : Fin (M + 1) ↦
            Dzv.2.2.2.1 p
              + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv p *
                coord.F2 p.castSucc,
          (Dzv.2.2.2.2.1
              - (fderiv ℝ
                  (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
                    (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
                      (0 : Fin (M + 1)).succ) z) v *
                  coord.solvedA3 0
              - coord.F2 (0 : Fin (M + 1)).succ *
                  (fderiv ℝ
                    (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
                      (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.solvedA3
                        0) z) v
              - (fderiv ℝ
                  (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
                    (ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
                      (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed)⁻¹) z) v *
                  coord.Ctop,
            Dzv.2.2.2.2.2
              - (fderiv ℝ Earlyfun z) v * Lastfun z
              + (coord.F3 - Earlyfun z) * (fderiv ℝ Lastfun z) v)))))

/-- The fully sheared actual retained-passive raw-order derivative agrees
componentwise with the point-specialized formal raw-order Jacobian.

This theorem assembles the landed component bridges.  It is deliberately weaker
than an absolute determinant formula: it does not prove that the correction
packaging above is a determinant-one shear of the actual Frechet derivative. -/
theorem sheared_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    shearedTopologyTupleEdgeRawOrderFDerivAt (ρ := ρ) (κ' := κ') z v =
      (retainedPassiveFormalRawOrderJacobianAt (ρ := ρ) (κ' := κ') z) v := by
  apply Prod.ext
  · funext p
    simpa [shearedTopologyTupleEdgeRawOrderFDerivAt] using
      A1passive_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
        (ρ := ρ) (κ' := κ') hz v p
  · apply Prod.ext
    · funext p
      simpa [shearedTopologyTupleEdgeRawOrderFDerivAt] using
        F2_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') hz v p
    · apply Prod.ext
      · funext p
        have hA3 :=
          rawEdgeTupleA3_fderiv_topologyTupleEdgeRawOrder_castSucc_eq_formalRawOrderJacobianAt
            (ρ := ρ) (κ' := κ') hz v p
        simpa [shearedTopologyTupleEdgeRawOrderFDerivAt] using hA3
      · apply Prod.ext
        · funext p
          simpa [shearedTopologyTupleEdgeRawOrderFDerivAt] using
            C_unshear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
              (ρ := ρ) (κ' := κ') hz v p
        · apply Prod.ext
          · simpa [shearedTopologyTupleEdgeRawOrderFDerivAt] using
              Ctop_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
                (ρ := ρ) (κ' := κ') hz v
          · simpa [shearedTopologyTupleEdgeRawOrderFDerivAt] using
              F3_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
                (ρ := ρ) (κ' := κ') hz v

/-- The point-specialized formal raw-order map recovers the source `F2`
tangent from its normalized `(F2,C)` edge pair.

This is the first recovery brick for a future staged target-side shear
factorization.  The inverse `coord.solvedA1 p` occurs only in this off-diagonal
recovery calculation; the determinant-bearing formal map is unchanged. -/
theorem retainedPassiveFormalRawOrderJacobianAt_recovers_F2
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) (p : Fin (M + 1)) :
    let u := (retainedPassiveFormalRawOrderJacobianAt (ρ := ρ) (κ' := κ') z) v
    let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
    (coord.solvedA1 p)⁻¹ * (coord.F2 p.succ * u.2.2.2.1 p - u.2.1 p) =
      v.2.1 p := by
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  have hdet : data.detChart := hz
  have hA : IsUnit (coord.solvedA1 p).det := by
    simpa [coord, data] using
      solvedA1_det_isUnit_of_detChart
        (K := ℝ) (ρ := ρ) data hdet p
  change (coord.solvedA1 p)⁻¹ *
      (coord.F2 p.succ *
          ((retainedPassiveFormalRawOrderJacobianAt (ρ := ρ) (κ' := κ') z) v).2.2.2.1 p -
        ((retainedPassiveFormalRawOrderJacobianAt (ρ := ρ) (κ' := κ') z) v).2.1 p) =
    v.2.1 p
  dsimp [retainedPassiveFormalRawOrderJacobianAt]
  rw [retainedPassiveFormalRawOrderJacobian_apply]
  change (coord.solvedA1 p)⁻¹ *
      (coord.F2 p.succ *
          (-coord.solvedA3 p * v.2.1 p + v.2.2.2.1 p) -
        (-(coord.solvedA1 p + coord.F2 p.succ * coord.solvedA3 p) *
            v.2.1 p + coord.F2 p.succ * v.2.2.2.1 p)) =
    v.2.1 p
  have hinside :
      coord.F2 p.succ *
          (-coord.solvedA3 p * v.2.1 p + v.2.2.2.1 p) -
        (-(coord.solvedA1 p + coord.F2 p.succ * coord.solvedA3 p) *
            v.2.1 p + coord.F2 p.succ * v.2.2.2.1 p) =
      coord.solvedA1 p * v.2.1 p := by
    have hleft :
        coord.F2 p.succ *
            (-coord.solvedA3 p * v.2.1 p + v.2.2.2.1 p) =
          -(coord.F2 p.succ * coord.solvedA3 p * v.2.1 p) +
            coord.F2 p.succ * v.2.2.2.1 p := by
      rw [Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
    have hright :
        -(coord.solvedA1 p + coord.F2 p.succ * coord.solvedA3 p) *
            v.2.1 p + coord.F2 p.succ * v.2.2.2.1 p =
          -(coord.solvedA1 p * v.2.1 p +
              coord.F2 p.succ * coord.solvedA3 p * v.2.1 p) +
            coord.F2 p.succ * v.2.2.2.1 p := by
      rw [Matrix.neg_mul, Matrix.add_mul, Matrix.mul_assoc]
    rw [hleft, hright]
    abel
  rw [hinside]
  exact Matrix.nonsing_inv_mul_cancel_left (coord.solvedA1 p) (v.2.1 p) hA

/-- The point-specialized formal raw-order map recovers the source `C` tangent
from the same normalized `(F2,C)` edge pair, after substituting the recovered
source `F2` tangent. -/
theorem retainedPassiveFormalRawOrderJacobianAt_recovers_C
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) (p : Fin (M + 1)) :
    let u := (retainedPassiveFormalRawOrderJacobianAt (ρ := ρ) (κ' := κ') z) v
    let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
    u.2.2.2.1 p +
        coord.solvedA3 p *
          ((coord.solvedA1 p)⁻¹ * (coord.F2 p.succ * u.2.2.2.1 p - u.2.1 p)) =
      v.2.2.2.1 p := by
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  have hF2 :
      (coord.solvedA1 p)⁻¹ *
          (coord.F2 p.succ *
              ((retainedPassiveFormalRawOrderJacobianAt (ρ := ρ) (κ' := κ') z) v).2.2.2.1 p -
            ((retainedPassiveFormalRawOrderJacobianAt (ρ := ρ) (κ' := κ') z) v).2.1 p) =
        v.2.1 p := by
    simpa [coord, data] using
      retainedPassiveFormalRawOrderJacobianAt_recovers_F2
        (ρ := ρ) (κ' := κ') hz v p
  change ((retainedPassiveFormalRawOrderJacobianAt (ρ := ρ) (κ' := κ') z) v).2.2.2.1 p +
        coord.solvedA3 p *
          ((coord.solvedA1 p)⁻¹ *
            (coord.F2 p.succ *
                ((retainedPassiveFormalRawOrderJacobianAt (ρ := ρ) (κ' := κ') z) v).2.2.2.1 p -
              ((retainedPassiveFormalRawOrderJacobianAt (ρ := ρ) (κ' := κ') z) v).2.1 p)) =
      v.2.2.2.1 p
  rw [hF2]
  dsimp [retainedPassiveFormalRawOrderJacobianAt]
  rw [retainedPassiveFormalRawOrderJacobian_apply]
  change (-coord.solvedA3 p * v.2.1 p + v.2.2.2.1 p) +
      coord.solvedA3 p * v.2.1 p =
    v.2.2.2.1 p
  ext i j
  simp

/-- The point-specialized formal raw-order map recovers the passive top-left
source tangent by projection. -/
theorem retainedPassiveFormalRawOrderJacobianAt_recovers_A1passive
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) (p : Fin M) :
    let u := (retainedPassiveFormalRawOrderJacobianAt (ρ := ρ) (κ' := κ') z) v
    u.1 p = v.1 p := by
  dsimp [retainedPassiveFormalRawOrderJacobianAt]
  rw [retainedPassiveFormalRawOrderJacobian_apply]

set_option linter.style.longLine false in
/-- The point-specialized formal raw-order map recovers the `Ctop` source
tangent by multiplying its formal output by the solved first-edge top-left
tail. -/
theorem retainedPassiveFormalRawOrderJacobianAt_recovers_Ctop
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    let u := (retainedPassiveFormalRawOrderJacobianAt (ρ := ρ) (κ' := κ') z) v
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let Tail :=
      ChartLocalSuffixState.retainedPassiveA1TailAfterFirst
        (K := ℝ) (ρ := ρ) data.A1seed
    Tail * u.2.2.2.2.1 = v.2.2.2.2.1 := by
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  let Tail :=
    ChartLocalSuffixState.retainedPassiveA1TailAfterFirst
      (K := ℝ) (ρ := ρ) data.A1seed
  have hdet : data.detChart := hz
  have hPassive :
      ∀ p : Fin (M + 1), p ≠ 0 → IsUnit (coord.A1seed p).det := by
    simpa [coord, data] using
      data.toCoordinateData_passiveA1_units hdet.2
  have hTail : IsUnit Tail.det := by
    simpa [Tail, coord, data] using
      ChartLocalSuffixState.retainedPassiveA1TailAfterFirst_det_isUnit_of_passive
        (K := ℝ) (ρ := ρ) coord.A1seed hPassive
  change Tail *
      ((retainedPassiveFormalRawOrderJacobianAt (ρ := ρ) (κ' := κ') z) v).2.2.2.2.1 =
    v.2.2.2.2.1
  dsimp [retainedPassiveFormalRawOrderJacobianAt]
  rw [retainedPassiveFormalRawOrderJacobian_apply]
  change Tail * (Tail⁻¹ * v.2.2.2.2.1) = v.2.2.2.2.1
  exact Matrix.mul_nonsing_inv_cancel_left Tail v.2.2.2.2.1 hTail

set_option linter.style.longLine false in
/-- The point-specialized formal raw-order map recovers the terminal `F3`
source tangent by right-multiplying its formal output by the nonsingular
inverse of the terminal formal right factor. -/
theorem retainedPassiveFormalRawOrderJacobianAt_recovers_F3
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    let u := (retainedPassiveFormalRawOrderJacobianAt (ρ := ρ) (κ' := κ') z) v
    let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
    u.2.2.2.2.2 * (-(coord.solvedA1 (Fin.last M)))⁻¹ = v.2.2.2.2.2 := by
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  let LastTop := coord.solvedA1 (Fin.last M)
  have hdet : data.detChart := hz
  have hLast : IsUnit LastTop.det := by
    simpa [LastTop, coord, data] using
      solvedA1_det_isUnit_of_detChart
        (K := ℝ) (ρ := ρ) data hdet (Fin.last M)
  have hNegLast : IsUnit (-LastTop).det := by
    exact matrix_det_neg_isUnit_of_det_isUnit LastTop hLast
  change ((retainedPassiveFormalRawOrderJacobianAt (ρ := ρ) (κ' := κ') z) v).2.2.2.2.2 *
      (-LastTop)⁻¹ =
    v.2.2.2.2.2
  dsimp [retainedPassiveFormalRawOrderJacobianAt]
  rw [retainedPassiveFormalRawOrderJacobian_apply]
  change (v.2.2.2.2.2 * (-LastTop)) * (-LastTop)⁻¹ = v.2.2.2.2.2
  exact Matrix.mul_nonsing_inv_cancel_right (-LastTop) v.2.2.2.2.2 hNegLast

/-- At the terminal retained-passive edge, the actual target-side normalized
`(F2,C)` pair agrees with the point-specialized formal edge pair. -/
theorem F2C_terminal_target_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
    let Dzv := (fderiv ℝ raw z) v
    let p : Fin (M + 1) := Fin.last M
    (Dzv.2.1 p
        + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv p *
          coord.F2 p.castSucc,
      Dzv.2.2.2.1 p
        + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv p *
          coord.F2 p.castSucc) =
      (((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.1 p,
        ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.1 p) := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  let p : Fin (M + 1) := Fin.last M
  apply Prod.ext
  · simpa [raw, coord, Dzv, p] using
      F2_terminal_target_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
        (ρ := ρ) (κ' := κ') hz v
  · simpa [raw, coord, Dzv, p] using
      C_unshear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
        (ρ := ρ) (κ' := κ') hz v p

/-- At the terminal retained-passive edge, the actual target-side normalized
`(F2,C)` pair recovers the source `F2` tangent. -/
theorem F2C_terminal_target_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F2
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
    let Dzv := (fderiv ℝ raw z) v
    let p : Fin (M + 1) := Fin.last M
    (coord.solvedA1 p)⁻¹ *
        (coord.F2 p.succ *
            (Dzv.2.2.2.1 p
              + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv p *
                coord.F2 p.castSucc) -
          (Dzv.2.1 p
            + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv p *
              coord.F2 p.castSucc)) =
      v.2.1 p := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  let p : Fin (M + 1) := Fin.last M
  have hF :
      Dzv.2.1 p
          + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv p *
            coord.F2 p.castSucc =
        ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.1 p := by
    simpa [raw, coord, Dzv, p] using
      F2_terminal_target_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
        (ρ := ρ) (κ' := κ') hz v
  have hC :
      Dzv.2.2.2.1 p
          + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv p *
            coord.F2 p.castSucc =
        ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.1 p := by
    simpa [raw, coord, Dzv, p] using
      C_unshear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
        (ρ := ρ) (κ' := κ') hz v p
  have hrec :=
    retainedPassiveFormalRawOrderJacobianAt_recovers_F2
      (ρ := ρ) (κ' := κ') hz v p
  change (coord.solvedA1 p)⁻¹ *
      (coord.F2 p.succ *
          (Dzv.2.2.2.1 p
            + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv p *
              coord.F2 p.castSucc) -
        (Dzv.2.1 p
          + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv p *
            coord.F2 p.castSucc)) =
    v.2.1 p
  rw [hC, hF]
  simpa [coord, p] using hrec

/-- At the terminal retained-passive edge, the actual target-side normalized
`(F2,C)` pair recovers the source `C` tangent. -/
theorem F2C_terminal_target_shear_fderiv_topologyTupleEdgeRawOrder_recovers_C
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
    let Dzv := (fderiv ℝ raw z) v
    let p : Fin (M + 1) := Fin.last M
    Dzv.2.2.2.1 p
        + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv p *
          coord.F2 p.castSucc
        + coord.solvedA3 p *
          ((coord.solvedA1 p)⁻¹ *
            (coord.F2 p.succ *
                (Dzv.2.2.2.1 p
                  + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv p *
                    coord.F2 p.castSucc) -
              (Dzv.2.1 p
                + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv p *
                  coord.F2 p.castSucc))) =
      v.2.2.2.1 p := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  let p : Fin (M + 1) := Fin.last M
  have hF :
      Dzv.2.1 p
          + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv p *
            coord.F2 p.castSucc =
        ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.1 p := by
    simpa [raw, coord, Dzv, p] using
      F2_terminal_target_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
        (ρ := ρ) (κ' := κ') hz v
  have hC :
      Dzv.2.2.2.1 p
          + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv p *
            coord.F2 p.castSucc =
        ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.1 p := by
    simpa [raw, coord, Dzv, p] using
      C_unshear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
        (ρ := ρ) (κ' := κ') hz v p
  have hrec :=
    retainedPassiveFormalRawOrderJacobianAt_recovers_C
      (ρ := ρ) (κ' := κ') hz v p
  change Dzv.2.2.2.1 p
        + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv p *
          coord.F2 p.castSucc
        + coord.solvedA3 p *
          ((coord.solvedA1 p)⁻¹ *
            (coord.F2 p.succ *
                (Dzv.2.2.2.1 p
                  + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv p *
                    coord.F2 p.castSucc) -
              (Dzv.2.1 p
                + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv p *
                  coord.F2 p.castSucc))) =
      v.2.2.2.1 p
  rw [hC, hF]
  simpa [coord, p] using hrec

set_option linter.style.longLine false in
/-- At a nonterminal retained-passive edge, if the staged input is the
successor extended-`F2` derivative, the actual target-side normalized `(F2,C)`
pair agrees with the point-specialized formal edge pair. -/
theorem F2C_nonterminal_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) (p : Fin M)
    (Xsucc : Matrix ρ (κ' p.castSucc.succ) ℝ)
    (hXsucc :
      Xsucc =
        (fderiv ℝ
          (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
              p.castSucc.succ) z) v) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
    let Dzv := (fderiv ℝ raw z) v
    let q : Fin (M + 1) := p.castSucc
    (Dzv.2.1 q
        + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q *
          coord.F2 q.castSucc
        - Xsucc * coord.C q,
      Dzv.2.2.2.1 q
        + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q *
          coord.F2 q.castSucc) =
      (((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.1 q,
        ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.1 q) := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  let q : Fin (M + 1) := p.castSucc
  apply Prod.ext
  · have hF2 :=
      F2_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
        (ρ := ρ) (κ' := κ') hz v q
    change Dzv.2.1 q
        + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q *
          coord.F2 q.castSucc
        - (fderiv ℝ
            (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
                q.succ) z) v *
          coord.C q =
        ((retainedPassiveFormalRawOrderJacobianAt
            (ρ := ρ) (κ' := κ') z) v).2.1 q at hF2
    change Dzv.2.1 q
        + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q *
          coord.F2 q.castSucc
        - Xsucc * coord.C q =
        ((retainedPassiveFormalRawOrderJacobianAt
            (ρ := ρ) (κ' := κ') z) v).2.1 q
    rw [← hXsucc] at hF2
    simpa [q] using hF2
  · simpa [raw, coord, Dzv, q] using
      C_unshear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
        (ρ := ρ) (κ' := κ') hz v q

/-- At a nonterminal retained-passive edge, the derivative-staged actual
target-side normalized `(F2,C)` pair recovers the current source `F2`
tangent. -/
theorem F2C_nonterminal_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F2
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) (p : Fin M)
    (Xsucc : Matrix ρ (κ' p.castSucc.succ) ℝ)
    (hXsucc :
      Xsucc =
        (fderiv ℝ
          (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
              p.castSucc.succ) z) v) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
    let Dzv := (fderiv ℝ raw z) v
    let q : Fin (M + 1) := p.castSucc
    (coord.solvedA1 q)⁻¹ *
        (coord.F2 q.succ *
            (Dzv.2.2.2.1 q
              + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q *
                coord.F2 q.castSucc) -
          (Dzv.2.1 q
            + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q *
              coord.F2 q.castSucc
            - Xsucc * coord.C q)) =
      v.2.1 q := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  let q : Fin (M + 1) := p.castSucc
  have hpair :=
    F2C_nonterminal_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (ρ := ρ) (κ' := κ') hz v p Xsucc hXsucc
  have hF :
      Dzv.2.1 q
          + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q *
            coord.F2 q.castSucc
          - Xsucc * coord.C q =
        ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.1 q := by
    simpa [raw, coord, Dzv, q] using congrArg Prod.fst hpair
  have hC :
      Dzv.2.2.2.1 q
          + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q *
            coord.F2 q.castSucc =
        ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.1 q := by
    simpa [raw, coord, Dzv, q] using congrArg Prod.snd hpair
  have hrec :=
    retainedPassiveFormalRawOrderJacobianAt_recovers_F2
      (ρ := ρ) (κ' := κ') hz v q
  change (coord.solvedA1 q)⁻¹ *
      (coord.F2 q.succ *
          (Dzv.2.2.2.1 q
            + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q *
              coord.F2 q.castSucc) -
        (Dzv.2.1 q
          + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q *
            coord.F2 q.castSucc
          - Xsucc * coord.C q)) =
    v.2.1 q
  rw [hC, hF]
  simpa [coord, q] using hrec

/-- At a nonterminal retained-passive edge, the derivative-staged actual
target-side normalized `(F2,C)` pair recovers the current source `C`
tangent. -/
theorem F2C_nonterminal_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_C
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) (p : Fin M)
    (Xsucc : Matrix ρ (κ' p.castSucc.succ) ℝ)
    (hXsucc :
      Xsucc =
        (fderiv ℝ
          (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
              p.castSucc.succ) z) v) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
    let Dzv := (fderiv ℝ raw z) v
    let q : Fin (M + 1) := p.castSucc
    Dzv.2.2.2.1 q
        + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q *
          coord.F2 q.castSucc
        + coord.solvedA3 q *
          ((coord.solvedA1 q)⁻¹ *
            (coord.F2 q.succ *
                (Dzv.2.2.2.1 q
                  + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q *
                    coord.F2 q.castSucc) -
              (Dzv.2.1 q
                + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q *
                  coord.F2 q.castSucc
                - Xsucc * coord.C q))) =
      v.2.2.2.1 q := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  let q : Fin (M + 1) := p.castSucc
  have hpair :=
    F2C_nonterminal_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (ρ := ρ) (κ' := κ') hz v p Xsucc hXsucc
  have hF :
      Dzv.2.1 q
          + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q *
            coord.F2 q.castSucc
          - Xsucc * coord.C q =
        ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.1 q := by
    simpa [raw, coord, Dzv, q] using congrArg Prod.fst hpair
  have hC :
      Dzv.2.2.2.1 q
          + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q *
            coord.F2 q.castSucc =
        ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.1 q := by
    simpa [raw, coord, Dzv, q] using congrArg Prod.snd hpair
  have hrec :=
    retainedPassiveFormalRawOrderJacobianAt_recovers_C
      (ρ := ρ) (κ' := κ') hz v q
  change Dzv.2.2.2.1 q
        + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q *
          coord.F2 q.castSucc
        + coord.solvedA3 q *
          ((coord.solvedA1 q)⁻¹ *
            (coord.F2 q.succ *
                (Dzv.2.2.2.1 q
                  + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q *
                    coord.F2 q.castSucc) -
              (Dzv.2.1 q
                + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q *
                  coord.F2 q.castSucc
                - Xsucc * coord.C q))) =
      v.2.2.2.1 q
  rw [hC, hF]
  simpa [coord, q] using hrec

set_option linter.style.longLine false in
/-- At a nonterminal retained-passive edge, if the successor source `F2`
tangent has already been staged, the actual target-side normalized `(F2,C)`
pair agrees with the point-specialized formal edge pair. -/
theorem F2C_nonterminal_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) (p : Fin M) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
    let Dzv := (fderiv ℝ raw z) v
    let q : Fin (M + 1) := p.castSucc
    let Xsucc : Matrix ρ (κ' p.castSucc.succ) ℝ :=
      (LinearEquiv.cast (R := ℝ)
        (M := fun i : Fin (M + 2) ↦ Matrix ρ (κ' i) ℝ)
        (Fin.succ_castSucc p).symm) (v.2.1 p.succ)
    (Dzv.2.1 q
        + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q *
          coord.F2 q.castSucc
        - Xsucc * coord.C q,
      Dzv.2.2.2.1 q
        + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q *
          coord.F2 q.castSucc) =
      (((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.1 q,
        ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.1 q) := by
  let Xsucc : Matrix ρ (κ' p.castSucc.succ) ℝ :=
    (LinearEquiv.cast (R := ℝ)
      (M := fun i : Fin (M + 2) ↦ Matrix ρ (κ' i) ℝ)
      (Fin.succ_castSucc p).symm) (v.2.1 p.succ)
  have hXsucc :
      Xsucc =
        (fderiv ℝ
          (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
              p.castSucc.succ) z) v := by
    rw [fderiv_retainedPassive_toCoordinateData_F2_nonterminal_succ_apply
      (ρ := ρ) (κ' := κ') z v p]
  simpa [Xsucc] using
    F2C_nonterminal_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (ρ := ρ) (κ' := κ') hz v p Xsucc hXsucc

set_option linter.style.longLine false in
/-- At a nonterminal retained-passive edge, the source-staged actual
target-side normalized `(F2,C)` pair recovers the current source `F2`
tangent. -/
theorem F2C_nonterminal_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F2
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) (p : Fin M) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
    let Dzv := (fderiv ℝ raw z) v
    let q : Fin (M + 1) := p.castSucc
    let Xsucc : Matrix ρ (κ' p.castSucc.succ) ℝ :=
      (LinearEquiv.cast (R := ℝ)
        (M := fun i : Fin (M + 2) ↦ Matrix ρ (κ' i) ℝ)
        (Fin.succ_castSucc p).symm) (v.2.1 p.succ)
    (coord.solvedA1 q)⁻¹ *
        (coord.F2 q.succ *
            (Dzv.2.2.2.1 q
              + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q *
                coord.F2 q.castSucc) -
          (Dzv.2.1 q
            + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q *
              coord.F2 q.castSucc
            - Xsucc * coord.C q)) =
      v.2.1 q := by
  let Xsucc : Matrix ρ (κ' p.castSucc.succ) ℝ :=
    (LinearEquiv.cast (R := ℝ)
      (M := fun i : Fin (M + 2) ↦ Matrix ρ (κ' i) ℝ)
      (Fin.succ_castSucc p).symm) (v.2.1 p.succ)
  have hXsucc :
      Xsucc =
        (fderiv ℝ
          (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
              p.castSucc.succ) z) v := by
    rw [fderiv_retainedPassive_toCoordinateData_F2_nonterminal_succ_apply
      (ρ := ρ) (κ' := κ') z v p]
  simpa [Xsucc] using
    F2C_nonterminal_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F2
      (ρ := ρ) (κ' := κ') hz v p Xsucc hXsucc

set_option linter.style.longLine false in
/-- At a nonterminal retained-passive edge, the source-staged actual
target-side normalized `(F2,C)` pair recovers the current source `C`
tangent. -/
theorem F2C_nonterminal_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_C
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) (p : Fin M) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
    let Dzv := (fderiv ℝ raw z) v
    let q : Fin (M + 1) := p.castSucc
    let Xsucc : Matrix ρ (κ' p.castSucc.succ) ℝ :=
      (LinearEquiv.cast (R := ℝ)
        (M := fun i : Fin (M + 2) ↦ Matrix ρ (κ' i) ℝ)
        (Fin.succ_castSucc p).symm) (v.2.1 p.succ)
    Dzv.2.2.2.1 q
        + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q *
          coord.F2 q.castSucc
        + coord.solvedA3 q *
          ((coord.solvedA1 q)⁻¹ *
            (coord.F2 q.succ *
                (Dzv.2.2.2.1 q
                  + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q *
                    coord.F2 q.castSucc) -
              (Dzv.2.1 q
                + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q *
                  coord.F2 q.castSucc
                - Xsucc * coord.C q))) =
      v.2.2.2.1 q := by
  let Xsucc : Matrix ρ (κ' p.castSucc.succ) ℝ :=
    (LinearEquiv.cast (R := ℝ)
      (M := fun i : Fin (M + 2) ↦ Matrix ρ (κ' i) ℝ)
      (Fin.succ_castSucc p).symm) (v.2.1 p.succ)
  have hXsucc :
      Xsucc =
        (fderiv ℝ
          (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
              p.castSucc.succ) z) v := by
    rw [fderiv_retainedPassive_toCoordinateData_F2_nonterminal_succ_apply
      (ρ := ρ) (κ' := κ') z v p]
  simpa [Xsucc] using
    F2C_nonterminal_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_C
      (ρ := ρ) (κ' := κ') hz v p Xsucc hXsucc

set_option linter.style.longLine false in
/-- The all-edge source-staged successor `F2` tangent family: nonterminal
edges use the casted successor source tangent, while the terminal edge uses
the retained-passive zero extension. -/
def retainedPassiveSourceStagedSuccessorF2
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    ∀ q : Fin (M + 1), Matrix ρ (κ' q.succ) ℝ :=
  @Fin.snoc (n := M)
    (α := fun q : Fin (M + 1) ↦ Matrix ρ (κ' q.succ) ℝ)
    (fun p : Fin M ↦
      (LinearEquiv.cast (R := ℝ)
        (M := fun i : Fin (M + 2) ↦ Matrix ρ (κ' i) ℝ)
        (Fin.succ_castSucc p).symm) (v.2.1 p.succ))
    (0 : Matrix ρ (κ' (Fin.last M).succ) ℝ)

set_option linter.style.longLine false in
@[simp]
theorem retainedPassiveSourceStagedSuccessorF2_castSucc
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) (p : Fin M) :
    retainedPassiveSourceStagedSuccessorF2 (ρ := ρ) (κ' := κ') v p.castSucc =
      (LinearEquiv.cast (R := ℝ)
        (M := fun i : Fin (M + 2) ↦ Matrix ρ (κ' i) ℝ)
        (Fin.succ_castSucc p).symm) (v.2.1 p.succ) := by
  simp [retainedPassiveSourceStagedSuccessorF2]

@[simp]
theorem retainedPassiveSourceStagedSuccessorF2_last
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    retainedPassiveSourceStagedSuccessorF2 (ρ := ρ) (κ' := κ') v (Fin.last M) = 0 := by
  simp [retainedPassiveSourceStagedSuccessorF2]

set_option linter.style.longLine false in
/-- The all-edge source-staged actual target-side normalized `(F2,C)` family
agrees with the point-specialized formal edge-pair family. -/
theorem F2C_all_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
    let Dzv := (fderiv ℝ raw z) v
    let Xsucc := retainedPassiveSourceStagedSuccessorF2 (ρ := ρ) (κ' := κ') v
    (fun q : Fin (M + 1) ↦
        Dzv.2.1 q
          + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q *
            coord.F2 q.castSucc
          - Xsucc q * coord.C q,
      fun q : Fin (M + 1) ↦
        Dzv.2.2.2.1 q
          + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q *
            coord.F2 q.castSucc) =
      (((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.1,
        ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.1) := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  let Xsucc := retainedPassiveSourceStagedSuccessorF2 (ρ := ρ) (κ' := κ') v
  apply Prod.ext
  · funext q
    induction q using Fin.lastCases with
    | last =>
        have hpair :=
          F2C_terminal_target_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
            (ρ := ρ) (κ' := κ') hz v
        have hF :
            Dzv.2.1 (Fin.last M)
                + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv (Fin.last M) *
                  coord.F2 (Fin.last M).castSucc =
              ((retainedPassiveFormalRawOrderJacobianAt
                (ρ := ρ) (κ' := κ') z) v).2.1 (Fin.last M) := by
          simpa [raw, coord, Dzv] using congrArg Prod.fst hpair
        change Dzv.2.1 (Fin.last M)
              + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv (Fin.last M) *
                coord.F2 (Fin.last M).castSucc
              - Xsucc (Fin.last M) * coord.C (Fin.last M) =
            ((retainedPassiveFormalRawOrderJacobianAt
              (ρ := ρ) (κ' := κ') z) v).2.1 (Fin.last M)
        rw [show Xsucc (Fin.last M) = 0 by simp [Xsucc]]
        rw [Matrix.zero_mul, sub_zero]
        exact hF
    | cast p =>
        have hpair :=
          F2C_nonterminal_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
            (ρ := ρ) (κ' := κ') hz v p
        have hF := congrArg Prod.fst hpair
        simpa [raw, coord, Dzv, Xsucc] using hF
  · funext q
    induction q using Fin.lastCases with
    | last =>
        have hpair :=
          F2C_terminal_target_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
            (ρ := ρ) (κ' := κ') hz v
        have hC := congrArg Prod.snd hpair
        simpa [raw, coord, Dzv, Xsucc] using hC
    | cast p =>
        have hpair :=
          F2C_nonterminal_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
            (ρ := ρ) (κ' := κ') hz v p
        have hC := congrArg Prod.snd hpair
        simpa [raw, coord, Dzv, Xsucc] using hC

set_option linter.style.longLine false in
/-- The formal edge-pair inverse recovers the source `(F2,C)` family from the
all-edge source-staged actual target-side normalized family. -/
theorem F2C_all_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_sourcePair
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
    let Dzv := (fderiv ℝ raw z) v
    let Xsucc := retainedPassiveSourceStagedSuccessorF2 (ρ := ρ) (κ' := κ') v
    (retainedPassiveFormalRawF2CLinearEquivAt (ρ := ρ) (κ' := κ') hz).symm
      (fun q : Fin (M + 1) ↦
          Dzv.2.1 q
            + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q *
              coord.F2 q.castSucc
            - Xsucc q * coord.C q,
        fun q : Fin (M + 1) ↦
          Dzv.2.2.2.1 q
            + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q *
              coord.F2 q.castSucc) =
      (v.2.1, v.2.2.2.1) := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  let Xsucc := retainedPassiveSourceStagedSuccessorF2 (ρ := ρ) (κ' := κ') v
  have hpair :=
    F2C_all_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (ρ := ρ) (κ' := κ') hz v
  have hrec :=
    retainedPassiveFormalRawF2CLinearEquivAt_symm_recovers_sourcePair
      (ρ := ρ) (κ' := κ') hz v
  change (retainedPassiveFormalRawF2CLinearEquivAt (ρ := ρ) (κ' := κ') hz).symm
      (fun q : Fin (M + 1) ↦
          Dzv.2.1 q
            + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q *
              coord.F2 q.castSucc
            - Xsucc q * coord.C q,
        fun q : Fin (M + 1) ↦
          Dzv.2.2.2.1 q
            + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q *
              coord.F2 q.castSucc) =
      (v.2.1, v.2.2.2.1)
  rw [hpair]
  simpa using hrec

set_option linter.style.longLine false in
/-- Recover the retained `F2` source family from a target raw tuple by a
backward edge recurrence.  The terminal edge uses the retained-passive zero
successor convention; a nonterminal edge uses the already recovered successor
`F2` value. -/
def retainedPassiveTargetRecoveredF2At
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    ∀ q : Fin (M + 1), Matrix ρ (κ' q.castSucc) ℝ :=
  let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
  Fin.reverseInduction
    (let q : Fin (M + 1) := Fin.last M
     let U_F :=
      w.2.1 q
        + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') w q *
          coord.F2 q.castSucc
     let U_C :=
      w.2.2.2.1 q
        + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') w q *
          coord.F2 q.castSucc
     (coord.solvedA1 q)⁻¹ * (coord.F2 q.succ * U_C - U_F))
    (fun p Xnext ↦
      let q : Fin (M + 1) := p.castSucc
      let Xsucc : Matrix ρ (κ' q.succ) ℝ :=
        (LinearEquiv.cast (R := ℝ)
          (M := fun i : Fin (M + 2) ↦ Matrix ρ (κ' i) ℝ)
          (Fin.succ_castSucc p).symm) Xnext
      let U_F :=
        w.2.1 q
          + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') w q *
            coord.F2 q.castSucc
          - Xsucc * coord.C q
      let U_C :=
        w.2.2.2.1 q
          + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') w q *
            coord.F2 q.castSucc
      (coord.solvedA1 q)⁻¹ * (coord.F2 q.succ * U_C - U_F))

set_option linter.style.longLine false in
@[simp]
theorem retainedPassiveTargetRecoveredF2At_last
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
    let q : Fin (M + 1) := Fin.last M
    retainedPassiveTargetRecoveredF2At (ρ := ρ) (κ' := κ') z w q =
      (coord.solvedA1 q)⁻¹ *
        (coord.F2 q.succ *
            (w.2.2.2.1 q
              + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') w q *
                coord.F2 q.castSucc) -
          (w.2.1 q
            + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') w q *
              coord.F2 q.castSucc)) := by
  simp [retainedPassiveTargetRecoveredF2At]

set_option linter.style.longLine false in
@[simp]
theorem retainedPassiveTargetRecoveredF2At_castSucc
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) (p : Fin M) :
    let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
    let q : Fin (M + 1) := p.castSucc
    let Xsucc : Matrix ρ (κ' q.succ) ℝ :=
      (LinearEquiv.cast (R := ℝ)
        (M := fun i : Fin (M + 2) ↦ Matrix ρ (κ' i) ℝ)
        (Fin.succ_castSucc p).symm)
        (retainedPassiveTargetRecoveredF2At (ρ := ρ) (κ' := κ') z w p.succ)
    retainedPassiveTargetRecoveredF2At (ρ := ρ) (κ' := κ') z w q =
      (coord.solvedA1 q)⁻¹ *
        (coord.F2 q.succ *
            (w.2.2.2.1 q
              + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') w q *
                coord.F2 q.castSucc) -
          (w.2.1 q
            + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') w q *
              coord.F2 q.castSucc
            - Xsucc * coord.C q)) := by
  simp [retainedPassiveTargetRecoveredF2At]

set_option linter.style.longLine false in
/-- The target-recovered successor `F2` family induced by the backward
recovery recurrence. -/
def retainedPassiveTargetRecoveredSuccessorF2At
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    ∀ q : Fin (M + 1), Matrix ρ (κ' q.succ) ℝ :=
  @Fin.snoc (n := M)
    (α := fun q : Fin (M + 1) ↦ Matrix ρ (κ' q.succ) ℝ)
    (fun p : Fin M ↦
      (LinearEquiv.cast (R := ℝ)
        (M := fun i : Fin (M + 2) ↦ Matrix ρ (κ' i) ℝ)
        (Fin.succ_castSucc p).symm)
        (retainedPassiveTargetRecoveredF2At (ρ := ρ) (κ' := κ') z w p.succ))
    (0 : Matrix ρ (κ' (Fin.last M).succ) ℝ)

set_option linter.style.longLine false in
@[simp]
theorem retainedPassiveTargetRecoveredSuccessorF2At_castSucc
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) (p : Fin M) :
    retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z w p.castSucc =
      (LinearEquiv.cast (R := ℝ)
        (M := fun i : Fin (M + 2) ↦ Matrix ρ (κ' i) ℝ)
        (Fin.succ_castSucc p).symm)
        (retainedPassiveTargetRecoveredF2At (ρ := ρ) (κ' := κ') z w p.succ) := by
  simp [retainedPassiveTargetRecoveredSuccessorF2At]

@[simp]
theorem retainedPassiveTargetRecoveredSuccessorF2At_last
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    retainedPassiveTargetRecoveredSuccessorF2At
        (ρ := ρ) (κ' := κ') z w (Fin.last M) = 0 := by
  simp [retainedPassiveTargetRecoveredSuccessorF2At]

set_option linter.style.longLine false in
/-- On an actual raw-order derivative target, the target-recovered `F2` family
is the source `F2` tangent family. -/
theorem retainedPassiveTargetRecoveredF2At_fderiv_eq_sourceF2
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    retainedPassiveTargetRecoveredF2At
        (ρ := ρ) (κ' := κ') z ((fderiv ℝ raw z) v) = v.2.1 := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  change retainedPassiveTargetRecoveredF2At
      (ρ := ρ) (κ' := κ') z ((fderiv ℝ raw z) v) = v.2.1
  funext q
  let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  induction q using Fin.reverseInduction with
  | last =>
      have hrec :=
        F2C_terminal_target_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F2
          (ρ := ρ) (κ' := κ') hz v
      rw [retainedPassiveTargetRecoveredF2At_last]
      simpa [raw, coord, Dzv] using hrec
  | cast p ih =>
      have hrec :=
        F2C_nonterminal_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F2
          (ρ := ρ) (κ' := κ') hz v p
      rw [retainedPassiveTargetRecoveredF2At_castSucc]
      rw [ih]
      simpa [raw, coord, Dzv] using hrec

set_option linter.style.longLine false in
/-- On an actual raw-order derivative target, the target-recovered successor
family agrees with the earlier source-staged successor family. -/
theorem retainedPassiveTargetRecoveredSuccessorF2At_fderiv_eq_sourceStagedSuccessorF2
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    retainedPassiveTargetRecoveredSuccessorF2At
        (ρ := ρ) (κ' := κ') z ((fderiv ℝ raw z) v) =
      retainedPassiveSourceStagedSuccessorF2 (ρ := ρ) (κ' := κ') v := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  change retainedPassiveTargetRecoveredSuccessorF2At
      (ρ := ρ) (κ' := κ') z ((fderiv ℝ raw z) v) =
    retainedPassiveSourceStagedSuccessorF2 (ρ := ρ) (κ' := κ') v
  have hF :=
    retainedPassiveTargetRecoveredF2At_fderiv_eq_sourceF2
      (ρ := ρ) (κ' := κ') hz v
  change retainedPassiveTargetRecoveredF2At
      (ρ := ρ) (κ' := κ') z ((fderiv ℝ raw z) v) = v.2.1 at hF
  funext q
  induction q using Fin.lastCases with
  | last =>
      simp [retainedPassiveTargetRecoveredSuccessorF2At,
        retainedPassiveSourceStagedSuccessorF2]
  | cast p =>
      have hp := congrFun hF p.succ
      simp [retainedPassiveTargetRecoveredSuccessorF2At,
        retainedPassiveSourceStagedSuccessorF2, hp]

set_option linter.style.longLine false in
/-- Target-side all-edge `(F2,C)` shear using the successor family recovered
from the target tuple itself. -/
def retainedPassiveTargetEdgePairShearAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    ((∀ q : Fin (M + 1), Matrix ρ (κ' q.castSucc) ℝ) ×
      (∀ q : Fin (M + 1), Matrix (κ' q.succ) (κ' q.castSucc) ℝ)) :=
  let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
  let Xsucc := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z w
  (fun q : Fin (M + 1) ↦
      w.2.1 q
        + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') w q *
          coord.F2 q.castSucc
        - Xsucc q * coord.C q,
    fun q : Fin (M + 1) ↦
      w.2.2.2.1 q
        + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') w q *
          coord.F2 q.castSucc)

set_option linter.style.longLine false in
/-- On an actual raw-order derivative target, the target-side all-edge
`(F2,C)` shear agrees with the `(F2,C)` component of the point-specialized
formal raw-order output. -/
theorem retainedPassiveTargetEdgePairShearAt_fderiv_eq_formalF2C
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    retainedPassiveTargetEdgePairShearAt
        (ρ := ρ) (κ' := κ') z ((fderiv ℝ raw z) v) =
      (((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.1,
        ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.1) := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  have hX :=
    retainedPassiveTargetRecoveredSuccessorF2At_fderiv_eq_sourceStagedSuccessorF2
      (ρ := ρ) (κ' := κ') hz v
  have hsource :=
    F2C_all_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (ρ := ρ) (κ' := κ') hz v
  change retainedPassiveTargetEdgePairShearAt (ρ := ρ) (κ' := κ') z Dzv =
      (((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.1,
        ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.1)
  rw [retainedPassiveTargetEdgePairShearAt, hX]
  simpa [raw, coord, Dzv] using hsource

set_option linter.style.longLine false in
/-- The formal edge-pair inverse recovers the source `(F2,C)` family from the
target-side all-edge normalized pair on an actual raw-order derivative target. -/
theorem retainedPassiveTargetEdgePairShearAt_fderiv_recovers_sourcePair
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    (retainedPassiveFormalRawF2CLinearEquivAt (ρ := ρ) (κ' := κ') hz).symm
        (retainedPassiveTargetEdgePairShearAt
          (ρ := ρ) (κ' := κ') z ((fderiv ℝ raw z) v)) =
      (v.2.1, v.2.2.2.1) := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  have hpair :=
    retainedPassiveTargetEdgePairShearAt_fderiv_eq_formalF2C
      (ρ := ρ) (κ' := κ') hz v
  have hrec :=
    retainedPassiveFormalRawF2CLinearEquivAt_symm_recovers_sourcePair
      (ρ := ρ) (κ' := κ') hz v
  change (retainedPassiveFormalRawF2CLinearEquivAt (ρ := ρ) (κ' := κ') hz).symm
      (retainedPassiveTargetEdgePairShearAt
        (ρ := ρ) (κ' := κ') z ((fderiv ℝ raw z) v)) =
    (v.2.1, v.2.2.2.1)
  rw [hpair]
  simpa using hrec

set_option linter.style.longLine false in
/-- Hybrid whole-tuple package whose `(F2,C)` edge-family branch is
source-staged, while `A1passive`, `Ctop`, and `F3` keep the derivative-staged
corrections from `shearedTopologyTupleEdgeRawOrderFDerivAt`. -/
def edgePairSourceStagedShearedTopologyTupleEdgeRawOrderFDerivAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    RetainedPassiveRawTopologyTuple ρ κ' ℝ :=
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  let old := shearedTopologyTupleEdgeRawOrderFDerivAt (ρ := ρ) (κ' := κ') z v
  let Xsucc := retainedPassiveSourceStagedSuccessorF2 (ρ := ρ) (κ' := κ') v
  (old.1,
    (fun q : Fin (M + 1) ↦
        Dzv.2.1 q
          + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q *
            coord.F2 q.castSucc
          - Xsucc q * coord.C q,
      (old.2.2.1,
        (fun q : Fin (M + 1) ↦
            Dzv.2.2.2.1 q
              + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q *
                coord.F2 q.castSucc,
          old.2.2.2.2))))

set_option linter.style.longLine false in
/-- The hybrid whole-tuple package with source-staged `(F2,C)` branch agrees
with the point-specialized formal raw-order Jacobian.  Only the `(F2,C)` branch
is source-staged; the other corrections remain derivative-staged. -/
theorem edgePairSourceStaged_sheared_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    edgePairSourceStagedShearedTopologyTupleEdgeRawOrderFDerivAt
        (ρ := ρ) (κ' := κ') z v =
      (retainedPassiveFormalRawOrderJacobianAt (ρ := ρ) (κ' := κ') z) v := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  let old := shearedTopologyTupleEdgeRawOrderFDerivAt (ρ := ρ) (κ' := κ') z v
  let Xsucc := retainedPassiveSourceStagedSuccessorF2 (ρ := ρ) (κ' := κ') v
  have hold :=
    sheared_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (ρ := ρ) (κ' := κ') hz v
  have hF2C :=
    F2C_all_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (ρ := ρ) (κ' := κ') hz v
  apply Prod.ext
  · simpa [edgePairSourceStagedShearedTopologyTupleEdgeRawOrderFDerivAt, old] using
      congrArg Prod.fst hold
  · apply Prod.ext
    · simpa [edgePairSourceStagedShearedTopologyTupleEdgeRawOrderFDerivAt,
        raw, coord, Dzv, Xsucc] using congrArg Prod.fst hF2C
    · apply Prod.ext
      · simpa [edgePairSourceStagedShearedTopologyTupleEdgeRawOrderFDerivAt, old] using
          congrArg (fun u : RetainedPassiveRawTopologyTuple ρ κ' ℝ ↦ u.2.2.1) hold
      · apply Prod.ext
        · simpa [edgePairSourceStagedShearedTopologyTupleEdgeRawOrderFDerivAt,
            raw, coord, Dzv, Xsucc] using congrArg Prod.snd hF2C
        · simpa [edgePairSourceStagedShearedTopologyTupleEdgeRawOrderFDerivAt, old] using
            congrArg (fun u : RetainedPassiveRawTopologyTuple ρ κ' ℝ ↦ u.2.2.2.2) hold

set_option linter.style.longLine false in
/-- The all-edge source-staged successor lower-left tangent family: nonterminal
edges use the stored passive `A3` source tangent, while the terminal edge uses
zero.  This is not the derivative of `solvedA3` at the terminal edge. -/
def retainedPassiveSourceStagedSuccessorA3
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    ∀ q : Fin (M + 1), Matrix (κ' q.succ) ρ ℝ :=
  @Fin.snoc (n := M)
    (α := fun q : Fin (M + 1) ↦ Matrix (κ' q.succ) ρ ℝ)
    (fun p : Fin M ↦ v.2.2.1 p)
    (0 : Matrix (κ' (Fin.last M).succ) ρ ℝ)

@[simp]
theorem retainedPassiveSourceStagedSuccessorA3_castSucc
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) (p : Fin M) :
    retainedPassiveSourceStagedSuccessorA3 (ρ := ρ) (κ' := κ') v p.castSucc =
      v.2.2.1 p := by
  simp [retainedPassiveSourceStagedSuccessorA3]

@[simp]
theorem retainedPassiveSourceStagedSuccessorA3_last
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    retainedPassiveSourceStagedSuccessorA3 (ρ := ρ) (κ' := κ') v (Fin.last M) = 0 := by
  simp [retainedPassiveSourceStagedSuccessorA3]

set_option linter.style.longLine false in
/-- At a nonterminal lower-left edge, the solved `A3` coordinate is the stored
passive source coordinate, so its Frechet derivative is the passive source
tangent. -/
theorem fderiv_retainedPassive_toCoordinateData_solvedA3_castSucc_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) (p : Fin M) :
    (fderiv ℝ
      (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.solvedA3
          p.castSucc) z) v =
      v.2.2.1 p := by
  have hfun :
      (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.solvedA3
          p.castSucc) =
        fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦ y.2.2.1 p := by
    funext y
    change
      ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA3
          p.castSucc =
        y.2.2.1 p
    have hsolve :=
      ChartLocalSuffixState.retainedPassiveSolvedA3_eq_of_ne_last
        (K := ℝ) (ρ := ρ) (κ' := κ')
        ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).F3
        (Fin.castSucc_ne_last p)
    simpa [ChartLocalSuffixState.RetainedPassiveCoordinateData.solvedA3, toCoordinateData] using hsolve
  let LA3 : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →L[ℝ]
      Matrix (κ' p.castSucc.succ) ρ ℝ :=
    { toLinearMap :=
        { toFun := fun y ↦ y.2.2.1 p
          map_add' := by
            intro x y
            rfl
          map_smul' := by
            intro a y
            rfl }
      cont := by fun_prop }
  rw [hfun]
  have hLA3 :
      fderiv ℝ
          (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦ y.2.2.1 p) z =
        LA3 := LA3.fderiv
  rw [hLA3]
  rfl

set_option linter.style.longLine false in
/-- The derivative of the extended successor `F2` coordinate is exactly the
all-edge source-staged successor `F2` tangent family. -/
theorem fderiv_retainedPassive_toCoordinateData_F2_succ_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Finite ρ] [∀ j, Finite (κ' j)]
    (z v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) (q : Fin (M + 1)) :
    (fderiv ℝ
      (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
          q.succ) z) v =
      retainedPassiveSourceStagedSuccessorF2 (ρ := ρ) (κ' := κ') v q := by
  induction q using Fin.lastCases with
  | last =>
      simpa using
        fderiv_retainedPassive_toCoordinateData_F2_last_apply
          (ρ := ρ) (κ' := κ') z v
  | cast p =>
      simpa using
        fderiv_retainedPassive_toCoordinateData_F2_nonterminal_succ_apply
          (ρ := ρ) (κ' := κ') z v p

set_option linter.style.longLine false in
/-- Multiplying by the successor extended `F2` slot makes the source-staged
lower-left readout valid at every edge.  At nonterminal edges this is the
projection derivative of `solvedA3`; at the terminal edge both sides have the
zero terminal extended `F2` factor. -/
theorem retainedPassive_F2_succ_mul_fderiv_solvedA3_eq_sourceStagedSuccessorA3
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) (q : Fin (M + 1)) :
    let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
    coord.F2 q.succ *
        (fderiv ℝ
          (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.solvedA3
              q) z) v =
      coord.F2 q.succ * retainedPassiveSourceStagedSuccessorA3 (ρ := ρ) (κ' := κ') v q := by
  let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
  induction q using Fin.lastCases with
  | last =>
      have hF2 : coord.F2 (Fin.last (M + 1)) = 0 := by
        simp [coord, ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.toCoordinateData]
      have hF2' : coord.F2 (Fin.last M).succ = 0 := by
        simpa using hF2
      change coord.F2 (Fin.last M).succ *
          (fderiv ℝ
            (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.solvedA3
                (Fin.last M)) z) v =
        coord.F2 (Fin.last M).succ *
          retainedPassiveSourceStagedSuccessorA3 (ρ := ρ) (κ' := κ') v (Fin.last M)
      rw [hF2']
      rw [Matrix.zero_mul, Matrix.zero_mul]
  | cast p =>
      have hA3 :=
        fderiv_retainedPassive_toCoordinateData_solvedA3_castSucc_apply
          (ρ := ρ) (κ' := κ') z v p
      change coord.F2 p.castSucc.succ *
          (fderiv ℝ
            (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.solvedA3
                p.castSucc) z) v =
        coord.F2 p.castSucc.succ *
          retainedPassiveSourceStagedSuccessorA3 (ρ := ρ) (κ' := κ') v p.castSucc
      rw [hA3]
      simp

set_option linter.style.longLine false in
/-- The passive top-left branch can be staged using explicit successor source
`F2` and lower-left tangents.  The terminal lower-left derivative is not
identified with a source tangent; it is killed only after multiplication by
the terminal zero extended `F2` slot. -/
theorem A1passive_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) (p : Fin M) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
    let XsuccF2 := retainedPassiveSourceStagedSuccessorF2 (ρ := ρ) (κ' := κ') v
    let XsuccA3 := retainedPassiveSourceStagedSuccessorA3 (ρ := ρ) (κ' := κ') v
    ((fderiv ℝ raw z) v).1 p
      - XsuccF2 p.succ * coord.solvedA3 p.succ
      - coord.F2 p.succ.succ * XsuccA3 p.succ =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).1 p := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
  let XsuccF2 := retainedPassiveSourceStagedSuccessorF2 (ρ := ρ) (κ' := κ') v
  let XsuccA3 := retainedPassiveSourceStagedSuccessorA3 (ρ := ρ) (κ' := κ') v
  have hA1 :=
    A1passive_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (ρ := ρ) (κ' := κ') hz v p
  have hF2 :=
    fderiv_retainedPassive_toCoordinateData_F2_succ_apply
      (ρ := ρ) (κ' := κ') z v p.succ
  have hA3 :=
    retainedPassive_F2_succ_mul_fderiv_solvedA3_eq_sourceStagedSuccessorA3
      (ρ := ρ) (κ' := κ') z v p.succ
  change ((fderiv ℝ raw z) v).1 p
      - (fderiv ℝ
          (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
              p.succ.succ) z) v *
          coord.solvedA3 p.succ
      - coord.F2 p.succ.succ *
          (fderiv ℝ
            (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.solvedA3
                p.succ) z) v =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).1 p at hA1
  change coord.F2 p.succ.succ *
          (fderiv ℝ
            (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.solvedA3
                p.succ) z) v =
        coord.F2 p.succ.succ * XsuccA3 p.succ at hA3
  rw [hF2] at hA1
  rw [hA3] at hA1
  simpa [XsuccF2, XsuccA3] using hA1

set_option linter.style.longLine false in
/-- Multiplying by the successor extended `F2` slot makes the raw lower-left
target readout agree with the source-staged lower-left tangent family on an
actual derivative target.  At the terminal edge this uses only the terminal
zero extended `F2` factor; it does not identify the terminal raw lower-left
derivative with zero. -/
theorem retainedPassive_F2_succ_mul_rawEdgeTupleA3_fderiv_eq_sourceStagedSuccessorA3
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) (q : Fin (M + 1)) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
    coord.F2 q.succ *
        rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') ((fderiv ℝ raw z) v) q =
      coord.F2 q.succ * retainedPassiveSourceStagedSuccessorA3 (ρ := ρ) (κ' := κ') v q := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
  induction q using Fin.lastCases with
  | last =>
      have hF2 : coord.F2 (Fin.last (M + 1)) = 0 := by
        simp [coord, ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.toCoordinateData]
      have hF2' : coord.F2 (Fin.last M).succ = 0 := by
        simpa using hF2
      change coord.F2 (Fin.last M).succ *
          rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') ((fderiv ℝ raw z) v)
            (Fin.last M) =
        coord.F2 (Fin.last M).succ *
          retainedPassiveSourceStagedSuccessorA3 (ρ := ρ) (κ' := κ') v (Fin.last M)
      rw [hF2']
      rw [Matrix.zero_mul, Matrix.zero_mul]
  | cast p =>
      have hA3 :=
        rawEdgeTupleA3_fderiv_topologyTupleEdgeRawOrder_castSucc_eq_formalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') hz v p
      change coord.F2 p.castSucc.succ *
          rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') ((fderiv ℝ raw z) v)
            p.castSucc =
        coord.F2 p.castSucc.succ *
          retainedPassiveSourceStagedSuccessorA3 (ρ := ρ) (κ' := κ') v p.castSucc
      rw [hA3]
      dsimp [retainedPassiveFormalRawOrderJacobianAt]
      rw [retainedPassiveFormalRawOrderJacobian_apply]
      simp

set_option linter.style.longLine false in
/-- The passive top-left branch can be staged using the target-recovered
successor `F2` family and the raw lower-left target readout.  The terminal
lower-left target readout is used only under the terminal zero extended `F2`
multiplier. -/
theorem A1passive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) (p : Fin M) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
    let Dzv := (fderiv ℝ raw z) v
    let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
    Dzv.1 p
      - XsuccF2 p.succ * coord.solvedA3 p.succ
      - coord.F2 p.succ.succ *
          rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv p.succ =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).1 p := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
  let XsourceF2 := retainedPassiveSourceStagedSuccessorF2 (ρ := ρ) (κ' := κ') v
  let XsourceA3 := retainedPassiveSourceStagedSuccessorA3 (ρ := ρ) (κ' := κ') v
  have hsource :=
    A1passive_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (ρ := ρ) (κ' := κ') hz v p
  have hF2 :=
    retainedPassiveTargetRecoveredSuccessorF2At_fderiv_eq_sourceStagedSuccessorF2
      (ρ := ρ) (κ' := κ') hz v
  have hA3 :=
    retainedPassive_F2_succ_mul_rawEdgeTupleA3_fderiv_eq_sourceStagedSuccessorA3
      (ρ := ρ) (κ' := κ') hz v p.succ
  change XsuccF2 = XsourceF2 at hF2
  change coord.F2 p.succ.succ *
          rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv p.succ =
        coord.F2 p.succ.succ * XsourceA3 p.succ at hA3
  change Dzv.1 p
      - XsourceF2 p.succ * coord.solvedA3 p.succ
      - coord.F2 p.succ.succ * XsourceA3 p.succ =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).1 p at hsource
  change Dzv.1 p
      - XsuccF2 p.succ * coord.solvedA3 p.succ
      - coord.F2 p.succ.succ *
          rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv p.succ =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).1 p
  rw [hF2]
  rw [hA3]
  exact hsource

set_option linter.style.longLine false in
/-- The target-staged passive top-left branch recovers the source passive
`A1` tangent by projection from the point-specialized formal raw-order map. -/
theorem A1passive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_A1passive
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) (p : Fin M) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
    let Dzv := (fderiv ℝ raw z) v
    let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
    Dzv.1 p
      - XsuccF2 p.succ * coord.solvedA3 p.succ
      - coord.F2 p.succ.succ *
          rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv p.succ =
      v.1 p := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
  have hA1 :=
    A1passive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (ρ := ρ) (κ' := κ') hz v p
  have hrec :=
    retainedPassiveFormalRawOrderJacobianAt_recovers_A1passive
      (ρ := ρ) (κ' := κ') z v p
  change Dzv.1 p
      - XsuccF2 p.succ * coord.solvedA3 p.succ
      - coord.F2 p.succ.succ *
          rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv p.succ =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).1 p at hA1
  change Dzv.1 p
      - XsuccF2 p.succ * coord.solvedA3 p.succ
      - coord.F2 p.succ.succ *
          rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv p.succ =
      v.1 p
  rw [hA1]
  simpa using hrec

set_option maxRecDepth 2048 in
/-- The derivative of the inverse passive top-left tail is the matrix-inverse
derivative applied to the actual Frechet derivative of the tail map. -/
theorem fderiv_retainedPassive_A1TailAfterFirst_inv_eq_tail_fderiv
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Finite (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let Tail :=
      ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
        data.A1seed
    let dTail :=
      (fderiv ℝ
        (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
          ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed) z) v
    (fderiv ℝ
      (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
        (ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed)⁻¹) z) v =
      -(Tail⁻¹ * dTail * Tail⁻¹) := by
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let _ : ∀ j, Fintype (κ' j) := fun j ↦ Fintype.ofFinite (κ' j)
  let Tfun : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ → Matrix ρ ρ ℝ :=
    fun y ↦ ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
      (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
  have hTdiff : DifferentiableAt ℝ Tfun z := by
    simpa [Tfun] using
      differentiableAt_retainedPassiveA1TailAfterFirst (ρ := ρ) (κ' := κ') z
  have hdet : data.detChart := hz
  have hTailUnit : IsUnit (Tfun z).det := by
    change IsUnit
      (ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
        data.A1seed).det
    exact
      ChartLocalSuffixState.retainedPassiveA1TailAfterFirst_det_isUnit_of_passive
        (K := ℝ) (ρ := ρ) data.A1seed
        (data.toCoordinateData_passiveA1_units hdet.2)
  have hInvHas : HasFDerivAt
      (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦ (Tfun y)⁻¹)
      ((-(ContinuousLinearMap.mulLeftRight ℝ (Matrix ρ ρ ℝ)
          (Tfun z)⁻¹ (Tfun z)⁻¹)).comp
        (fderiv ℝ Tfun z)) z := by
    simpa [Tfun, Function.comp_def] using
      ((hasFDerivAt_matrix_inv_of_isUnit_det (Tfun z) hTailUnit).comp
        (x := z) hTdiff.hasFDerivAt)
  have hInvFDeriv :
      fderiv ℝ
          (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦ (Tfun y)⁻¹) z =
        ((-(ContinuousLinearMap.mulLeftRight ℝ (Matrix ρ ρ ℝ)
          (Tfun z)⁻¹ (Tfun z)⁻¹)).comp
        (fderiv ℝ Tfun z)) :=
    hInvHas.fderiv
  change
    (fderiv ℝ
      (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦ (Tfun y)⁻¹) z) v =
      -((Tfun z)⁻¹ * (fderiv ℝ Tfun z) v * (Tfun z)⁻¹)
  rw [hInvFDeriv]
  simp [ContinuousLinearMap.mulLeftRight_apply]

set_option linter.style.longLine false in
/-- The first top-left branch can be source-staged in the successor `F2`
and multiplied successor lower-left terms, leaving the passive-tail inverse
derivative term explicit. -/
theorem Ctop_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    let dTailInv :=
      (fderiv ℝ
        (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
          (ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed)⁻¹) z) v
    let XsuccF2 := retainedPassiveSourceStagedSuccessorF2 (ρ := ρ) (κ' := κ') v
    let XsuccA3 := retainedPassiveSourceStagedSuccessorA3 (ρ := ρ) (κ' := κ') v
    ((fderiv ℝ raw z) v).2.2.2.2.1
      - XsuccF2 0 * coord.solvedA3 0
      - coord.F2 (0 : Fin (M + 1)).succ * XsuccA3 0
      - dTailInv * coord.Ctop =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.1 := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  let dTailInv :=
    (fderiv ℝ
      (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
        (ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed)⁻¹) z) v
  let XsuccF2 := retainedPassiveSourceStagedSuccessorF2 (ρ := ρ) (κ' := κ') v
  let XsuccA3 := retainedPassiveSourceStagedSuccessorA3 (ρ := ρ) (κ' := κ') v
  have hCtop :=
    Ctop_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (ρ := ρ) (κ' := κ') hz v
  have hF2 :=
    fderiv_retainedPassive_toCoordinateData_F2_succ_apply
      (ρ := ρ) (κ' := κ') z v (0 : Fin (M + 1))
  have hA3 :=
    retainedPassive_F2_succ_mul_fderiv_solvedA3_eq_sourceStagedSuccessorA3
      (ρ := ρ) (κ' := κ') z v (0 : Fin (M + 1))
  change ((fderiv ℝ raw z) v).2.2.2.2.1
      - (fderiv ℝ
          (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
              (0 : Fin (M + 1)).succ) z) v *
          coord.solvedA3 0
      - coord.F2 (0 : Fin (M + 1)).succ *
          (fderiv ℝ
            (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.solvedA3
                0) z) v
      - (fderiv ℝ
          (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
            (ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed)⁻¹) z) v *
          coord.Ctop =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.1 at hCtop
  change coord.F2 (0 : Fin (M + 1)).succ *
          (fderiv ℝ
            (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.solvedA3
                0) z) v =
        coord.F2 (0 : Fin (M + 1)).succ * XsuccA3 0 at hA3
  rw [hF2] at hCtop
  rw [hA3] at hCtop
  simpa [XsuccF2, XsuccA3, dTailInv] using hCtop

set_option linter.style.longLine false in
/-- Substitute the inverse-tail derivative formula into the source-staged first
top-left branch, leaving the actual tail derivative unexpanded. -/
theorem Ctop_tail_fderiv_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    let Tfun : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ → Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
    let Tail :=
      ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
        data.A1seed
    let dTail := (fderiv ℝ Tfun z) v
    let XsuccF2 := retainedPassiveSourceStagedSuccessorF2 (ρ := ρ) (κ' := κ') v
    let XsuccA3 := retainedPassiveSourceStagedSuccessorA3 (ρ := ρ) (κ' := κ') v
    ((fderiv ℝ raw z) v).2.2.2.2.1
      - XsuccF2 0 * coord.solvedA3 0
      - coord.F2 (0 : Fin (M + 1)).succ * XsuccA3 0
      + Tail⁻¹ * dTail * Tail⁻¹ * coord.Ctop =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.1 := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  let Tfun : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ → Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
  let Tail :=
    ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
      data.A1seed
  let dTail := (fderiv ℝ Tfun z) v
  let XsuccF2 := retainedPassiveSourceStagedSuccessorF2 (ρ := ρ) (κ' := κ') v
  let XsuccA3 := retainedPassiveSourceStagedSuccessorA3 (ρ := ρ) (κ' := κ') v
  have hCtop :=
    Ctop_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (ρ := ρ) (κ' := κ') hz v
  have hInv :=
    fderiv_retainedPassive_A1TailAfterFirst_inv_eq_tail_fderiv
      (ρ := ρ) (κ' := κ') hz v
  change ((fderiv ℝ raw z) v).2.2.2.2.1
      - XsuccF2 0 * coord.solvedA3 0
      - coord.F2 (0 : Fin (M + 1)).succ * XsuccA3 0
      - (fderiv ℝ
          (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
            (Tfun y)⁻¹) z) v * coord.Ctop =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.1 at hCtop
  change
    (fderiv ℝ
      (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
        (Tfun y)⁻¹) z) v =
      -(Tail⁻¹ * dTail * Tail⁻¹) at hInv
  rw [hInv] at hCtop
  simpa [Tfun, Tail, dTail, neg_mul, sub_neg_eq_add, Matrix.mul_assoc] using hCtop

set_option linter.style.longLine false in
/-- In the single-edge case, the tail derivative term in the source-staged
first top-left branch vanishes because the tail after the first edge is empty. -/
theorem Ctop_tail_zero_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
    {ρ : Type*} {κ' : Fin 2 → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := 0) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := 0) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    let XsuccF2 := retainedPassiveSourceStagedSuccessorF2 (ρ := ρ) (κ' := κ') v
    let XsuccA3 := retainedPassiveSourceStagedSuccessorA3 (ρ := ρ) (κ' := κ') v
    ((fderiv ℝ raw z) v).2.2.2.2.1
      - XsuccF2 0 * coord.solvedA3 0
      - coord.F2 (0 : Fin 1).succ * XsuccA3 0 =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.1 := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  let Tfun : RetainedPassiveRawTopologyTuple (M := 0) ρ κ' ℝ → Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
  let Tail :=
    ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
      data.A1seed
  let dTail := (fderiv ℝ Tfun z) v
  let XsuccF2 := retainedPassiveSourceStagedSuccessorF2 (ρ := ρ) (κ' := κ') v
  let XsuccA3 := retainedPassiveSourceStagedSuccessorA3 (ρ := ρ) (κ' := κ') v
  have hCtop :=
    Ctop_tail_fderiv_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (ρ := ρ) (κ' := κ') hz v
  have hTailZero :=
    fderiv_retainedPassive_A1TailAfterFirst_zero_apply
      (ρ := ρ) (κ' := κ') z v
  have hdTail : dTail = 0 := by
    simpa [dTail, Tfun] using hTailZero
  change ((fderiv ℝ raw z) v).2.2.2.2.1
      - XsuccF2 0 * coord.solvedA3 0
      - coord.F2 (0 : Fin 1).succ * XsuccA3 0
      + Tail⁻¹ * dTail * Tail⁻¹ * coord.Ctop =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.1 at hCtop
  rw [hdTail] at hCtop
  simpa [Tail, dTail, add_assoc] using hCtop

set_option linter.style.longLine false in
/-- For positive tail length, substitute the first passive suffix-product
recurrence for `dTail` in the source-staged first top-left branch. -/
theorem Ctop_tail_pos_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (hM : 0 < M)
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    let Tail :=
      ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
        data.A1seed
    let q : Fin M := ⟨0, hM⟩
    let p : Fin (M + 1) := q.succ
    let Psucc : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ → Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ)
          (κ := fun _ : Fin (M + 2) ↦ ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
          (Fin.last (M + 1)) p.succ p.succ.le_last
    let XsuccF2 := retainedPassiveSourceStagedSuccessorF2 (ρ := ρ) (κ' := κ') v
    let XsuccA3 := retainedPassiveSourceStagedSuccessorA3 (ρ := ρ) (κ' := κ') v
    ((fderiv ℝ raw z) v).2.2.2.2.1
      - XsuccF2 0 * coord.solvedA3 0
      - coord.F2 (0 : Fin (M + 1)).succ * XsuccA3 0
      + Tail⁻¹ * ((fderiv ℝ Psucc z) v * data.A1seed p + Psucc z * v.1 q) *
          Tail⁻¹ * coord.Ctop =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.1 := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  let Tfun : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ → Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
  let Tail :=
    ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
      data.A1seed
  let dTail := (fderiv ℝ Tfun z) v
  let q : Fin M := ⟨0, hM⟩
  let p : Fin (M + 1) := q.succ
  let Psucc : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ → Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ)
        (κ := fun _ : Fin (M + 2) ↦ ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
        (Fin.last (M + 1)) p.succ p.succ.le_last
  let XsuccF2 := retainedPassiveSourceStagedSuccessorF2 (ρ := ρ) (κ' := κ') v
  let XsuccA3 := retainedPassiveSourceStagedSuccessorA3 (ρ := ρ) (κ' := κ') v
  have hCtop :=
    Ctop_tail_fderiv_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (ρ := ρ) (κ' := κ') hz v
  have hTail :=
    fderiv_retainedPassive_A1TailAfterFirst_pos_apply
      (M := M) (ρ := ρ) (κ' := κ') hM z v
  have hdTail :
      dTail = (fderiv ℝ Psucc z) v * data.A1seed p + Psucc z * v.1 q := by
    simpa [dTail, Tfun, Psucc, q, p] using hTail
  change ((fderiv ℝ raw z) v).2.2.2.2.1
      - XsuccF2 0 * coord.solvedA3 0
      - coord.F2 (0 : Fin (M + 1)).succ * XsuccA3 0
      + Tail⁻¹ * dTail * Tail⁻¹ * coord.Ctop =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.1 at hCtop
  rw [hdTail] at hCtop
  simpa [Tfun, Tail, dTail, q, p, Psucc, add_assoc] using hCtop

set_option linter.style.longLine false in
/-- In the single-edge case, the source-staged first top-left branch recovers
the source `Ctop` tangent after multiplication by the passive tail. -/
theorem Ctop_tail_zero_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop
    {ρ : Type*} {κ' : Fin 2 → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := 0) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := 0) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    let Tail :=
      ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
        data.A1seed
    let XsuccF2 := retainedPassiveSourceStagedSuccessorF2 (ρ := ρ) (κ' := κ') v
    let XsuccA3 := retainedPassiveSourceStagedSuccessorA3 (ρ := ρ) (κ' := κ') v
    Tail *
      (((fderiv ℝ raw z) v).2.2.2.2.1
        - XsuccF2 0 * coord.solvedA3 0
        - coord.F2 (0 : Fin 1).succ * XsuccA3 0) =
      v.2.2.2.2.1 := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  let Tail :=
    ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
      data.A1seed
  let XsuccF2 := retainedPassiveSourceStagedSuccessorF2 (ρ := ρ) (κ' := κ') v
  let XsuccA3 := retainedPassiveSourceStagedSuccessorA3 (ρ := ρ) (κ' := κ') v
  have hCtop :=
    Ctop_tail_zero_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (ρ := ρ) (κ' := κ') hz v
  have hrec :=
    retainedPassiveFormalRawOrderJacobianAt_recovers_Ctop
      (ρ := ρ) (κ' := κ') hz v
  change Tail *
      (((fderiv ℝ raw z) v).2.2.2.2.1
        - XsuccF2 0 * coord.solvedA3 0
        - coord.F2 (0 : Fin 1).succ * XsuccA3 0) =
      v.2.2.2.2.1
  change ((fderiv ℝ raw z) v).2.2.2.2.1
      - XsuccF2 0 * coord.solvedA3 0
      - coord.F2 (0 : Fin 1).succ * XsuccA3 0 =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.1 at hCtop
  rw [hCtop]
  simpa [Tail, data] using hrec

set_option linter.style.longLine false in
/-- For positive passive-tail length, the source-staged first top-left branch
with the first tail-derivative recurrence substituted recovers the source
`Ctop` tangent after multiplication by the passive tail. -/
theorem Ctop_tail_pos_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (hM : 0 < M)
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    let Tail :=
      ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
        data.A1seed
    let q : Fin M := ⟨0, hM⟩
    let p : Fin (M + 1) := q.succ
    let Psucc : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ → Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ)
          (κ := fun _ : Fin (M + 2) ↦ ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
          (Fin.last (M + 1)) p.succ p.succ.le_last
    let XsuccF2 := retainedPassiveSourceStagedSuccessorF2 (ρ := ρ) (κ' := κ') v
    let XsuccA3 := retainedPassiveSourceStagedSuccessorA3 (ρ := ρ) (κ' := κ') v
    Tail *
      (((fderiv ℝ raw z) v).2.2.2.2.1
        - XsuccF2 0 * coord.solvedA3 0
        - coord.F2 (0 : Fin (M + 1)).succ * XsuccA3 0
        + Tail⁻¹ * ((fderiv ℝ Psucc z) v * data.A1seed p + Psucc z * v.1 q) *
            Tail⁻¹ * coord.Ctop) =
      v.2.2.2.2.1 := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  let Tail :=
    ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
      data.A1seed
  let q : Fin M := ⟨0, hM⟩
  let p : Fin (M + 1) := q.succ
  let Psucc : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ → Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ)
        (κ := fun _ : Fin (M + 2) ↦ ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
        (Fin.last (M + 1)) p.succ p.succ.le_last
  let XsuccF2 := retainedPassiveSourceStagedSuccessorF2 (ρ := ρ) (κ' := κ') v
  let XsuccA3 := retainedPassiveSourceStagedSuccessorA3 (ρ := ρ) (κ' := κ') v
  have hCtop :=
    Ctop_tail_pos_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (ρ := ρ) (κ' := κ') hM hz v
  have hrec :=
    retainedPassiveFormalRawOrderJacobianAt_recovers_Ctop
      (ρ := ρ) (κ' := κ') hz v
  change Tail *
      (((fderiv ℝ raw z) v).2.2.2.2.1
        - XsuccF2 0 * coord.solvedA3 0
        - coord.F2 (0 : Fin (M + 1)).succ * XsuccA3 0
        + Tail⁻¹ * ((fderiv ℝ Psucc z) v * data.A1seed p + Psucc z * v.1 q) *
            Tail⁻¹ * coord.Ctop) =
      v.2.2.2.2.1
  change ((fderiv ℝ raw z) v).2.2.2.2.1
      - XsuccF2 0 * coord.solvedA3 0
      - coord.F2 (0 : Fin (M + 1)).succ * XsuccA3 0
      + Tail⁻¹ * ((fderiv ℝ Psucc z) v * data.A1seed p + Psucc z * v.1 q) *
          Tail⁻¹ * coord.Ctop =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.1 at hCtop
  rw [hCtop]
  simpa [Tail, data] using hrec

set_option linter.style.longLine false in
/-- The terminal lower-left branch recovers the source `F3` tangent after
right-multiplication by the inverse of the negative terminal solved top-left
factor. -/
theorem F3_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let A1fun : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →
        Fin (M + 1) → Matrix ρ ρ ℝ :=
      fun y p ↦
        ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p
    let Earlyfun : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →
        Matrix (κ' (Fin.last (M + 1))) ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
          (K := ℝ) (ρ := ρ) (κ := κ')
          (A1fun y)
          (ChartLocalSuffixState.retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
          0 (Nat.zero_le (M + 1))
    let Lastfun : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct
          (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          (A1fun y) (Fin.last (M + 1)) (Fin.last M).castSucc
            (Fin.last M).castSucc.le_last
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    (((fderiv ℝ raw z) v).2.2.2.2.2
      - (fderiv ℝ Earlyfun z) v * Lastfun z
      + (coord.F3 - Earlyfun z) * (fderiv ℝ Lastfun z) v) *
        (-(coord.solvedA1 (Fin.last M)))⁻¹ =
      v.2.2.2.2.2 := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let A1fun : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →
      Fin (M + 1) → Matrix ρ ρ ℝ :=
    fun y p ↦
      ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p
  let Earlyfun : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →
      Matrix (κ' (Fin.last (M + 1))) ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
        (K := ℝ) (ρ := ρ) (κ := κ')
        (A1fun y)
        (ChartLocalSuffixState.retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
        0 (Nat.zero_le (M + 1))
  let Lastfun : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct
        (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
        (A1fun y) (Fin.last (M + 1)) (Fin.last M).castSucc
          (Fin.last M).castSucc.le_last
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  have hF3 :=
    F3_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (ρ := ρ) (κ' := κ') hz v
  have hrec :=
    retainedPassiveFormalRawOrderJacobianAt_recovers_F3
      (ρ := ρ) (κ' := κ') hz v
  change (((fderiv ℝ raw z) v).2.2.2.2.2
      - (fderiv ℝ Earlyfun z) v * Lastfun z
      + (coord.F3 - Earlyfun z) * (fderiv ℝ Lastfun z) v) *
        (-(coord.solvedA1 (Fin.last M)))⁻¹ =
      v.2.2.2.2.2
  change ((fderiv ℝ raw z) v).2.2.2.2.2
      - (fderiv ℝ Earlyfun z) v * Lastfun z
      + (coord.F3 - Earlyfun z) * (fderiv ℝ Lastfun z) v =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.2 at hF3
  rw [hF3]
  simpa [coord, data] using hrec

end Aoyagi
end DLN
end DLNFibre
