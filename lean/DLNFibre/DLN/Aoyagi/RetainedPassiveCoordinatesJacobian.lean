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

/-- Conditional determinant bridge from the actual retained-passive raw-order
Frechet derivative to the point-specialized formal raw-order Jacobian.

The hypothesis is intentionally a supplied target-side linear equivalence with
absolute determinant one.  This theorem does not construct that equivalence. -/
theorem topologyTupleEdgeRawOrderFDerivAbsDet_eq_formalRawOrderAbsDetAt_of_target_linearEquiv
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)
    (T :
      RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ≃ₗ[ℝ]
        RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)
    (hT :
      ∀ v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ,
        T ((fderiv ℝ
          (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')) z) v) =
          (retainedPassiveFormalRawOrderJacobianAt
            (ρ := ρ) (κ' := κ') z) v)
    (hdetT :
      |LinearMap.det
        (T : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
          RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)| = 1) :
    topologyTupleEdgeRawOrderFDerivAbsDet
        (ρ := ρ) (κ' := κ') z =
      retainedPassiveFormalRawOrderJacobianAbsDetAt
        (ρ := ρ) (κ' := κ') z := by
  let E : Type _ := RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ
  let raw : E → E :=
    topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let D : E →ₗ[ℝ] E :=
    ((fderiv ℝ raw z : E →L[ℝ] E) : E →ₗ[ℝ] E)
  let F : E →ₗ[ℝ] E :=
    retainedPassiveFormalRawOrderJacobianAt (ρ := ρ) (κ' := κ') z
  have hF : F = (T : E →ₗ[ℝ] E).comp D := by
    apply LinearMap.ext
    intro v
    simpa [E, raw, D, F, LinearMap.comp_apply] using (hT v).symm
  have hdetTE : |LinearMap.det (T : E →ₗ[ℝ] E)| = 1 := by
    simpa [E] using hdetT
  have hdetF :
      LinearMap.det F =
        LinearMap.det (T : E →ₗ[ℝ] E) * LinearMap.det D := by
    rw [hF, LinearMap.det_comp]
  rw [topologyTupleEdgeRawOrderFDerivAbsDet,
    retainedPassiveFormalRawOrderJacobianAbsDetAt]
  change |LinearMap.det D| = |LinearMap.det F|
  rw [hdetF, abs_mul, hdetTE, one_mul]

/-- Product-form version of the conditional retained-passive
determinant/Jacobian bridge.

The target-side determinant-one linear equivalence remains a hypothesis; the
right-hand side is only the already-proved formal raw-order product
determinant. -/
theorem topologyTupleEdgeRawOrderFDerivAbsDet_product_eq_of_target_linearEquiv
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)
    (T :
      RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ≃ₗ[ℝ]
        RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)
    (hT :
      ∀ v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ,
        T ((fderiv ℝ
          (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')) z) v) =
          (retainedPassiveFormalRawOrderJacobianAt
            (ρ := ρ) (κ' := κ') z) v)
    (hdetT :
      |LinearMap.det
        (T : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
          RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)| = 1) :
    let data :
        ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
          (K := ℝ) (ρ := ρ) κ' :=
      ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.ofTopologyTuple
        (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord :
        ChartLocalSuffixState.RetainedPassiveCoordinateData
          (K := ℝ) (ρ := ρ) κ' :=
      data.toCoordinateData
    topologyTupleEdgeRawOrderFDerivAbsDet
        (ρ := ρ) (κ' := κ') z =
      |((ChartLocalSuffixState.retainedPassiveA1TailAfterFirst
          (K := ℝ) (ρ := ρ) data.A1seed)⁻¹).det| ^ Fintype.card ρ *
        (∏ p : Fin (M + 1),
          |(coord.solvedA1 p).det| ^ Fintype.card (κ' p.castSucc)) *
          |(coord.solvedA1 (Fin.last M)).det| ^
            Fintype.card (κ' (Fin.last (M + 1))) := by
  calc
    topologyTupleEdgeRawOrderFDerivAbsDet
        (ρ := ρ) (κ' := κ') z =
      retainedPassiveFormalRawOrderJacobianAbsDetAt
        (ρ := ρ) (κ' := κ') z := by
        exact
          topologyTupleEdgeRawOrderFDerivAbsDet_eq_formalRawOrderAbsDetAt_of_target_linearEquiv
            (ρ := ρ) (κ' := κ') z T hT hdetT
    _ =
      (let data :
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := ρ) κ' :=
        ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.ofTopologyTuple
          (K := ℝ) (ρ := ρ) (κ' := κ') z
      let coord :
          ChartLocalSuffixState.RetainedPassiveCoordinateData
            (K := ℝ) (ρ := ρ) κ' :=
        data.toCoordinateData
      |((ChartLocalSuffixState.retainedPassiveA1TailAfterFirst
          (K := ℝ) (ρ := ρ) data.A1seed)⁻¹).det| ^ Fintype.card ρ *
        (∏ p : Fin (M + 1),
          |(coord.solvedA1 p).det| ^ Fintype.card (κ' p.castSucc)) *
          |(coord.solvedA1 (Fin.last M)).det| ^
            Fintype.card (κ' (Fin.last (M + 1)))) := by
        simpa using
          retainedPassiveFormalRawOrderJacobianAbsDetAt_eq
            (ρ := ρ) (κ' := κ') z

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

section TargetEdgePairLinearMap

/-- Right multiplication by a fixed rectangular matrix, as a linear map. -/
private def retainedPassiveMatrixMulRightLinearMap
    {l m n : Type*} [Fintype m] (B : Matrix m n ℝ) :
    Matrix l m ℝ →ₗ[ℝ] Matrix l n ℝ where
  toFun A := A * B
  map_add' A A' := by
    ext i j
    simp [Matrix.add_mul]
  map_smul' a A := by
    ext i j
    simp [Matrix.mul_apply, Finset.mul_sum, mul_assoc]

/-- Left multiplication by a fixed rectangular matrix, as a linear map. -/
private def retainedPassiveMatrixMulLeftLinearMap
    {l m n : Type*} [Fintype m] (A : Matrix l m ℝ) :
    Matrix m n ℝ →ₗ[ℝ] Matrix l n ℝ where
  toFun B := A * B
  map_add' B B' := by
    ext i j
    simp [Matrix.mul_add]
  map_smul' a B := by
    ext i j
    simp [Matrix.mul_apply, Finset.mul_sum, mul_left_comm]

@[simp]
private theorem retainedPassiveMatrixMulRightLinearMap_apply
    {l m n : Type*} [Fintype m] (B : Matrix m n ℝ) (A : Matrix l m ℝ) :
    retainedPassiveMatrixMulRightLinearMap B A = A * B :=
  rfl

@[simp]
private theorem retainedPassiveMatrixMulLeftLinearMap_apply
    {l m n : Type*} [Fintype m] (A : Matrix l m ℝ) (B : Matrix m n ℝ) :
    retainedPassiveMatrixMulLeftLinearMap A B = A * B :=
  rfl

/-- Projection to the raw retained-passive `F2` component at one edge. -/
private def retainedPassiveRawF2LinearMapAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    (q : Fin (M + 1)) :
    RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
      Matrix ρ (κ' q.castSucc) ℝ where
  toFun w := w.2.1 q
  map_add' _w _w' := rfl
  map_smul' _a _w := rfl

/-- Projection to the raw retained-passive `C` component at one edge. -/
private def retainedPassiveRawCLinearMapAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    (q : Fin (M + 1)) :
    RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
      Matrix (κ' q.succ) (κ' q.castSucc) ℝ where
  toFun w := w.2.2.2.1 q
  map_add' _w _w' := rfl
  map_smul' _a _w := rfl

/-- Linear readout of the raw top-left edge block in endpoint order. -/
private def retainedPassiveRawEdgeTupleA1LinearMapAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    (q : Fin (M + 1)) :
    RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
      Matrix ρ ρ ℝ where
  toFun w := rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') w q
  map_add' w w' := by
    cases q using Fin.cases <;> rfl
  map_smul' a w := by
    cases q using Fin.cases <;> rfl

/-- Linear readout of the raw lower-left edge block in endpoint order. -/
private def retainedPassiveRawEdgeTupleA3LinearMapAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    (q : Fin (M + 1)) :
    RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
      Matrix (κ' q.succ) ρ ℝ where
  toFun w := rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') w q
  map_add' w w' := by
    cases q using Fin.lastCases
    · simp [rawEdgeTupleA3, ofTopologyTuple]
      rfl
    · simp [rawEdgeTupleA3, ofTopologyTuple]
  map_smul' a w := by
    cases q using Fin.lastCases
    · simp [rawEdgeTupleA3, ofTopologyTuple]
      rfl
    · simp [rawEdgeTupleA3, ofTopologyTuple]

@[simp] private theorem retainedPassiveRawF2LinearMapAt_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    (q : Fin (M + 1)) (w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    retainedPassiveRawF2LinearMapAt (ρ := ρ) (κ' := κ') q w = w.2.1 q := rfl

@[simp] private theorem retainedPassiveRawCLinearMapAt_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    (q : Fin (M + 1)) (w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    retainedPassiveRawCLinearMapAt (ρ := ρ) (κ' := κ') q w = w.2.2.2.1 q := rfl

@[simp] private theorem retainedPassiveRawEdgeTupleA1LinearMapAt_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    (q : Fin (M + 1)) (w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    retainedPassiveRawEdgeTupleA1LinearMapAt (ρ := ρ) (κ' := κ') q w =
      rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') w q := rfl

@[simp] private theorem retainedPassiveRawEdgeTupleA3LinearMapAt_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    (q : Fin (M + 1)) (w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    retainedPassiveRawEdgeTupleA3LinearMapAt (ρ := ρ) (κ' := κ') q w =
      rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') w q := rfl

set_option linter.style.longLine false in
/-- The terminal branch of the target-recovered `F2` recurrence, as a linear map. -/
private def retainedPassiveTargetRecoveredF2TerminalLinearMapAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
      Matrix ρ (κ' (Fin.last M).castSucc) ℝ :=
  let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
  let q : Fin (M + 1) := Fin.last M
  let dC : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
      Matrix (κ' q.succ) (κ' q.castSucc) ℝ :=
    retainedPassiveRawCLinearMapAt (ρ := ρ) (κ' := κ') q +
      (retainedPassiveMatrixMulRightLinearMap (coord.F2 q.castSucc)).comp
        (retainedPassiveRawEdgeTupleA3LinearMapAt (ρ := ρ) (κ' := κ') q)
  let dF : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
      Matrix ρ (κ' q.castSucc) ℝ :=
    retainedPassiveRawF2LinearMapAt (ρ := ρ) (κ' := κ') q +
      (retainedPassiveMatrixMulRightLinearMap (coord.F2 q.castSucc)).comp
        (retainedPassiveRawEdgeTupleA1LinearMapAt (ρ := ρ) (κ' := κ') q)
  (retainedPassiveMatrixMulLeftLinearMap (coord.solvedA1 q)⁻¹).comp
    ((retainedPassiveMatrixMulLeftLinearMap (coord.F2 q.succ)).comp dC - dF)

set_option linter.style.longLine false in
private theorem retainedPassiveTargetRecoveredF2TerminalLinearMapAt_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
    let q : Fin (M + 1) := Fin.last M
    retainedPassiveTargetRecoveredF2TerminalLinearMapAt (ρ := ρ) (κ' := κ') z w =
      (coord.solvedA1 q)⁻¹ *
        (coord.F2 q.succ *
            (w.2.2.2.1 q
              + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') w q *
                coord.F2 q.castSucc) -
          (w.2.1 q
            + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') w q *
              coord.F2 q.castSucc)) := by
  dsimp [retainedPassiveTargetRecoveredF2TerminalLinearMapAt,
    retainedPassiveMatrixMulLeftLinearMap, retainedPassiveMatrixMulRightLinearMap,
    retainedPassiveRawCLinearMapAt, retainedPassiveRawEdgeTupleA3LinearMapAt,
    retainedPassiveRawF2LinearMapAt, retainedPassiveRawEdgeTupleA1LinearMapAt]
  rfl

set_option linter.style.longLine false in
/-- One nonterminal branch of the target-recovered `F2` recurrence, as a linear map. -/
private def retainedPassiveTargetRecoveredF2StepLinearMapAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) (p : Fin M)
    (Xnext : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
      Matrix ρ (κ' ((p.succ : Fin (M + 1)).castSucc)) ℝ) :
    RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
      Matrix ρ (κ' ((p.castSucc : Fin (M + 1)).castSucc)) ℝ :=
  let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
  let q : Fin (M + 1) := p.castSucc
  let Xsucc : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
      Matrix ρ (κ' q.succ) ℝ :=
    (LinearEquiv.cast (R := ℝ)
      (M := fun i : Fin (M + 2) ↦ Matrix ρ (κ' i) ℝ)
      (Fin.succ_castSucc p).symm).toLinearMap.comp Xnext
  let dC : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
      Matrix (κ' q.succ) (κ' q.castSucc) ℝ :=
    retainedPassiveRawCLinearMapAt (ρ := ρ) (κ' := κ') q +
      (retainedPassiveMatrixMulRightLinearMap (coord.F2 q.castSucc)).comp
        (retainedPassiveRawEdgeTupleA3LinearMapAt (ρ := ρ) (κ' := κ') q)
  let dF : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
      Matrix ρ (κ' q.castSucc) ℝ :=
    retainedPassiveRawF2LinearMapAt (ρ := ρ) (κ' := κ') q +
      (retainedPassiveMatrixMulRightLinearMap (coord.F2 q.castSucc)).comp
        (retainedPassiveRawEdgeTupleA1LinearMapAt (ρ := ρ) (κ' := κ') q)
  (retainedPassiveMatrixMulLeftLinearMap (coord.solvedA1 q)⁻¹).comp
    ((retainedPassiveMatrixMulLeftLinearMap (coord.F2 q.succ)).comp dC -
      (dF - (retainedPassiveMatrixMulRightLinearMap (coord.C q)).comp Xsucc))

set_option linter.style.longLine false in
private theorem retainedPassiveTargetRecoveredF2StepLinearMapAt_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) (p : Fin M)
    (Xnext : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
      Matrix ρ (κ' ((p.succ : Fin (M + 1)).castSucc)) ℝ)
    (w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
    let q : Fin (M + 1) := p.castSucc
    let Xsucc : Matrix ρ (κ' q.succ) ℝ :=
      (LinearEquiv.cast (R := ℝ)
        (M := fun i : Fin (M + 2) ↦ Matrix ρ (κ' i) ℝ)
        (Fin.succ_castSucc p).symm) (Xnext w)
    retainedPassiveTargetRecoveredF2StepLinearMapAt (ρ := ρ) (κ' := κ') z p Xnext w =
      (coord.solvedA1 q)⁻¹ *
        (coord.F2 q.succ *
            (w.2.2.2.1 q
              + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') w q *
                coord.F2 q.castSucc) -
          (w.2.1 q
            + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') w q *
              coord.F2 q.castSucc
            - Xsucc * coord.C q)) := by
  dsimp [retainedPassiveTargetRecoveredF2StepLinearMapAt,
    retainedPassiveMatrixMulLeftLinearMap, retainedPassiveMatrixMulRightLinearMap,
    retainedPassiveRawCLinearMapAt, retainedPassiveRawEdgeTupleA3LinearMapAt,
    retainedPassiveRawF2LinearMapAt, retainedPassiveRawEdgeTupleA1LinearMapAt]
  rfl

set_option linter.style.longLine false in
/-- The target-recovered `F2` recurrence as a linear map in the target raw tuple. -/
def retainedPassiveTargetRecoveredF2LinearMapAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
      ∀ q : Fin (M + 1), Matrix ρ (κ' q.castSucc) ℝ :=
  LinearMap.pi fun q =>
    Fin.reverseInduction
      (motive := fun q : Fin (M + 1) =>
        RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
          Matrix ρ (κ' q.castSucc) ℝ)
      (retainedPassiveTargetRecoveredF2TerminalLinearMapAt (ρ := ρ) (κ' := κ') z)
      (fun p Xnext =>
        retainedPassiveTargetRecoveredF2StepLinearMapAt (ρ := ρ) (κ' := κ') z p Xnext)
      q

set_option linter.style.longLine false in
/-- The linear-map recovered `F2` recurrence agrees with the existing function. -/
theorem retainedPassiveTargetRecoveredF2LinearMapAt_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    retainedPassiveTargetRecoveredF2LinearMapAt (ρ := ρ) (κ' := κ') z w =
      retainedPassiveTargetRecoveredF2At (ρ := ρ) (κ' := κ') z w := by
  funext q
  induction q using Fin.reverseInduction with
  | last =>
      rw [retainedPassiveTargetRecoveredF2At_last]
      simpa [retainedPassiveTargetRecoveredF2LinearMapAt] using
        retainedPassiveTargetRecoveredF2TerminalLinearMapAt_apply
          (ρ := ρ) (κ' := κ') z w
  | cast p ih =>
      rw [retainedPassiveTargetRecoveredF2At_castSucc]
      have hleft :
          (retainedPassiveTargetRecoveredF2LinearMapAt
              (ρ := ρ) (κ' := κ') z) w p.castSucc =
            retainedPassiveTargetRecoveredF2StepLinearMapAt
              (ρ := ρ) (κ' := κ') z p
              (Fin.reverseInduction
                (motive := fun q : Fin (M + 1) =>
                  RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
                    Matrix ρ (κ' q.castSucc) ℝ)
                (retainedPassiveTargetRecoveredF2TerminalLinearMapAt
                  (ρ := ρ) (κ' := κ') z)
                (fun p Xnext =>
                  retainedPassiveTargetRecoveredF2StepLinearMapAt
                    (ρ := ρ) (κ' := κ') z p Xnext)
                p.succ) w := by
        simp [retainedPassiveTargetRecoveredF2LinearMapAt]
      rw [hleft]
      rw [retainedPassiveTargetRecoveredF2StepLinearMapAt_apply]
      have hnext :
          (Fin.reverseInduction
            (motive := fun q : Fin (M + 1) =>
              RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
                Matrix ρ (κ' q.castSucc) ℝ)
            (retainedPassiveTargetRecoveredF2TerminalLinearMapAt
              (ρ := ρ) (κ' := κ') z)
            (fun p Xnext =>
              retainedPassiveTargetRecoveredF2StepLinearMapAt
                (ρ := ρ) (κ' := κ') z p Xnext)
            p.succ) w =
            retainedPassiveTargetRecoveredF2At (ρ := ρ) (κ' := κ') z w p.succ := by
        simpa [retainedPassiveTargetRecoveredF2LinearMapAt] using ih
      rw [hnext]

set_option linter.style.longLine false in
/-- The target-recovered successor `F2` family as a linear map. -/
def retainedPassiveTargetRecoveredSuccessorF2LinearMapAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
      ∀ q : Fin (M + 1), Matrix ρ (κ' q.succ) ℝ :=
  LinearMap.pi fun q =>
    Fin.lastCases
      (motive := fun q : Fin (M + 1) =>
        RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
          Matrix ρ (κ' q.succ) ℝ)
      (0 : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
        Matrix ρ (κ' (Fin.last M).succ) ℝ)
      (fun p =>
        (LinearEquiv.cast (R := ℝ)
          (M := fun i : Fin (M + 2) ↦ Matrix ρ (κ' i) ℝ)
          (Fin.succ_castSucc p).symm).toLinearMap.comp
            ((LinearMap.proj p.succ).comp
              (retainedPassiveTargetRecoveredF2LinearMapAt
                (ρ := ρ) (κ' := κ') z)))
      q

set_option linter.style.longLine false in
/-- The successor `F2` linear map agrees with the existing successor function. -/
theorem retainedPassiveTargetRecoveredSuccessorF2LinearMapAt_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    retainedPassiveTargetRecoveredSuccessorF2LinearMapAt
        (ρ := ρ) (κ' := κ') z w =
      retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z w := by
  funext q
  induction q using Fin.lastCases with
  | last =>
      simp [retainedPassiveTargetRecoveredSuccessorF2LinearMapAt,
        retainedPassiveTargetRecoveredSuccessorF2At]
      rfl
  | cast p =>
      simp [retainedPassiveTargetRecoveredSuccessorF2LinearMapAt,
        retainedPassiveTargetRecoveredSuccessorF2At,
        retainedPassiveTargetRecoveredF2LinearMapAt_apply]
      rfl

set_option linter.style.longLine false in
/-- Target-side all-edge `(F2,C)` shear as a linear map in the target raw tuple. -/
def retainedPassiveTargetEdgePairShearLinearMapAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
      ((∀ q : Fin (M + 1), Matrix ρ (κ' q.castSucc) ℝ) ×
        (∀ q : Fin (M + 1), Matrix (κ' q.succ) (κ' q.castSucc) ℝ)) :=
  let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
  let Xsucc := retainedPassiveTargetRecoveredSuccessorF2LinearMapAt
    (ρ := ρ) (κ' := κ') z
  let Fmap : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
      ∀ q : Fin (M + 1), Matrix ρ (κ' q.castSucc) ℝ :=
    LinearMap.pi fun q =>
      retainedPassiveRawF2LinearMapAt (ρ := ρ) (κ' := κ') q +
        (retainedPassiveMatrixMulRightLinearMap (coord.F2 q.castSucc)).comp
          (retainedPassiveRawEdgeTupleA1LinearMapAt (ρ := ρ) (κ' := κ') q) -
        (retainedPassiveMatrixMulRightLinearMap (coord.C q)).comp
          ((LinearMap.proj q).comp Xsucc)
  let Cmap : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
      ∀ q : Fin (M + 1), Matrix (κ' q.succ) (κ' q.castSucc) ℝ :=
    LinearMap.pi fun q =>
      retainedPassiveRawCLinearMapAt (ρ := ρ) (κ' := κ') q +
        (retainedPassiveMatrixMulRightLinearMap (coord.F2 q.castSucc)).comp
          (retainedPassiveRawEdgeTupleA3LinearMapAt (ρ := ρ) (κ' := κ') q)
  Fmap.prod Cmap

set_option linter.style.longLine false in
/-- The edge-pair shear linear map agrees with the existing target-side function. -/
theorem retainedPassiveTargetEdgePairShearLinearMapAt_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    retainedPassiveTargetEdgePairShearLinearMapAt (ρ := ρ) (κ' := κ') z w =
      retainedPassiveTargetEdgePairShearAt (ρ := ρ) (κ' := κ') z w := by
  apply Prod.ext
  · funext q
    simp [retainedPassiveTargetEdgePairShearLinearMapAt,
      retainedPassiveTargetEdgePairShearAt, retainedPassiveMatrixMulRightLinearMap,
      retainedPassiveRawF2LinearMapAt, retainedPassiveRawEdgeTupleA1LinearMapAt,
      retainedPassiveTargetRecoveredSuccessorF2LinearMapAt_apply,
      LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply]
  · funext q
    simp [retainedPassiveTargetEdgePairShearLinearMapAt,
      retainedPassiveTargetEdgePairShearAt, retainedPassiveMatrixMulRightLinearMap,
      retainedPassiveRawCLinearMapAt, retainedPassiveRawEdgeTupleA3LinearMapAt,
      LinearMap.add_apply, LinearMap.comp_apply]

private abbrev retainedPassiveRawF2Family
    {M : ℕ} (ρ : Type*) (κ' : Fin (M + 2) → Type*) :=
  ∀ q : Fin (M + 1), Matrix ρ (κ' q.castSucc) ℝ

private abbrev retainedPassiveRawCFamily
    {M : ℕ} (κ' : Fin (M + 2) → Type*) :=
  ∀ q : Fin (M + 1), Matrix (κ' q.succ) (κ' q.castSucc) ℝ

private abbrev retainedPassiveRawF2CFamily
    {M : ℕ} (ρ : Type*) (κ' : Fin (M + 2) → Type*) :=
  retainedPassiveRawF2Family (M := M) ρ κ' ×
    retainedPassiveRawCFamily (M := M) κ'

private abbrev retainedPassiveRawF2SuccessorFamily
    {M : ℕ} (ρ : Type*) (κ' : Fin (M + 2) → Type*) :=
  ∀ q : Fin (M + 1), Matrix ρ (κ' q.succ) ℝ

private abbrev retainedPassiveRawA1PassiveFamily
    {M : ℕ} (ρ : Type*) :=
  Fin M → Matrix ρ ρ ℝ

private abbrev retainedPassiveRawA3PassiveFamily
    {M : ℕ} (ρ : Type*) (κ' : Fin (M + 2) → Type*) :=
  ∀ p : Fin M, Matrix (κ' p.castSucc.succ) ρ ℝ

private abbrev retainedPassiveRawCtopFamily (ρ : Type*) :=
  Matrix ρ ρ ℝ

private abbrev retainedPassiveRawF3Family
    {M : ℕ} (ρ : Type*) (κ' : Fin (M + 2) → Type*) :=
  Matrix (κ' (Fin.last (M + 1))) ρ ℝ

private def retainedPassiveRawA1PassiveLinearMapAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*} :
    RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
      retainedPassiveRawA1PassiveFamily (M := M) ρ where
  toFun w := w.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def retainedPassiveRawA3PassiveLinearMapAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*} :
    RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
      retainedPassiveRawA3PassiveFamily (M := M) ρ κ' where
  toFun w := w.2.2.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def retainedPassiveRawCtopLinearMapAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*} :
    RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
      retainedPassiveRawCtopFamily ρ where
  toFun w := w.2.2.2.2.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def retainedPassiveRawF3LinearMapAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*} :
    RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
      retainedPassiveRawF3Family (M := M) ρ κ' where
  toFun w := w.2.2.2.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def retainedPassiveRawF2CProjectionLinearMapAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*} :
    RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
      retainedPassiveRawF2CFamily (M := M) ρ κ' :=
  (LinearMap.pi fun q =>
    retainedPassiveRawF2LinearMapAt (ρ := ρ) (κ' := κ') q).prod
    (LinearMap.pi fun q =>
      retainedPassiveRawCLinearMapAt (ρ := ρ) (κ' := κ') q)

private def retainedPassiveF2SuccessorFamilyLinearMap
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*} :
    retainedPassiveRawF2Family (M := M) ρ κ' →ₗ[ℝ]
      retainedPassiveRawF2SuccessorFamily (M := M) ρ κ' :=
  LinearMap.pi fun q =>
    Fin.lastCases
      (motive := fun q : Fin (M + 1) =>
        retainedPassiveRawF2Family (M := M) ρ κ' →ₗ[ℝ]
          Matrix ρ (κ' q.succ) ℝ)
      (0 : retainedPassiveRawF2Family (M := M) ρ κ' →ₗ[ℝ]
        Matrix ρ (κ' (Fin.last M).succ) ℝ)
      (fun p =>
        (LinearEquiv.cast (R := ℝ)
          (M := fun i : Fin (M + 2) ↦ Matrix ρ (κ' i) ℝ)
          (Fin.succ_castSucc p).symm).toLinearMap.comp
            (LinearMap.proj p.succ))
      q

@[simp]
private theorem retainedPassiveF2SuccessorFamilyLinearMap_last
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    (X : retainedPassiveRawF2Family (M := M) ρ κ') :
    retainedPassiveF2SuccessorFamilyLinearMap
        (ρ := ρ) (κ' := κ') X (Fin.last M) = 0 := by
  simp only [retainedPassiveF2SuccessorFamilyLinearMap, LinearMap.pi_apply,
    Fin.lastCases_last, LinearMap.zero_apply]

@[simp]
private theorem retainedPassiveF2SuccessorFamilyLinearMap_castSucc
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    (X : retainedPassiveRawF2Family (M := M) ρ κ') (p : Fin M) :
    retainedPassiveF2SuccessorFamilyLinearMap
        (ρ := ρ) (κ' := κ') X p.castSucc =
      (LinearEquiv.cast (R := ℝ)
        (M := fun i : Fin (M + 2) ↦ Matrix ρ (κ' i) ℝ)
        (Fin.succ_castSucc p).symm) (X p.succ) := by
  simp only [retainedPassiveF2SuccessorFamilyLinearMap, LinearMap.pi_apply,
    Fin.lastCases_castSucc, LinearMap.comp_apply, LinearMap.proj_apply,
    LinearEquiv.coe_coe]

/-- One edge block in the determinant-friendly raw-tuple order
`(A1_q, A3_q, F_q, C_q)`. -/
private abbrev retainedPassiveRawTargetEdgeBlock
    {M : ℕ} (ρ : Type*) (κ' : Fin (M + 2) → Type*) (q : Fin (M + 1)) :=
  Matrix ρ ρ ℝ ×
    (Matrix (κ' q.succ) ρ ℝ ×
      (Matrix ρ (κ' q.castSucc) ℝ ×
        Matrix (κ' q.succ) (κ' q.castSucc) ℝ))

set_option linter.style.longLine false in
/-- Regroup a retained-passive raw tuple as edge-indexed blocks
`(A1_q, A3_q, F_q, C_q)`. -/
private def retainedPassiveRawTargetEdgeBlockLinearEquiv
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*} :
    RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ≃ₗ[ℝ]
      ((q : Fin (M + 1)) → retainedPassiveRawTargetEdgeBlock ρ κ' q) where
  toFun w := fun q =>
    (rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') w q,
      (rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') w q,
        (w.2.1 q, w.2.2.2.1 q)))
  invFun v :=
    (fun p : Fin M => (v p.succ).1,
      (fun q : Fin (M + 1) => (v q).2.2.1,
        (fun p : Fin M => (v p.castSucc).2.1,
          (fun q : Fin (M + 1) => (v q).2.2.2,
            ((v 0).1, (v (Fin.last M)).2.1)))))
  left_inv w := by
    rcases w with ⟨A1passive, F2, A3passive, C, Ctop, F3⟩
    simp [rawEdgeTupleA1, rawEdgeTupleA3, ofTopologyTuple]
  right_inv v := by
    funext q
    apply Prod.ext
    · cases q using Fin.cases <;> simp [rawEdgeTupleA1, ofTopologyTuple]
    · apply Prod.ext
      · induction q using Fin.lastCases <;> simp [rawEdgeTupleA3, ofTopologyTuple]
      · rfl
  map_add' w w' := by
    funext q
    apply Prod.ext
    · cases q using Fin.cases <;> rfl
    · apply Prod.ext
      · induction q using Fin.lastCases <;> simp [rawEdgeTupleA3, ofTopologyTuple]; rfl
      · rfl
  map_smul' a w := by
    funext q
    apply Prod.ext
    · cases q using Fin.cases <;> rfl
    · apply Prod.ext
      · induction q using Fin.lastCases <;> simp [rawEdgeTupleA3, ofTopologyTuple]; rfl
      · rfl

@[simp]
private theorem retainedPassiveRawTargetEdgeBlockLinearEquiv_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    (w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)
    (q : Fin (M + 1)) :
    retainedPassiveRawTargetEdgeBlockLinearEquiv
        (ρ := ρ) (κ' := κ') w q =
      (rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') w q,
        (rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') w q,
          (w.2.1 q, w.2.2.2.1 q))) :=
  rfl

@[simp]
private theorem retainedPassiveRawTargetEdgeBlockLinearEquiv_symm_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    (v : (q : Fin (M + 1)) → retainedPassiveRawTargetEdgeBlock ρ κ' q) :
    (retainedPassiveRawTargetEdgeBlockLinearEquiv
        (ρ := ρ) (κ' := κ')).symm v =
      (fun p : Fin M => (v p.succ).1,
        (fun q : Fin (M + 1) => (v q).2.2.1,
          (fun p : Fin M => (v p.castSucc).2.1,
            (fun q : Fin (M + 1) => (v q).2.2.2,
              ((v 0).1, (v (Fin.last M)).2.1))))) :=
  rfl

@[simp]
private theorem rawEdgeTupleA1_retainedPassiveRawTargetEdgeBlockLinearEquiv_symm
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    (v : (q : Fin (M + 1)) → retainedPassiveRawTargetEdgeBlock ρ κ' q)
    (q : Fin (M + 1)) :
    rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ')
        ((retainedPassiveRawTargetEdgeBlockLinearEquiv
          (ρ := ρ) (κ' := κ')).symm v) q =
      (v q).1 := by
  cases q using Fin.cases <;> simp [rawEdgeTupleA1, ofTopologyTuple]

@[simp]
private theorem rawEdgeTupleA3_retainedPassiveRawTargetEdgeBlockLinearEquiv_symm
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    (v : (q : Fin (M + 1)) → retainedPassiveRawTargetEdgeBlock ρ κ' q)
    (q : Fin (M + 1)) :
    rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ')
        ((retainedPassiveRawTargetEdgeBlockLinearEquiv
          (ρ := ρ) (κ' := κ')).symm v) q =
      (v q).2.1 := by
  induction q using Fin.lastCases <;> simp [rawEdgeTupleA3, ofTopologyTuple]

@[simp]
private theorem retainedPassiveRawTargetEdgeBlockLinearEquiv_symm_f2
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    (v : (q : Fin (M + 1)) → retainedPassiveRawTargetEdgeBlock ρ κ' q)
    (q : Fin (M + 1)) :
    ((retainedPassiveRawTargetEdgeBlockLinearEquiv
        (ρ := ρ) (κ' := κ')).symm v).2.1 q =
      (v q).2.2.1 :=
  rfl

@[simp]
private theorem retainedPassiveRawTargetEdgeBlockLinearEquiv_symm_c
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    (v : (q : Fin (M + 1)) → retainedPassiveRawTargetEdgeBlock ρ κ' q)
    (q : Fin (M + 1)) :
    ((retainedPassiveRawTargetEdgeBlockLinearEquiv
        (ρ := ρ) (κ' := κ')).symm v).2.2.2.1 q =
      (v q).2.2.2 :=
  rfl

@[simp]
private theorem rawEdgeTupleA1_retainedPassiveRawTargetEdgeBlockTuple
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    (v : (q : Fin (M + 1)) → retainedPassiveRawTargetEdgeBlock ρ κ' q)
    (q : Fin (M + 1)) :
    rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ')
      (fun p : Fin M => (v p.succ).1,
        (fun q : Fin (M + 1) => (v q).2.2.1,
          (fun p : Fin M => (v p.castSucc).2.1,
            (fun q : Fin (M + 1) => (v q).2.2.2,
              ((v 0).1, (v (Fin.last M)).2.1))))) q =
      (v q).1 := by
  cases q using Fin.cases <;> simp [rawEdgeTupleA1, ofTopologyTuple]

@[simp]
private theorem rawEdgeTupleA3_retainedPassiveRawTargetEdgeBlockTuple
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    (v : (q : Fin (M + 1)) → retainedPassiveRawTargetEdgeBlock ρ κ' q)
    (q : Fin (M + 1)) :
    rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ')
      (fun p : Fin M => (v p.succ).1,
        (fun q : Fin (M + 1) => (v q).2.2.1,
          (fun p : Fin M => (v p.castSucc).2.1,
            (fun q : Fin (M + 1) => (v q).2.2.2,
              ((v 0).1, (v (Fin.last M)).2.1))))) q =
      (v q).2.1 := by
  induction q using Fin.lastCases <;> simp [rawEdgeTupleA3, ofTopologyTuple]

set_option linter.style.longLine false in
/-- Same-edge determinant-one shear on an edge block:
`F_q -= A1_q * H_q` and `C_q -= A3_q * H_q`. -/
private def retainedPassiveRawTargetEdgeBlockDiagonalLinearMap
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [∀ j, Fintype (κ' j)]
    (q : Fin (M + 1)) (H : Matrix ρ (κ' q.castSucc) ℝ) :
    retainedPassiveRawTargetEdgeBlock ρ κ' q →ₗ[ℝ]
      retainedPassiveRawTargetEdgeBlock ρ κ' q :=
  let hA3 :
      Matrix (κ' q.succ) ρ ℝ →ₗ[ℝ]
        (Matrix ρ (κ' q.castSucc) ℝ ×
          Matrix (κ' q.succ) (κ' q.castSucc) ℝ) :=
    (0 : Matrix (κ' q.succ) ρ ℝ →ₗ[ℝ] Matrix ρ (κ' q.castSucc) ℝ).prod
      (-(retainedPassiveMatrixMulRightLinearMap H :
        Matrix (κ' q.succ) ρ ℝ →ₗ[ℝ]
          Matrix (κ' q.succ) (κ' q.castSucc) ℝ))
  let hA1 :
      Matrix ρ ρ ℝ →ₗ[ℝ]
        (Matrix (κ' q.succ) ρ ℝ ×
          (Matrix ρ (κ' q.castSucc) ℝ ×
            Matrix (κ' q.succ) (κ' q.castSucc) ℝ)) :=
    (0 : Matrix ρ ρ ℝ →ₗ[ℝ] Matrix (κ' q.succ) ρ ℝ).prod
      ((-(retainedPassiveMatrixMulRightLinearMap H :
          Matrix ρ ρ ℝ →ₗ[ℝ] Matrix ρ (κ' q.castSucc) ℝ)).prod
        (0 : Matrix ρ ρ ℝ →ₗ[ℝ]
          Matrix (κ' q.succ) (κ' q.castSucc) ℝ))
  linearMapLowerTriangular
    (LinearMap.id : Matrix ρ ρ ℝ →ₗ[ℝ] Matrix ρ ρ ℝ)
    (linearMapLowerTriangular
      (LinearMap.id : Matrix (κ' q.succ) ρ ℝ →ₗ[ℝ] Matrix (κ' q.succ) ρ ℝ)
      (LinearMap.id :
        (Matrix ρ (κ' q.castSucc) ℝ ×
          Matrix (κ' q.succ) (κ' q.castSucc) ℝ) →ₗ[ℝ]
          (Matrix ρ (κ' q.castSucc) ℝ ×
            Matrix (κ' q.succ) (κ' q.castSucc) ℝ))
      hA3)
    hA1

@[simp]
private theorem retainedPassiveRawTargetEdgeBlockDiagonalLinearMap_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [∀ j, Fintype (κ' j)]
    (q : Fin (M + 1)) (H : Matrix ρ (κ' q.castSucc) ℝ)
    (x : retainedPassiveRawTargetEdgeBlock ρ κ' q) :
    retainedPassiveRawTargetEdgeBlockDiagonalLinearMap
        (ρ := ρ) (κ' := κ') q H x =
      (x.1,
        (x.2.1,
          (x.2.2.1 - x.1 * H,
            x.2.2.2 - x.2.1 * H))) := by
  rcases x with ⟨A1, A3, F, C⟩
  simp [retainedPassiveRawTargetEdgeBlockDiagonalLinearMap, sub_eq_add_neg]
  constructor <;> abel

set_option linter.style.longLine false in
/-- The same-edge target edge-block diagonal shear has determinant one. -/
private theorem retainedPassiveRawTargetEdgeBlockDiagonalLinearMap_det_eq_one
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [∀ j, Fintype (κ' j)]
    (q : Fin (M + 1)) (H : Matrix ρ (κ' q.castSucc) ℝ) :
    LinearMap.det
      (retainedPassiveRawTargetEdgeBlockDiagonalLinearMap
        (ρ := ρ) (κ' := κ') q H) = 1 := by
  unfold retainedPassiveRawTargetEdgeBlockDiagonalLinearMap
  rw [linearMapLowerTriangular_det_eq_mul, LinearMap.det_id, one_mul]
  rw [linearMapLowerTriangular_det_eq_mul, LinearMap.det_id, LinearMap.det_id, one_mul]

set_option linter.style.longLine false in
/-- Successor off-diagonal contribution to the current edge block.  It reads
only the successor edge's `(F,C)` pair and writes only to the current `F`
slot. -/
private def retainedPassiveRawTargetEdgeBlockSuccessorLinearMap
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [∀ j, Fintype (κ' j)]
    (p : Fin M)
    (Ainv : Matrix ρ ρ ℝ)
    (Hsucc : Matrix ρ (κ' p.succ.succ) ℝ)
    (D : Matrix (κ' p.castSucc.succ) (κ' p.castSucc.castSucc) ℝ) :
    retainedPassiveRawTargetEdgeBlock ρ κ' p.succ →ₗ[ℝ]
      retainedPassiveRawTargetEdgeBlock ρ κ' p.castSucc :=
  let Fproj :
      retainedPassiveRawTargetEdgeBlock ρ κ' p.succ →ₗ[ℝ]
        Matrix ρ (κ' p.succ.castSucc) ℝ :=
    { toFun := fun x => x.2.2.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let Cproj :
      retainedPassiveRawTargetEdgeBlock ρ κ' p.succ →ₗ[ℝ]
        Matrix (κ' p.succ.succ) (κ' p.succ.castSucc) ℝ :=
    { toFun := fun x => x.2.2.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let Y :
      retainedPassiveRawTargetEdgeBlock ρ κ' p.succ →ₗ[ℝ]
        Matrix ρ (κ' p.succ.castSucc) ℝ :=
    (retainedPassiveMatrixMulLeftLinearMap Ainv).comp
      ((retainedPassiveMatrixMulLeftLinearMap Hsucc).comp Cproj - Fproj)
  let Ysucc :
      retainedPassiveRawTargetEdgeBlock ρ κ' p.succ →ₗ[ℝ]
        Matrix ρ (κ' p.castSucc.succ) ℝ :=
    (LinearEquiv.cast (R := ℝ)
      (M := fun i : Fin (M + 2) ↦ Matrix ρ (κ' i) ℝ)
      (Fin.succ_castSucc p).symm).toLinearMap.comp Y
  let Fout :
      retainedPassiveRawTargetEdgeBlock ρ κ' p.succ →ₗ[ℝ]
        Matrix ρ (κ' p.castSucc.castSucc) ℝ :=
    (retainedPassiveMatrixMulRightLinearMap D).comp Ysucc
  (0 :
    retainedPassiveRawTargetEdgeBlock ρ κ' p.succ →ₗ[ℝ] Matrix ρ ρ ℝ).prod
    ((0 :
      retainedPassiveRawTargetEdgeBlock ρ κ' p.succ →ₗ[ℝ]
        Matrix (κ' p.castSucc.succ) ρ ℝ).prod
      (Fout.prod
        (0 :
          retainedPassiveRawTargetEdgeBlock ρ κ' p.succ →ₗ[ℝ]
            Matrix (κ' p.castSucc.succ) (κ' p.castSucc.castSucc) ℝ)))

set_option linter.style.longLine false in
set_option linter.flexible false in
@[simp]
private theorem retainedPassiveRawTargetEdgeBlockSuccessorLinearMap_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [∀ j, Fintype (κ' j)]
    (p : Fin M)
    (Ainv : Matrix ρ ρ ℝ)
    (Hsucc : Matrix ρ (κ' p.succ.succ) ℝ)
    (D : Matrix (κ' p.castSucc.succ) (κ' p.castSucc.castSucc) ℝ)
    (x : retainedPassiveRawTargetEdgeBlock ρ κ' p.succ) :
    retainedPassiveRawTargetEdgeBlockSuccessorLinearMap
        (ρ := ρ) (κ' := κ') p Ainv Hsucc D x =
      (0,
        (0,
          (((LinearEquiv.cast (R := ℝ)
              (M := fun i : Fin (M + 2) ↦ Matrix ρ (κ' i) ℝ)
              (Fin.succ_castSucc p).symm)
              (Ainv * (Hsucc * x.2.2.2 - x.2.2.1))) * D,
            0))) := by
  simp [retainedPassiveRawTargetEdgeBlockSuccessorLinearMap]
  change
    retainedPassiveMatrixMulRightLinearMap D
        ((LinearEquiv.cast (R := ℝ)
          (M := fun i : Fin (M + 2) ↦ Matrix ρ (κ' i) ℝ)
          (Fin.succ_castSucc p).symm).toLinearMap
          (retainedPassiveMatrixMulLeftLinearMap Ainv
            (retainedPassiveMatrixMulLeftLinearMap Hsucc x.2.2.2 - x.2.2.1))) =
      ((LinearEquiv.cast (R := ℝ)
          (M := fun i : Fin (M + 2) ↦ Matrix ρ (κ' i) ℝ)
          (Fin.succ_castSucc p).symm)
          (Ainv * (Hsucc * x.2.2.2 - x.2.2.1))) * D
  change
      ((LinearEquiv.cast (R := ℝ)
          (M := fun i : Fin (M + 2) ↦ Matrix ρ (κ' i) ℝ)
          (Fin.succ_castSucc p).symm)
          (Ainv * (Hsucc * x.2.2.2 - x.2.2.1))) * D =
        ((LinearEquiv.cast (R := ℝ)
          (M := fun i : Fin (M + 2) ↦ Matrix ρ (κ' i) ℝ)
          (Fin.succ_castSucc p).symm)
          (Ainv * (Hsucc * x.2.2.2 - x.2.2.1))) * D
  rfl

set_option linter.style.longLine false in
private theorem retainedPassiveF2SuccessorFamilyLinearMap_formalRawF2CLinearEquivAt_symm_castSucc
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (F : ∀ q : Fin (M + 1), Matrix ρ (κ' q.castSucc) ℝ)
    (C : ∀ q : Fin (M + 1), Matrix (κ' q.succ) (κ' q.castSucc) ℝ)
    (p : Fin M) :
    let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
    retainedPassiveF2SuccessorFamilyLinearMap (ρ := ρ) (κ' := κ')
        (((retainedPassiveFormalRawF2CLinearEquivAt
            (ρ := ρ) (κ' := κ') hz).symm (F, C)).1) p.castSucc =
      (LinearEquiv.cast (R := ℝ)
        (M := fun i : Fin (M + 2) ↦ Matrix ρ (κ' i) ℝ)
        (Fin.succ_castSucc p).symm)
        ((coord.solvedA1 p.succ)⁻¹ *
          (coord.F2 p.succ.succ * C p.succ - F p.succ)) := by
  simp [retainedPassiveF2SuccessorFamilyLinearMap_castSucc,
    retainedPassiveFormalRawF2CLinearEquivAt_symm_apply]

set_option linter.style.longLine false in
private theorem retainedPassiveRawTargetEdgeBlock_inverse_castSucc_f_eq_diagonal_add_successor
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : (q : Fin (M + 1)) → retainedPassiveRawTargetEdgeBlock ρ κ' q)
    (p : Fin M) :
    let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
    (v p.castSucc).2.2.1 - (v p.castSucc).1 * coord.F2 p.castSucc.castSucc +
          retainedPassiveF2SuccessorFamilyLinearMap (ρ := ρ) (κ' := κ')
            (((retainedPassiveFormalRawF2CLinearEquivAt
                (ρ := ρ) (κ' := κ') hz).symm
              (fun q => (v q).2.2.1, fun q => (v q).2.2.2)).1) p.castSucc *
            coord.C p.castSucc =
        (retainedPassiveRawTargetEdgeBlockDiagonalLinearMap
            (ρ := ρ) (κ' := κ') p.castSucc (coord.F2 p.castSucc.castSucc)
            (v p.castSucc) +
          retainedPassiveRawTargetEdgeBlockSuccessorLinearMap
            (ρ := ρ) (κ' := κ') p ((coord.solvedA1 p.succ)⁻¹)
            (coord.F2 p.succ.succ) (coord.C p.castSucc) (v p.succ)).2.2.1 := by
  dsimp
  rw [retainedPassiveF2SuccessorFamilyLinearMap_formalRawF2CLinearEquivAt_symm_castSucc]
  simp [retainedPassiveRawTargetEdgeBlockDiagonalLinearMap_apply,
    retainedPassiveRawTargetEdgeBlockSuccessorLinearMap_apply,
    sub_eq_add_neg, add_assoc]

private theorem rawEdgeTupleA1_replaceF2C
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    (w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)
    (F2 : retainedPassiveRawF2Family (M := M) ρ κ')
    (C : retainedPassiveRawCFamily (M := M) κ')
    (q : Fin (M + 1)) :
    rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ')
        (w.1, (F2, (w.2.2.1, (C, (w.2.2.2.2.1, w.2.2.2.2.2))))) q =
      rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') w q := by
  cases q using Fin.cases <;> simp [rawEdgeTupleA1, ofTopologyTuple]

private theorem rawEdgeTupleA3_replaceF2C
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    (w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)
    (F2 : retainedPassiveRawF2Family (M := M) ρ κ')
    (C : retainedPassiveRawCFamily (M := M) κ')
    (q : Fin (M + 1)) :
    rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ')
        (w.1, (F2, (w.2.2.1, (C, (w.2.2.2.2.1, w.2.2.2.2.2))))) q =
      rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') w q := by
  induction q using Fin.lastCases <;> simp [rawEdgeTupleA3, ofTopologyTuple]

set_option linter.style.longLine false in
/-- The target-side edge-pair shear lifted to the full raw tuple by fixing all
non-edge-pair fields. -/
def retainedPassiveTargetEdgePairShearRawTupleLinearMapAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
      RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ :=
  let edgePair :=
    retainedPassiveTargetEdgePairShearLinearMapAt (ρ := ρ) (κ' := κ') z
  retainedPassiveRawA1PassiveLinearMapAt.prod
    (((LinearMap.fst ℝ
          (retainedPassiveRawF2Family (M := M) ρ κ')
          (retainedPassiveRawCFamily (M := M) κ')).comp edgePair).prod
      (retainedPassiveRawA3PassiveLinearMapAt.prod
        (((LinearMap.snd ℝ
              (retainedPassiveRawF2Family (M := M) ρ κ')
              (retainedPassiveRawCFamily (M := M) κ')).comp edgePair).prod
          (retainedPassiveRawCtopLinearMapAt.prod
            retainedPassiveRawF3LinearMapAt))))

set_option linter.style.longLine false in
/-- Formula for the full raw-tuple lift of the target-side edge-pair shear. -/
theorem retainedPassiveTargetEdgePairShearRawTupleLinearMapAt_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    retainedPassiveTargetEdgePairShearRawTupleLinearMapAt
        (ρ := ρ) (κ' := κ') z w =
      (w.1,
        ((retainedPassiveTargetEdgePairShearAt (ρ := ρ) (κ' := κ') z w).1,
          (w.2.2.1,
            ((retainedPassiveTargetEdgePairShearAt (ρ := ρ) (κ' := κ') z w).2,
              (w.2.2.2.2.1, w.2.2.2.2.2))))) := by
  simp [retainedPassiveTargetEdgePairShearRawTupleLinearMapAt,
    retainedPassiveTargetEdgePairShearLinearMapAt_apply,
    retainedPassiveRawA1PassiveLinearMapAt,
    retainedPassiveRawA3PassiveLinearMapAt,
    retainedPassiveRawCtopLinearMapAt,
    retainedPassiveRawF3LinearMapAt]

set_option linter.style.longLine false in
private theorem rawEdgeTupleA1_targetEdgePairShearRawTupleLinearMapAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)
    (q : Fin (M + 1)) :
    rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ')
        (retainedPassiveTargetEdgePairShearRawTupleLinearMapAt
          (ρ := ρ) (κ' := κ') z w) q =
      rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') w q := by
  cases q using Fin.cases with
  | zero =>
      simp [retainedPassiveTargetEdgePairShearRawTupleLinearMapAt_apply,
        rawEdgeTupleA1, ofTopologyTuple]
  | succ p =>
      simp [retainedPassiveTargetEdgePairShearRawTupleLinearMapAt_apply,
        rawEdgeTupleA1, ofTopologyTuple]

set_option linter.style.longLine false in
private theorem rawEdgeTupleA3_targetEdgePairShearRawTupleLinearMapAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)
    (q : Fin (M + 1)) :
    rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ')
        (retainedPassiveTargetEdgePairShearRawTupleLinearMapAt
          (ρ := ρ) (κ' := κ') z w) q =
      rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') w q := by
  induction q using Fin.lastCases with
  | last =>
      simp [retainedPassiveTargetEdgePairShearRawTupleLinearMapAt_apply,
        rawEdgeTupleA3, ofTopologyTuple]
  | cast p =>
      simp [retainedPassiveTargetEdgePairShearRawTupleLinearMapAt_apply,
        rawEdgeTupleA3, ofTopologyTuple]

set_option linter.style.longLine false in
/-- The inverse linear map for the full raw-tuple target edge-pair shear. -/
def retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
      RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ :=
  let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
  let sourcePair :
      RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
        retainedPassiveRawF2CFamily (M := M) ρ κ' :=
    (retainedPassiveFormalRawF2CLinearEquivAt (ρ := ρ) (κ' := κ') hz).symm.toLinearMap.comp
      retainedPassiveRawF2CProjectionLinearMapAt
  let X :
      RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
        retainedPassiveRawF2Family (M := M) ρ κ' :=
    (LinearMap.fst ℝ
      (retainedPassiveRawF2Family (M := M) ρ κ')
      (retainedPassiveRawCFamily (M := M) κ')).comp sourcePair
  let Xsucc :
      RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
        retainedPassiveRawF2SuccessorFamily (M := M) ρ κ' :=
    retainedPassiveF2SuccessorFamilyLinearMap.comp X
  let Fmap :
      RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
        retainedPassiveRawF2Family (M := M) ρ κ' :=
    LinearMap.pi fun q =>
      retainedPassiveRawF2LinearMapAt (ρ := ρ) (κ' := κ') q -
        (retainedPassiveMatrixMulRightLinearMap (coord.F2 q.castSucc)).comp
          (retainedPassiveRawEdgeTupleA1LinearMapAt (ρ := ρ) (κ' := κ') q) +
          (retainedPassiveMatrixMulRightLinearMap (coord.C q)).comp
            ((LinearMap.proj q).comp Xsucc)
  let Cmap :
      RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
        retainedPassiveRawCFamily (M := M) κ' :=
    LinearMap.pi fun q =>
      retainedPassiveRawCLinearMapAt (ρ := ρ) (κ' := κ') q -
        (retainedPassiveMatrixMulRightLinearMap (coord.F2 q.castSucc)).comp
          (retainedPassiveRawEdgeTupleA3LinearMapAt (ρ := ρ) (κ' := κ') q)
  retainedPassiveRawA1PassiveLinearMapAt.prod
    (Fmap.prod
      (retainedPassiveRawA3PassiveLinearMapAt.prod
        (Cmap.prod
          (retainedPassiveRawCtopLinearMapAt.prod
            retainedPassiveRawF3LinearMapAt))))

set_option linter.style.longLine false in
/-- Formula for the inverse full raw-tuple target edge-pair shear. -/
theorem retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
    let sourcePair :=
      (retainedPassiveFormalRawF2CLinearEquivAt (ρ := ρ) (κ' := κ') hz).symm
        (w.2.1, w.2.2.2.1)
    let Xsucc : retainedPassiveRawF2SuccessorFamily (M := M) ρ κ' :=
      retainedPassiveF2SuccessorFamilyLinearMap (ρ := ρ) (κ' := κ') sourcePair.1
    retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt
        (ρ := ρ) (κ' := κ') hz w =
      (w.1,
        (fun q : Fin (M + 1) =>
            w.2.1 q
              - rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') w q *
                coord.F2 q.castSucc
              + Xsucc q * coord.C q,
          (w.2.2.1,
            (fun q : Fin (M + 1) =>
                w.2.2.2.1 q
                  - rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') w q *
                    coord.F2 q.castSucc,
              (w.2.2.2.2.1, w.2.2.2.2.2))))) := by
  have hproj :
      retainedPassiveRawF2CProjectionLinearMapAt
          (ρ := ρ) (κ' := κ') w =
        (w.2.1, w.2.2.2.1) := by
    ext q <;> rfl
  ext q <;>
    simp [retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt,
    retainedPassiveF2SuccessorFamilyLinearMap,
    retainedPassiveRawA1PassiveLinearMapAt,
    retainedPassiveRawA3PassiveLinearMapAt,
    retainedPassiveRawCtopLinearMapAt,
    retainedPassiveRawF3LinearMapAt,
    retainedPassiveRawF2LinearMapAt,
    retainedPassiveRawCLinearMapAt,
    retainedPassiveRawEdgeTupleA1LinearMapAt,
    retainedPassiveRawEdgeTupleA3LinearMapAt,
    retainedPassiveMatrixMulRightLinearMap, hproj]

set_option linter.style.longLine false in
private theorem rawEdgeTupleA1_targetEdgePairShearRawTupleInverseLinearMapAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)
    (q : Fin (M + 1)) :
    rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ')
        (retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt
          (ρ := ρ) (κ' := κ') hz w) q =
      rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') w q := by
  cases q using Fin.cases with
  | zero =>
      simp [retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt_apply,
        rawEdgeTupleA1, ofTopologyTuple]
  | succ p =>
      simp [retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt_apply,
        rawEdgeTupleA1, ofTopologyTuple]

set_option linter.style.longLine false in
private theorem rawEdgeTupleA3_targetEdgePairShearRawTupleInverseLinearMapAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)
    (q : Fin (M + 1)) :
    rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ')
        (retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt
          (ρ := ρ) (κ' := κ') hz w) q =
      rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') w q := by
  induction q using Fin.lastCases with
  | last =>
      simp [retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt_apply,
        rawEdgeTupleA3, ofTopologyTuple]
  | cast p =>
      simp [retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt_apply,
        rawEdgeTupleA3, ofTopologyTuple]

set_option linter.style.longLine false in
set_option linter.flexible false in
/-- The first component of the formal edge-pair inverse of the target-side
edge-pair shear is the backward target-recovered `F2` recurrence. -/
theorem retainedPassiveFormalRawF2CLinearEquivAt_symm_targetEdgePairShearAt_fst
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    ((retainedPassiveFormalRawF2CLinearEquivAt (ρ := ρ) (κ' := κ') hz).symm
        (retainedPassiveTargetEdgePairShearAt (ρ := ρ) (κ' := κ') z w)).1 =
      retainedPassiveTargetRecoveredF2At (ρ := ρ) (κ' := κ') z w := by
  rw [retainedPassiveFormalRawF2CLinearEquivAt_symm_apply]
  funext q
  induction q using Fin.lastCases with
  | last =>
      rw [retainedPassiveTargetRecoveredF2At_last]
      simp [retainedPassiveTargetEdgePairShearAt,
        retainedPassiveTargetRecoveredSuccessorF2At]
      congr 1
      let coord :=
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
      let B : Matrix ρ (κ' (Fin.last M).castSucc) ℝ :=
        w.2.1 (Fin.last M)
          + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') w (Fin.last M) *
            coord.F2 (Fin.last M).castSucc
      let Z : Matrix ρ (κ' (Fin.last M).castSucc) ℝ :=
        (0 : Matrix ρ (κ' (Fin.last M).succ) ℝ) * coord.C (Fin.last M)
      have hZ : Z = 0 := by
        dsimp [Z]
        exact Matrix.zero_mul _
      change _ - (B - Z) = _ - B
      rw [hZ, sub_zero]
  | cast p =>
      rw [retainedPassiveTargetRecoveredF2At_castSucc]
      simp [retainedPassiveTargetEdgePairShearAt,
        retainedPassiveTargetRecoveredSuccessorF2At]

set_option linter.style.longLine false in
/-- Applying the inverse raw-tuple shear after the forward raw-tuple shear
recovers the original raw tuple. -/
theorem retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt_leftInverse
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt
        (ρ := ρ) (κ' := κ') hz
        (retainedPassiveTargetEdgePairShearRawTupleLinearMapAt
          (ρ := ρ) (κ' := κ') z w) =
      w := by
  have hfst :=
    retainedPassiveFormalRawF2CLinearEquivAt_symm_targetEdgePairShearAt_fst
      (ρ := ρ) (κ' := κ') hz w
  have hsucc :
      retainedPassiveF2SuccessorFamilyLinearMap (ρ := ρ) (κ' := κ')
          (((retainedPassiveFormalRawF2CLinearEquivAt
              (ρ := ρ) (κ' := κ') hz).symm
              (retainedPassiveTargetEdgePairShearAt
                (ρ := ρ) (κ' := κ') z w)).1) =
        retainedPassiveTargetRecoveredSuccessorF2At
          (ρ := ρ) (κ' := κ') z w := by
    rw [hfst]
    funext q
    induction q using Fin.lastCases with
    | last =>
        simp only [retainedPassiveF2SuccessorFamilyLinearMap_last,
          retainedPassiveTargetRecoveredSuccessorF2At_last]
    | cast p =>
        simp only [retainedPassiveF2SuccessorFamilyLinearMap_castSucc,
          retainedPassiveTargetRecoveredSuccessorF2At_castSucc]
  ext q <;>
    simp only [retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt_apply,
      retainedPassiveTargetEdgePairShearRawTupleLinearMapAt_apply,
      rawEdgeTupleA1_replaceF2C, rawEdgeTupleA3_replaceF2C,
      hsucc] <;>
    simp [retainedPassiveTargetEdgePairShearAt, sub_eq_add_neg,
      add_assoc, add_left_comm, add_comm]

set_option linter.style.longLine false in
/-- The target recovery recurrence applied to the inverse raw-tuple map returns
the first component of the formal edge-pair inverse used to define that map. -/
theorem retainedPassiveTargetRecoveredF2At_rawTupleInverse
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    retainedPassiveTargetRecoveredF2At (ρ := ρ) (κ' := κ') z
        (retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt
          (ρ := ρ) (κ' := κ') hz w) =
      ((retainedPassiveFormalRawF2CLinearEquivAt (ρ := ρ) (κ' := κ') hz).symm
        (w.2.1, w.2.2.2.1)).1 := by
  funext q
  induction q using Fin.reverseInduction with
  | last =>
      rw [retainedPassiveTargetRecoveredF2At_last]
      rw [rawEdgeTupleA1_targetEdgePairShearRawTupleInverseLinearMapAt
        (ρ := ρ) (κ' := κ') hz w (Fin.last M)]
      rw [rawEdgeTupleA3_targetEdgePairShearRawTupleInverseLinearMapAt
        (ρ := ρ) (κ' := κ') hz w (Fin.last M)]
      rw [retainedPassiveFormalRawF2CLinearEquivAt_symm_apply]
      simp only [retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt_apply,
        retainedPassiveF2SuccessorFamilyLinearMap_last, Matrix.zero_mul]
      simp only [Matrix.mul_add, Matrix.mul_neg,
        sub_eq_add_neg]
      simp only [Matrix.mul_zero, add_zero]
      abel_nf
  | cast p ih =>
      rw [retainedPassiveTargetRecoveredF2At_castSucc]
      have ih' := ih
      rw [retainedPassiveFormalRawF2CLinearEquivAt_symm_apply] at ih'
      rw [ih']
      rw [rawEdgeTupleA1_targetEdgePairShearRawTupleInverseLinearMapAt
        (ρ := ρ) (κ' := κ') hz w p.castSucc]
      rw [rawEdgeTupleA3_targetEdgePairShearRawTupleInverseLinearMapAt
        (ρ := ρ) (κ' := κ') hz w p.castSucc]
      rw [retainedPassiveFormalRawF2CLinearEquivAt_symm_apply]
      simp only [retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt_apply,
        retainedPassiveF2SuccessorFamilyLinearMap_castSucc]
      have hsource :
          ((retainedPassiveFormalRawF2CLinearEquivAt
              (ρ := ρ) (κ' := κ') hz).symm
              (w.2.1, w.2.2.2.1)).1 p.succ =
            ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.solvedA1 p.succ)⁻¹ *
              ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.F2 p.succ.succ *
                w.2.2.2.1 p.succ - w.2.1 p.succ) := by
        rw [retainedPassiveFormalRawF2CLinearEquivAt_symm_apply]
      rw [hsource]
      simp only [Matrix.mul_add, Matrix.mul_neg,
        sub_eq_add_neg]
      abel_nf

set_option linter.style.longLine false in
/-- Applying the forward raw-tuple shear after the inverse raw-tuple shear
recovers the target raw tuple. -/
theorem retainedPassiveTargetEdgePairShearRawTupleLinearMapAt_rightInverse
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    retainedPassiveTargetEdgePairShearRawTupleLinearMapAt
        (ρ := ρ) (κ' := κ') z
        (retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt
          (ρ := ρ) (κ' := κ') hz w) =
      w := by
  have hrec :=
    retainedPassiveTargetRecoveredF2At_rawTupleInverse
      (ρ := ρ) (κ' := κ') hz w
  have hsucc :
      retainedPassiveTargetRecoveredSuccessorF2At
          (ρ := ρ) (κ' := κ') z
          (retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt
            (ρ := ρ) (κ' := κ') hz w) =
        retainedPassiveF2SuccessorFamilyLinearMap (ρ := ρ) (κ' := κ')
          (((retainedPassiveFormalRawF2CLinearEquivAt
              (ρ := ρ) (κ' := κ') hz).symm
              (w.2.1, w.2.2.2.1)).1) := by
    funext q
    induction q using Fin.lastCases with
    | last =>
        simp only [retainedPassiveTargetRecoveredSuccessorF2At_last,
          retainedPassiveF2SuccessorFamilyLinearMap_last]
    | cast p =>
        simp only [retainedPassiveTargetRecoveredSuccessorF2At_castSucc,
          retainedPassiveF2SuccessorFamilyLinearMap_castSucc]
        rw [hrec]
  have hF :
      (retainedPassiveTargetEdgePairShearAt (ρ := ρ) (κ' := κ') z
          (retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt
            (ρ := ρ) (κ' := κ') hz w)).1 = w.2.1 := by
    funext q
    rw [retainedPassiveTargetEdgePairShearAt]
    change
      (retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt
            (ρ := ρ) (κ' := κ') hz w).2.1 q +
          rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ')
              (retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt
                (ρ := ρ) (κ' := κ') hz w) q *
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.F2 q.castSucc -
          retainedPassiveTargetRecoveredSuccessorF2At
              (ρ := ρ) (κ' := κ') z
              (retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt
                (ρ := ρ) (κ' := κ') hz w) q *
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.C q =
        w.2.1 q
    have hF2q :
        (retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt
              (ρ := ρ) (κ' := κ') hz w).2.1 q =
          w.2.1 q -
              rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') w q *
                (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.F2 q.castSucc +
            retainedPassiveF2SuccessorFamilyLinearMap (ρ := ρ) (κ' := κ')
                (((retainedPassiveFormalRawF2CLinearEquivAt
                    (ρ := ρ) (κ' := κ') hz).symm
                    (w.2.1, w.2.2.2.1)).1) q *
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.C q := by
      rw [retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt_apply]
    rw [rawEdgeTupleA1_targetEdgePairShearRawTupleInverseLinearMapAt
      (ρ := ρ) (κ' := κ') hz w q]
    rw [congrFun hsucc q, hF2q]
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hC :
      (retainedPassiveTargetEdgePairShearAt (ρ := ρ) (κ' := κ') z
          (retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt
            (ρ := ρ) (κ' := κ') hz w)).2 = w.2.2.2.1 := by
    funext q
    rw [retainedPassiveTargetEdgePairShearAt]
    change
      (retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt
            (ρ := ρ) (κ' := κ') hz w).2.2.2.1 q +
          rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ')
              (retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt
                (ρ := ρ) (κ' := κ') hz w) q *
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.F2 q.castSucc =
        w.2.2.2.1 q
    have hCq :
        (retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt
              (ρ := ρ) (κ' := κ') hz w).2.2.2.1 q =
          w.2.2.2.1 q -
            rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') w q *
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.F2 q.castSucc := by
      rw [retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt_apply]
    rw [rawEdgeTupleA3_targetEdgePairShearRawTupleInverseLinearMapAt
      (ρ := ρ) (κ' := κ') hz w q]
    rw [hCq]
    simp [sub_eq_add_neg, add_left_comm, add_comm]
  rw [retainedPassiveTargetEdgePairShearRawTupleLinearMapAt_apply]
  rw [hF, hC]
  rw [retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt_apply]

set_option linter.style.longLine false in
/-- The full raw-tuple target edge-pair shear as a linear equivalence. -/
def retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ≃ₗ[ℝ]
      RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ :=
  LinearEquiv.ofLinear
    (retainedPassiveTargetEdgePairShearRawTupleLinearMapAt
      (ρ := ρ) (κ' := κ') z)
    (retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt
      (ρ := ρ) (κ' := κ') hz)
    (by
      apply LinearMap.ext
      intro w
      simpa using
        retainedPassiveTargetEdgePairShearRawTupleLinearMapAt_rightInverse
          (ρ := ρ) (κ' := κ') hz w)
    (by
      apply LinearMap.ext
      intro w
      simpa using
        retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt_leftInverse
          (ρ := ρ) (κ' := κ') hz w)

set_option linter.style.longLine false in
/-- Formula for the full raw-tuple target edge-pair linear equivalence. -/
theorem retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt
        (ρ := ρ) (κ' := κ') hz w =
      retainedPassiveTargetEdgePairShearRawTupleLinearMapAt
        (ρ := ρ) (κ' := κ') z w := rfl

set_option linter.style.longLine false in
/-- Formula for the inverse of the full raw-tuple target edge-pair linear
equivalence. -/
theorem retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt_symm_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    (retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt
        (ρ := ρ) (κ' := κ') hz).symm w =
      retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt
        (ρ := ρ) (κ' := κ') hz w := rfl

set_option linter.style.longLine false in
set_option linter.flexible false in
/-- Pointwise edge-block formula for the raw inverse shear transported to
edge-block coordinates. -/
private theorem retainedPassiveRawTargetEdgeBlockLinearEquiv_inverse_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : (q : Fin (M + 1)) → retainedPassiveRawTargetEdgeBlock ρ κ' q)
    (q : Fin (M + 1)) :
    let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
    retainedPassiveRawTargetEdgeBlockLinearEquiv (ρ := ρ) (κ' := κ')
        (retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt
          (ρ := ρ) (κ' := κ') hz
          ((retainedPassiveRawTargetEdgeBlockLinearEquiv
            (ρ := ρ) (κ' := κ')).symm v)) q =
      ((v q).1,
        ((v q).2.1,
          ((v q).2.2.1 - (v q).1 * coord.F2 q.castSucc +
              retainedPassiveF2SuccessorFamilyLinearMap (ρ := ρ) (κ' := κ')
                (((retainedPassiveFormalRawF2CLinearEquivAt
                    (ρ := ρ) (κ' := κ') hz).symm
                  (fun q => (v q).2.2.1, fun q => (v q).2.2.2)).1) q *
                coord.C q,
            (v q).2.2.2 - (v q).2.1 * coord.F2 q.castSucc))) := by
  dsimp
  apply Prod.ext
  · rw [rawEdgeTupleA1_targetEdgePairShearRawTupleInverseLinearMapAt
      (ρ := ρ) (κ' := κ') hz]
    cases q using Fin.cases <;> simp [rawEdgeTupleA1, ofTopologyTuple]
  · apply Prod.ext
    · rw [rawEdgeTupleA3_targetEdgePairShearRawTupleInverseLinearMapAt
        (ρ := ρ) (κ' := κ') hz]
      induction q using Fin.lastCases <;> simp [rawEdgeTupleA3, ofTopologyTuple]
    · apply Prod.ext
      · simp only [retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt_apply,
          rawEdgeTupleA1_retainedPassiveRawTargetEdgeBlockTuple]
      · simp only [retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt_apply,
          rawEdgeTupleA3_retainedPassiveRawTargetEdgeBlockTuple]

set_option linter.style.longLine false in
set_option linter.flexible false in
/-- The inverse full raw-tuple target edge-pair shear has determinant one. -/
theorem retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt_det_eq_one
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    LinearMap.det
      (retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt
        (ρ := ρ) (κ' := κ') hz) = 1 := by
  let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
  let E :=
    retainedPassiveRawTargetEdgeBlockLinearEquiv
      (M := M) (ρ := ρ) (κ' := κ')
  let D : ∀ q : Fin (M + 1),
      retainedPassiveRawTargetEdgeBlock ρ κ' q →ₗ[ℝ]
        retainedPassiveRawTargetEdgeBlock ρ κ' q :=
    fun q =>
      retainedPassiveRawTargetEdgeBlockDiagonalLinearMap
        (ρ := ρ) (κ' := κ') q (coord.F2 q.castSucc)
  let L : ∀ p : Fin M,
      retainedPassiveRawTargetEdgeBlock ρ κ' p.succ →ₗ[ℝ]
        retainedPassiveRawTargetEdgeBlock ρ κ' p.castSucc :=
    fun p =>
      retainedPassiveRawTargetEdgeBlockSuccessorLinearMap
        (ρ := ρ) (κ' := κ') p
        ((coord.solvedA1 p.succ)⁻¹)
        (coord.F2 p.succ.succ)
        (coord.C p.castSucc)
  let T :
      (((q : Fin (M + 1)) → retainedPassiveRawTargetEdgeBlock ρ κ' q) →ₗ[ℝ]
        ((q : Fin (M + 1)) → retainedPassiveRawTargetEdgeBlock ρ κ' q)) :=
    (E : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
        ((q : Fin (M + 1)) → retainedPassiveRawTargetEdgeBlock ρ κ' q)).comp
      ((retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt
          (ρ := ρ) (κ' := κ') hz).comp
        (E.symm :
          ((q : Fin (M + 1)) → retainedPassiveRawTargetEdgeBlock ρ κ' q) →ₗ[ℝ]
            RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ))
  have hTdet : LinearMap.det T = 1 := by
    have htri :=
      linearMap_det_finSuccUpperTriangular_eq_prod
        (T := T) (D := D) (L := L)
        (by
          intro x
          have h :=
            retainedPassiveRawTargetEdgeBlockLinearEquiv_inverse_apply
              (ρ := ρ) (κ' := κ') hz x (Fin.last M)
          change
            retainedPassiveRawTargetEdgeBlockLinearEquiv (ρ := ρ) (κ' := κ')
                (retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt
                  (ρ := ρ) (κ' := κ') hz
                  ((retainedPassiveRawTargetEdgeBlockLinearEquiv
                    (ρ := ρ) (κ' := κ')).symm x)) (Fin.last M) =
              D (Fin.last M) (x (Fin.last M))
          rw [h]
          apply Prod.ext
          · simp [D]
          · apply Prod.ext
            · simp [D]
            · apply Prod.ext
              · simp [D, coord, retainedPassiveF2SuccessorFamilyLinearMap_last,
                  sub_eq_add_neg, add_assoc]
                ext i j
                change
                  (∑ a : κ' (Fin.last M).succ,
                    (0 : ℝ) *
                      (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.C
                        (Fin.last M) a j) = 0
                simp
              · simp [D, coord, sub_eq_add_neg])
        (by
          intro p x
          have h :=
            retainedPassiveRawTargetEdgeBlockLinearEquiv_inverse_apply
              (ρ := ρ) (κ' := κ') hz x p.castSucc
          change
            retainedPassiveRawTargetEdgeBlockLinearEquiv (ρ := ρ) (κ' := κ')
                (retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt
                  (ρ := ρ) (κ' := κ') hz
                  ((retainedPassiveRawTargetEdgeBlockLinearEquiv
                    (ρ := ρ) (κ' := κ')).symm x)) p.castSucc =
              D p.castSucc (x p.castSucc) + L p (x p.succ)
          rw [h]
          apply Prod.ext
          · simp [D, L]
          · apply Prod.ext
            · simp [D, L]
            · apply Prod.ext
              · simpa [D, L, coord] using
                  retainedPassiveRawTargetEdgeBlock_inverse_castSucc_f_eq_diagonal_add_successor
                    (ρ := ρ) (κ' := κ') hz x p
              · simp [D, L, coord, sub_eq_add_neg, add_assoc])
    rw [htri]
    simp [D, retainedPassiveRawTargetEdgeBlockDiagonalLinearMap_det_eq_one]
  have hconj :
      LinearMap.det T =
        LinearMap.det
          (retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt
            (ρ := ρ) (κ' := κ') hz) := by
    simp [T, E, LinearMap.det_conj]
  rw [← hconj]
  exact hTdet

set_option linter.style.longLine false in
/-- The inverse of the full raw-tuple target edge-pair linear equivalence has
determinant one. -/
theorem retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt_symm_det_eq_one
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    LinearMap.det
      ((retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt
        (ρ := ρ) (κ' := κ') hz).symm :
          RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
            RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) = 1 := by
  change LinearMap.det
      (retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt
        (ρ := ρ) (κ' := κ') hz) = 1
  exact
    retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt_det_eq_one
      (ρ := ρ) (κ' := κ') hz

set_option linter.style.longLine false in
/-- The full raw-tuple target edge-pair linear equivalence has determinant
one. -/
theorem retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt_det_eq_one
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    LinearMap.det
      (retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt
        (ρ := ρ) (κ' := κ') hz :
          RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
            RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) = 1 := by
  have hmul :=
    LinearEquiv.det_mul_det_symm
      (retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt
        (ρ := ρ) (κ' := κ') hz)
  rw [retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt_symm_det_eq_one
    (ρ := ρ) (κ' := κ') hz] at hmul
  simpa using hmul

set_option linter.style.longLine false in
/-- The full raw-tuple target edge-pair linear equivalence has absolute
determinant one. -/
theorem retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt_abs_det_eq_one
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    |LinearMap.det
      (retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt
        (ρ := ρ) (κ' := κ') hz :
          RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
            RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)| = 1 := by
  rw [retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt_det_eq_one
    (ρ := ρ) (κ' := κ') hz, abs_one]

private abbrev retainedPassiveRawA1passiveRestFamily
    {M : ℕ} (ρ : Type*) (κ' : Fin (M + 2) → Type*) :=
  retainedPassiveRawF2Family (M := M) ρ κ' ×
    (retainedPassiveRawA3PassiveFamily (M := M) ρ κ' ×
      (retainedPassiveRawCFamily (M := M) κ' ×
        (retainedPassiveRawCtopFamily ρ ×
          retainedPassiveRawF3Family (M := M) ρ κ')))

private def retainedPassiveRawA1passiveRestF2CProjectionLinearMapAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*} :
    retainedPassiveRawA1passiveRestFamily (M := M) ρ κ' →ₗ[ℝ]
      retainedPassiveRawF2CFamily (M := M) ρ κ' where
  toFun w := (w.1, w.2.2.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def retainedPassiveRawA1passiveRestEdgeTupleA3LinearMapAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    (q : Fin (M + 1)) :
    retainedPassiveRawA1passiveRestFamily (M := M) ρ κ' →ₗ[ℝ]
      Matrix (κ' q.succ) ρ ℝ where
  toFun w := Fin.lastCases w.2.2.2.2 (fun p => w.2.1 p) q
  map_add' w w' := by
    induction q using Fin.lastCases with
    | last =>
        simp only [Fin.lastCases_last]
        rfl
    | cast p =>
        simp only [Fin.lastCases_castSucc]
        rfl
  map_smul' a w := by
    induction q using Fin.lastCases with
    | last =>
        simp only [Fin.lastCases_last]
        rfl
    | cast p =>
        simp only [Fin.lastCases_castSucc]
        rfl

private theorem retainedPassiveRawA1passiveRestEdgeTupleA3LinearMapAt_apply_rawTupleRest
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    (w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)
    (q : Fin (M + 1)) :
    retainedPassiveRawA1passiveRestEdgeTupleA3LinearMapAt
        (ρ := ρ) (κ' := κ') q w.2 =
      rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') w q := by
  induction q using Fin.lastCases with
  | last =>
      unfold retainedPassiveRawA1passiveRestEdgeTupleA3LinearMapAt
      change Fin.lastCases w.2.2.2.2.2 (fun p => w.2.2.1 p) (Fin.last M) =
        rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') w (Fin.last M)
      simp [rawEdgeTupleA3, ofTopologyTuple]
  | cast p =>
      unfold retainedPassiveRawA1passiveRestEdgeTupleA3LinearMapAt
      change Fin.lastCases w.2.2.2.2.2 (fun p => w.2.2.1 p) p.castSucc =
        rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') w p.castSucc
      simp [rawEdgeTupleA3, ofTopologyTuple]

set_option linter.style.longLine false in
/-- The post-edge-pair passive `A1` correction, read from the already
normalised `(F2,C)` pair and the unchanged lower-left raw readout. -/
private def retainedPassivePostEdgePairA1passiveCorrectionLinearMapAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    retainedPassiveRawA1passiveRestFamily (M := M) ρ κ' →ₗ[ℝ]
      retainedPassiveRawA1PassiveFamily (M := M) ρ :=
  let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
  let sourcePair :
      retainedPassiveRawA1passiveRestFamily (M := M) ρ κ' →ₗ[ℝ]
        retainedPassiveRawF2CFamily (M := M) ρ κ' :=
    (retainedPassiveFormalRawF2CLinearEquivAt (ρ := ρ) (κ' := κ') hz).symm.toLinearMap.comp
      retainedPassiveRawA1passiveRestF2CProjectionLinearMapAt
  let X :
      retainedPassiveRawA1passiveRestFamily (M := M) ρ κ' →ₗ[ℝ]
        retainedPassiveRawF2Family (M := M) ρ κ' :=
    (LinearMap.fst ℝ
      (retainedPassiveRawF2Family (M := M) ρ κ')
      (retainedPassiveRawCFamily (M := M) κ')).comp sourcePair
  let Xsucc :
      retainedPassiveRawA1passiveRestFamily (M := M) ρ κ' →ₗ[ℝ]
        retainedPassiveRawF2SuccessorFamily (M := M) ρ κ' :=
    retainedPassiveF2SuccessorFamilyLinearMap.comp X
  LinearMap.pi fun p : Fin M =>
    (retainedPassiveMatrixMulRightLinearMap (coord.solvedA3 p.succ)).comp
        ((LinearMap.proj p.succ).comp Xsucc) +
      (retainedPassiveMatrixMulLeftLinearMap (coord.F2 p.succ.succ)).comp
        (retainedPassiveRawA1passiveRestEdgeTupleA3LinearMapAt
          (ρ := ρ) (κ' := κ') p.succ)

set_option linter.style.longLine false in
/-- After the target edge-pair shear, change only the passive `A1` field by
subtracting the target-staged correction read from the normalised `(F2,C)`
pair. -/
def retainedPassivePostEdgePairA1passiveShearRawTupleLinearEquivAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ≃ₗ[ℝ]
      RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ :=
  linearEquivUpperShear
    (R := ℝ)
    (M := retainedPassiveRawA1PassiveFamily (M := M) ρ)
    (N := retainedPassiveRawA1passiveRestFamily (M := M) ρ κ')
    (-(retainedPassivePostEdgePairA1passiveCorrectionLinearMapAt
      (ρ := ρ) (κ' := κ') hz))

set_option linter.style.longLine false in
/-- Formula for the post-edge-pair passive `A1` raw-tuple shear. -/
theorem retainedPassivePostEdgePairA1passiveShearRawTupleLinearEquivAt_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
    let sourcePair :=
      (retainedPassiveFormalRawF2CLinearEquivAt (ρ := ρ) (κ' := κ') hz).symm
        (w.2.1, w.2.2.2.1)
    let Xsucc : retainedPassiveRawF2SuccessorFamily (M := M) ρ κ' :=
      retainedPassiveF2SuccessorFamilyLinearMap (ρ := ρ) (κ' := κ') sourcePair.1
    retainedPassivePostEdgePairA1passiveShearRawTupleLinearEquivAt
        (ρ := ρ) (κ' := κ') hz w =
      (fun p : Fin M =>
          w.1 p
            - Xsucc p.succ * coord.solvedA3 p.succ
            - coord.F2 p.succ.succ *
                rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') w p.succ,
        w.2) := by
  apply Prod.ext
  · funext p
    simp [retainedPassivePostEdgePairA1passiveShearRawTupleLinearEquivAt,
      retainedPassivePostEdgePairA1passiveCorrectionLinearMapAt,
      retainedPassiveRawA1passiveRestF2CProjectionLinearMapAt,
      retainedPassiveRawA1passiveRestEdgeTupleA3LinearMapAt_apply_rawTupleRest,
      retainedPassiveMatrixMulRightLinearMap,
      retainedPassiveMatrixMulLeftLinearMap,
      sub_eq_add_neg, add_left_comm, add_comm]
  · rfl

set_option linter.style.longLine false in
/-- Formula for the inverse post-edge-pair passive `A1` raw-tuple shear. -/
theorem retainedPassivePostEdgePairA1passiveShearRawTupleLinearEquivAt_symm_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
    let sourcePair :=
      (retainedPassiveFormalRawF2CLinearEquivAt (ρ := ρ) (κ' := κ') hz).symm
        (w.2.1, w.2.2.2.1)
    let Xsucc : retainedPassiveRawF2SuccessorFamily (M := M) ρ κ' :=
      retainedPassiveF2SuccessorFamilyLinearMap (ρ := ρ) (κ' := κ') sourcePair.1
    (retainedPassivePostEdgePairA1passiveShearRawTupleLinearEquivAt
        (ρ := ρ) (κ' := κ') hz).symm w =
      (fun p : Fin M =>
          w.1 p
            + Xsucc p.succ * coord.solvedA3 p.succ
            + coord.F2 p.succ.succ *
                rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') w p.succ,
        w.2) := by
  apply Prod.ext
  · funext p
    simp [retainedPassivePostEdgePairA1passiveShearRawTupleLinearEquivAt,
      retainedPassivePostEdgePairA1passiveCorrectionLinearMapAt,
      retainedPassiveRawA1passiveRestF2CProjectionLinearMapAt,
      retainedPassiveRawA1passiveRestEdgeTupleA3LinearMapAt_apply_rawTupleRest,
      retainedPassiveMatrixMulRightLinearMap,
      retainedPassiveMatrixMulLeftLinearMap,
      sub_eq_add_neg, add_left_comm, add_comm]
  · rfl

/-- The post-edge-pair passive `A1` raw-tuple shear has determinant one. -/
theorem retainedPassivePostEdgePairA1passiveShearRawTupleLinearEquivAt_det_eq_one
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    LinearMap.det
      (retainedPassivePostEdgePairA1passiveShearRawTupleLinearEquivAt
        (ρ := ρ) (κ' := κ') hz :
          RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
            RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) = 1 := by
  simpa [retainedPassivePostEdgePairA1passiveShearRawTupleLinearEquivAt] using
    linearEquivUpperShear_det_eq_one
      (R := ℝ)
      (M := retainedPassiveRawA1PassiveFamily (M := M) ρ)
      (N := retainedPassiveRawA1passiveRestFamily (M := M) ρ κ')
      (f := -(retainedPassivePostEdgePairA1passiveCorrectionLinearMapAt
        (ρ := ρ) (κ' := κ') hz))

/-- The post-edge-pair passive `A1` raw-tuple shear has absolute determinant
one. -/
theorem retainedPassivePostEdgePairA1passiveShearRawTupleLinearEquivAt_abs_det_eq_one
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    |LinearMap.det
      (retainedPassivePostEdgePairA1passiveShearRawTupleLinearEquivAt
        (ρ := ρ) (κ' := κ') hz :
          RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →ₗ[ℝ]
            RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)| = 1 := by
  rw [retainedPassivePostEdgePairA1passiveShearRawTupleLinearEquivAt_det_eq_one
    (ρ := ρ) (κ' := κ') hz, abs_one]

end TargetEdgePairLinearMap

set_option linter.style.longLine false in
/-- Source `(F2,C)` tangents recovered from an arbitrary target tuple by first
forming the target-side normalized edge pair and then applying the formal
edge-pair inverse. -/
def retainedPassiveTargetRecoveredSourcePairAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    ((∀ q : Fin (M + 1), Matrix ρ (κ' q.castSucc) ℝ) ×
      (∀ q : Fin (M + 1), Matrix (κ' q.succ) (κ' q.castSucc) ℝ)) :=
  (retainedPassiveFormalRawF2CLinearEquivAt (ρ := ρ) (κ' := κ') hz).symm
    (retainedPassiveTargetEdgePairShearAt (ρ := ρ) (κ' := κ') z w)

set_option linter.style.longLine false in
/-- The target-recovered source `(F2,C)` pair recovers the actual source pair
on raw-order Frechet derivative targets. -/
theorem retainedPassiveTargetRecoveredSourcePairAt_fderiv_eq_sourcePair
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    retainedPassiveTargetRecoveredSourcePairAt
        (ρ := ρ) (κ' := κ') hz ((fderiv ℝ raw z) v) =
      (v.2.1, v.2.2.2.1) := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  simpa [retainedPassiveTargetRecoveredSourcePairAt, raw] using
    retainedPassiveTargetEdgePairShearAt_fderiv_recovers_sourcePair
      (ρ := ρ) (κ' := κ') hz v

set_option linter.style.longLine false in
/-- Source `C` tangent recovered from an arbitrary target tuple. -/
def retainedPassiveTargetRecoveredSourceCAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)
    (q : Fin (M + 1)) : Matrix (κ' q.succ) (κ' q.castSucc) ℝ :=
  (retainedPassiveTargetRecoveredSourcePairAt (ρ := ρ) (κ' := κ') hz w).2 q

set_option linter.style.longLine false in
/-- The target-recovered source `C` tangent recovers the source `C` component
on raw-order Frechet derivative targets. -/
theorem retainedPassiveTargetRecoveredSourceCAt_fderiv_eq_sourceC
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)
    (q : Fin (M + 1)) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    retainedPassiveTargetRecoveredSourceCAt
        (ρ := ρ) (κ' := κ') hz ((fderiv ℝ raw z) v) q =
      v.2.2.2.1 q := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  have hpair :=
    retainedPassiveTargetRecoveredSourcePairAt_fderiv_eq_sourcePair
      (ρ := ρ) (κ' := κ') hz v
  change
      (retainedPassiveTargetRecoveredSourcePairAt
        (ρ := ρ) (κ' := κ') hz ((fderiv ℝ raw z) v)).2 q =
        v.2.2.2.1 q
  rw [hpair]

set_option linter.style.longLine false in
/-- One target-only product-rule step for the Frechet derivative of a stored
`C`-block suffix product. -/
def retainedPassiveCTailTargetOnlyStepAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)
    (p : Fin (M + 1))
    (dCsucc : Matrix (κ' (Fin.last (M + 1))) (κ' p.succ) ℝ) :
    Matrix (κ' (Fin.last (M + 1))) (κ' p.castSucc) ℝ :=
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let Cfun : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →
      ∀ s : Fin (M + 1), Matrix (κ' s.succ) (κ' s.castSucc) ℝ :=
    fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
  let Csucc : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →
      Matrix (κ' (Fin.last (M + 1))) (κ' p.succ) ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ') (Cfun y)
        (Fin.last (M + 1)) p.succ p.succ.le_last
  dCsucc * data.C p +
    Csucc z *
      retainedPassiveTargetRecoveredSourceCAt
        (M := M) (ρ := ρ) (κ' := κ') hz w p

set_option linter.style.longLine false in
/-- On actual raw-order Frechet derivative targets, the target-only `C` suffix
one-step helper is the product-rule derivative of the suffix beginning at
`p.castSucc`. -/
theorem retainedPassiveCTailTargetOnlyStepAt_fderiv_eq_sourceStep
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)
    (p : Fin (M + 1)) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let Cfun : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →
        ∀ s : Fin (M + 1), Matrix (κ' s.succ) (κ' s.castSucc) ℝ :=
      fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
    let Ccast : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →
        Matrix (κ' (Fin.last (M + 1))) (κ' p.castSucc) ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ') (Cfun y)
          (Fin.last (M + 1)) p.castSucc p.castSucc.le_last
    let Csucc : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →
        Matrix (κ' (Fin.last (M + 1))) (κ' p.succ) ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ') (Cfun y)
          (Fin.last (M + 1)) p.succ p.succ.le_last
    retainedPassiveCTailTargetOnlyStepAt
        (M := M) (ρ := ρ) (κ' := κ') hz ((fderiv ℝ raw z) v) p
        ((fderiv ℝ Csucc z) v) =
      (fderiv ℝ Ccast z) v := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let Dzv := (fderiv ℝ raw z) v
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let Cfun : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →
      ∀ s : Fin (M + 1), Matrix (κ' s.succ) (κ' s.castSucc) ℝ :=
    fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
  let Ccast : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →
      Matrix (κ' (Fin.last (M + 1))) (κ' p.castSucc) ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ') (Cfun y)
        (Fin.last (M + 1)) p.castSucc p.castSucc.le_last
  let Csucc : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →
      Matrix (κ' (Fin.last (M + 1))) (κ' p.succ) ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ') (Cfun y)
        (Fin.last (M + 1)) p.succ p.succ.le_last
  have hprod :=
    fderiv_retainedPassive_C_residualFactorProduct_castSucc_apply
      (M := M) (ρ := ρ) (κ' := κ') z v p
  have hC :=
    retainedPassiveTargetRecoveredSourceCAt_fderiv_eq_sourceC
      (M := M) (ρ := ρ) (κ' := κ') hz v p
  calc
    retainedPassiveCTailTargetOnlyStepAt
        (M := M) (ρ := ρ) (κ' := κ') hz Dzv p ((fderiv ℝ Csucc z) v)
        =
      (fderiv ℝ Csucc z) v * data.C p + Csucc z * v.2.2.2.1 p := by
        simp [retainedPassiveCTailTargetOnlyStepAt, raw, Dzv, data, Cfun, Csucc, hC]
    _ = (fderiv ℝ Ccast z) v := by
        simpa [data, Cfun, Ccast, Csucc] using hprod.symm

set_option linter.style.longLine false in
/-- Target-only recursive derivative for a stored `C` suffix product, indexed
by the first vertex included in the suffix. -/
def retainedPassiveCSuffixTargetStagedFDerivAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)
    (m : ℕ) (hm : m ≤ M + 1) :
    Matrix (κ' (Fin.last (M + 1))) (κ' ⟨m, Nat.lt_succ_of_le hm⟩) ℝ :=
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  Nat.decreasingInduction
    (motive := fun m hm ↦
      Matrix (κ' (Fin.last (M + 1))) (κ' ⟨m, Nat.lt_succ_of_le hm⟩) ℝ)
    (fun n hns acc ↦ by
      let p : Fin (M + 1) := ⟨n, Nat.lt_of_succ_le hns⟩
      let Csucc :=
        ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
          data.C (Fin.last (M + 1)) p.succ p.succ.le_last
      let acc' : Matrix (κ' (Fin.last (M + 1))) (κ' p.succ) ℝ := by
        simpa [p] using acc
      let step : Matrix (κ' (Fin.last (M + 1))) (κ' p.castSucc) ℝ :=
        acc' * data.C p +
          Csucc *
            retainedPassiveTargetRecoveredSourceCAt
              (M := M) (ρ := ρ) (κ' := κ') hz w p
      simpa [p] using step)
    0
    hm

@[simp]
theorem retainedPassiveCSuffixTargetStagedFDerivAt_self
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    retainedPassiveCSuffixTargetStagedFDerivAt
        (M := M) (ρ := ρ) (κ' := κ') hz w (M + 1) le_rfl =
      (0 : Matrix (κ' (Fin.last (M + 1))) (κ' (Fin.last (M + 1))) ℝ) := by
  simp [retainedPassiveCSuffixTargetStagedFDerivAt]
  rfl

set_option linter.style.longLine false in
/-- One-step unfold equation for the target-only recursive stored `C` suffix
derivative. -/
theorem retainedPassiveCSuffixTargetStagedFDerivAt_step
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)
    (m : ℕ) (hm : m < M + 1) :
    retainedPassiveCSuffixTargetStagedFDerivAt
        (M := M) (ρ := ρ) (κ' := κ') hz w m (Nat.le_of_lt hm) =
      let p : Fin (M + 1) := ⟨m, hm⟩
      let dCsucc : Matrix (κ' (Fin.last (M + 1))) (κ' p.succ) ℝ := by
        simpa [p] using
          retainedPassiveCSuffixTargetStagedFDerivAt
            (M := M) (ρ := ρ) (κ' := κ') hz w (m + 1)
            (Nat.succ_le_of_lt hm)
      retainedPassiveCTailTargetOnlyStepAt
        (M := M) (ρ := ρ) (κ' := κ') hz w p dCsucc := by
  unfold retainedPassiveCSuffixTargetStagedFDerivAt
  rw [Nat.decreasingInduction_succ_left (smn := Nat.succ_le_of_lt hm)]
  simp [retainedPassiveCTailTargetOnlyStepAt]

set_option linter.style.longLine false in
/-- The retained-passive stored `C` suffix product beginning at vertex `m`. -/
def retainedPassiveCSuffixProductAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (m : ℕ) (hm : m ≤ M + 1) :
    RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →
      Matrix (κ' (Fin.last (M + 1))) (κ' ⟨m, Nat.lt_succ_of_le hm⟩) ℝ :=
  fun y ↦
    ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
      (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
      (Fin.last (M + 1))
      ⟨m, Nat.lt_succ_of_le hm⟩
      (Fin.val_fin_le.mpr hm)

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- The Frechet derivative of a stored `C` suffix product agrees with the
target-only recursive staged expression on actual raw-order derivative targets. -/
theorem fderiv_retainedPassive_C_residualFactorProduct_targetStaged_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)
    (m : ℕ) (hm : m ≤ M + 1) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    (fderiv ℝ
      (retainedPassiveCSuffixProductAt
        (M := M) (ρ := ρ) (κ' := κ') m hm) z) v =
      retainedPassiveCSuffixTargetStagedFDerivAt
        (M := M) (ρ := ρ) (κ' := κ') hz ((fderiv ℝ raw z) v) m hm := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let Dzv := (fderiv ℝ raw z) v
  let motive : (m : ℕ) → m ≤ M + 1 → Prop := fun m hm ↦
    (fderiv ℝ
      (retainedPassiveCSuffixProductAt
        (M := M) (ρ := ρ) (κ' := κ') m hm) z) v =
      retainedPassiveCSuffixTargetStagedFDerivAt
        (M := M) (ρ := ρ) (κ' := κ') hz Dzv m hm
  have hbase : motive (M + 1) le_rfl := by
    dsimp [motive]
    rw [retainedPassiveCSuffixTargetStagedFDerivAt_self]
    change
      (fderiv ℝ
        (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
          ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
            (Fin.last (M + 1)) (Fin.last (M + 1)) le_rfl) z) v =
        (0 : Matrix (κ' (Fin.last (M + 1))) (κ' (Fin.last (M + 1))) ℝ)
    exact
      fderiv_retainedPassive_C_residualFactorProduct_self_apply
        (M := M) (ρ := ρ) (κ' := κ') z v (Fin.last (M + 1))
  have hstep : ∀ n (hns : n + 1 ≤ M + 1),
      motive (n + 1) hns → motive n (Nat.le_of_succ_le hns) := by
    intro n hns ih
    let p : Fin (M + 1) := ⟨n, Nat.lt_of_succ_le hns⟩
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let Csucc : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →
        Matrix (κ' (Fin.last (M + 1))) (κ' p.succ) ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
          (Fin.last (M + 1)) p.succ p.succ.le_last
    have hstaged :=
      retainedPassiveCSuffixTargetStagedFDerivAt_step
        (M := M) (ρ := ρ) (κ' := κ') hz Dzv n
        (Nat.lt_of_succ_le hns)
    let dCsucc : Matrix (κ' (Fin.last (M + 1))) (κ' p.succ) ℝ := by
      simpa [p] using
        retainedPassiveCSuffixTargetStagedFDerivAt
          (M := M) (ρ := ρ) (κ' := κ') hz Dzv (n + 1) hns
    have hih :
        (fderiv ℝ Csucc z) v = dCsucc := by
      simpa [motive, retainedPassiveCSuffixProductAt, Csucc, p, dCsucc] using ih
    have hsourceStep :=
      retainedPassiveCTailTargetOnlyStepAt_fderiv_eq_sourceStep
        (M := M) (ρ := ρ) (κ' := κ') hz v p
    have hleft :
        (fderiv ℝ
          (retainedPassiveCSuffixProductAt
            (M := M) (ρ := ρ) (κ' := κ') n (Nat.le_of_succ_le hns)) z) v =
          retainedPassiveCTailTargetOnlyStepAt
            (M := M) (ρ := ρ) (κ' := κ') hz Dzv p dCsucc := by
      have hleft0 :
          (fderiv ℝ
            (retainedPassiveCSuffixProductAt
              (M := M) (ρ := ρ) (κ' := κ') n (Nat.le_of_succ_le hns)) z) v =
            retainedPassiveCTailTargetOnlyStepAt
              (M := M) (ρ := ρ) (κ' := κ') hz Dzv p ((fderiv ℝ Csucc z) v) := by
        simpa [raw, Dzv, retainedPassiveCSuffixProductAt, Csucc, p] using hsourceStep.symm
      simpa [hih] using hleft0
    have hright :
        retainedPassiveCTailTargetOnlyStepAt
            (M := M) (ρ := ρ) (κ' := κ') hz Dzv p dCsucc =
          retainedPassiveCSuffixTargetStagedFDerivAt
            (M := M) (ρ := ρ) (κ' := κ') hz Dzv n (Nat.le_of_succ_le hns) := by
      simpa [data, p, Csucc, dCsucc] using hstaged.symm
    exact hleft.trans hright
  simpa [motive, raw, Dzv] using
    Nat.decreasingInduction (motive := motive) hstep hbase hm

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

set_option linter.style.longLine false in
/-- Target-only staged tangent for a passive top-left `A1` coordinate. -/
def retainedPassiveTargetStagedA1passiveTangentAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) (q : Fin M) :
    Matrix ρ ρ ℝ :=
  let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
  let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z w
  w.1 q
    - XsuccF2 q.succ * coord.solvedA3 q.succ
    - coord.F2 q.succ.succ *
        rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') w q.succ

set_option linter.style.longLine false in
/-- On an actual raw-order derivative target, the target-only staged passive
`A1` tangent recovers the source passive `A1` tangent. -/
theorem retainedPassiveTargetStagedA1passiveTangentAt_fderiv_eq_source
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) (q : Fin M) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    retainedPassiveTargetStagedA1passiveTangentAt
        (ρ := ρ) (κ' := κ') z ((fderiv ℝ raw z) v) q =
      v.1 q := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let coord := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
  have hA1 :=
    A1passive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_A1passive
      (ρ := ρ) (κ' := κ') hz v q
  simpa [retainedPassiveTargetStagedA1passiveTangentAt, raw, coord, Dzv, XsuccF2] using hA1

set_option linter.style.longLine false in
/-- The passive top-left seed-product suffix derivative can be target-staged
at its current passive seed, leaving the remaining suffix derivative explicit. -/
theorem fderiv_retainedPassive_A1seed_residualFactorProduct_succ_castSucc_target_staged_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) (q : Fin M) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    let Dzv := (fderiv ℝ raw z) v
    let p : Fin (M + 1) := q.succ
    let Pcast : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ → Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct
          (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
          (Fin.last (M + 1)) p.castSucc p.castSucc.le_last
    let Psucc : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ → Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct
          (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
          (Fin.last (M + 1)) p.succ p.succ.le_last
    let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
    (fderiv ℝ Pcast z) v =
      (fderiv ℝ Psucc z) v * data.A1seed p +
        Psucc z *
          (Dzv.1 q
            - XsuccF2 q.succ * coord.solvedA3 q.succ
            - coord.F2 q.succ.succ *
                rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q.succ) := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  let p : Fin (M + 1) := q.succ
  let Pcast : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ → Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct
        (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
        (Fin.last (M + 1)) p.castSucc p.castSucc.le_last
  let Psucc : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ → Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct
        (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
        (Fin.last (M + 1)) p.succ p.succ.le_last
  let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
  have hbase :=
    fderiv_retainedPassive_A1seed_residualFactorProduct_succ_castSucc_apply
      (M := M) (ρ := ρ) (κ' := κ') z v q
  have hA1 :=
    A1passive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_A1passive
      (ρ := ρ) (κ' := κ') hz v q
  change (fderiv ℝ Pcast z) v =
      (fderiv ℝ Psucc z) v * data.A1seed p + Psucc z * v.1 q at hbase
  change Dzv.1 q
      - XsuccF2 q.succ * coord.solvedA3 q.succ
      - coord.F2 q.succ.succ *
          rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q.succ =
      v.1 q at hA1
  rw [← hA1] at hbase
  simpa [raw, data, coord, Dzv, p, Pcast, Psucc, XsuccF2] using hbase

set_option linter.style.longLine false in
/-- For a positive retained-passive top-left tail, target-stage the first
passive seed tangent in the first suffix-product derivative step. -/
theorem fderiv_retainedPassive_A1TailAfterFirst_pos_target_staged_apply
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
    let Dzv := (fderiv ℝ raw z) v
    let q : Fin M := ⟨0, hM⟩
    let p : Fin (M + 1) := q.succ
    let Tfun : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ → Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
    let Psucc : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ → Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ)
          (κ := fun _ : Fin (M + 2) ↦ ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
          (Fin.last (M + 1)) p.succ p.succ.le_last
    let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
    (fderiv ℝ Tfun z) v =
      (fderiv ℝ Psucc z) v * data.A1seed p +
        Psucc z *
          (Dzv.1 q
            - XsuccF2 q.succ * coord.solvedA3 q.succ
            - coord.F2 q.succ.succ *
                rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q.succ) := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  let q : Fin M := ⟨0, hM⟩
  let p : Fin (M + 1) := q.succ
  let Tfun : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ → Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
  let Pcast : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ → Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ)
        (κ := fun _ : Fin (M + 2) ↦ ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
        (Fin.last (M + 1)) p.castSucc p.castSucc.le_last
  let Psucc : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ → Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ)
        (κ := fun _ : Fin (M + 2) ↦ ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
        (Fin.last (M + 1)) p.succ p.succ.le_last
  let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
  have htail_eq : Tfun = Pcast := by
    funext y
    simp [Tfun, Pcast, ChartLocalSuffixState.retainedPassiveA1TailAfterFirst, p, q]
  have hrec :=
    fderiv_retainedPassive_A1seed_residualFactorProduct_succ_castSucc_target_staged_apply
      (M := M) (ρ := ρ) (κ' := κ') hz v q
  calc
    (fderiv ℝ Tfun z) v = (fderiv ℝ Pcast z) v := by
      rw [htail_eq]
    _ =
      (fderiv ℝ Psucc z) v * data.A1seed p +
        Psucc z *
          (Dzv.1 q
            - XsuccF2 q.succ * coord.solvedA3 q.succ
            - coord.F2 q.succ.succ *
                rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q.succ) := by
      simpa [raw, data, coord, Dzv, q, p, Pcast, Psucc, XsuccF2] using hrec

set_option linter.style.longLine false in
/-- Target-only recursive derivative for a retained-passive top-left `A1`
tail suffix, indexed by the first passive slot included in the suffix. -/
def retainedPassiveA1TailTargetStagedFDerivAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)
    (m : ℕ) (hm : m ≤ M) : Matrix ρ ρ ℝ :=
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  Nat.decreasingInduction
    (motive := fun _ _ ↦ Matrix ρ ρ ℝ)
    (fun n hns acc ↦
      let q : Fin M := ⟨n, Nat.lt_of_succ_le hns⟩
      let p : Fin (M + 1) := q.succ
      let Psucc :=
        ChartLocalSuffixState.residualFactorProduct (K := ℝ)
          (κ := fun _ : Fin (M + 2) ↦ ρ)
          data.A1seed (Fin.last (M + 1)) p.succ p.succ.le_last
      acc * data.A1seed p +
        Psucc *
          retainedPassiveTargetStagedA1passiveTangentAt
            (ρ := ρ) (κ' := κ') z w q)
    0
    hm

@[simp]
theorem retainedPassiveA1TailTargetStagedFDerivAt_self
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    retainedPassiveA1TailTargetStagedFDerivAt
        (ρ := ρ) (κ' := κ') z w M le_rfl =
      (0 : Matrix ρ ρ ℝ) := by
  simp [retainedPassiveA1TailTargetStagedFDerivAt]

set_option linter.style.longLine false in
/-- One-step unfold equation for the target-only recursive passive top-left
tail derivative. -/
theorem retainedPassiveA1TailTargetStagedFDerivAt_step
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)
    (m : ℕ) (hm : m < M) :
    retainedPassiveA1TailTargetStagedFDerivAt
        (ρ := ρ) (κ' := κ') z w m (Nat.le_of_lt hm) =
      let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
      let q : Fin M := ⟨m, hm⟩
      let p : Fin (M + 1) := q.succ
      let Psucc :=
        ChartLocalSuffixState.residualFactorProduct (K := ℝ)
          (κ := fun _ : Fin (M + 2) ↦ ρ)
          data.A1seed (Fin.last (M + 1)) p.succ p.succ.le_last
      retainedPassiveA1TailTargetStagedFDerivAt
          (ρ := ρ) (κ' := κ') z w (m + 1) (Nat.succ_le_of_lt hm) *
        data.A1seed p +
          Psucc *
            retainedPassiveTargetStagedA1passiveTangentAt
              (ρ := ρ) (κ' := κ') z w q := by
  unfold retainedPassiveA1TailTargetStagedFDerivAt
  rw [Nat.decreasingInduction_succ_left]

set_option linter.style.longLine false in
/-- First-index unfold equation for a nonempty target-only recursive passive
top-left tail derivative. -/
theorem retainedPassiveA1TailTargetStagedFDerivAt_zero
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (hM : 0 < M)
    (z w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let q : Fin M := ⟨0, hM⟩
    let p : Fin (M + 1) := q.succ
    let Psucc :=
      ChartLocalSuffixState.residualFactorProduct (K := ℝ)
        (κ := fun _ : Fin (M + 2) ↦ ρ)
        data.A1seed (Fin.last (M + 1)) p.succ p.succ.le_last
    retainedPassiveA1TailTargetStagedFDerivAt
        (ρ := ρ) (κ' := κ') z w 0 (Nat.zero_le M) =
      retainedPassiveA1TailTargetStagedFDerivAt
          (ρ := ρ) (κ' := κ') z w 1 (Nat.succ_le_of_lt hM) *
        data.A1seed p +
          Psucc *
            retainedPassiveTargetStagedA1passiveTangentAt
              (ρ := ρ) (κ' := κ') z w q := by
  simpa using
    retainedPassiveA1TailTargetStagedFDerivAt_step
      (ρ := ρ) (κ' := κ') z w 0 hM

set_option linter.style.longLine false in
/-- The retained-passive top-left seed-product suffix beginning at passive
slot `m`.  The boundary value `m=M` is the empty endpoint suffix. -/
def retainedPassiveA1seedTailProductAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (m : ℕ) (hm : m ≤ M) :
    RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ → Matrix ρ ρ ℝ :=
  fun y ↦
    ChartLocalSuffixState.residualFactorProduct (K := ℝ)
      (κ := fun _ : Fin (M + 2) ↦ ρ)
      (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
      (Fin.last (M + 1))
      ⟨m + 1, Nat.lt_succ_of_le (Nat.succ_le_succ hm)⟩
      (Fin.val_fin_le.mpr (Nat.succ_le_succ hm))

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- The Frechet derivative of any passive top-left seed-product suffix agrees
with the target-only recursive staged expression on an actual raw-order
derivative target. -/
theorem fderiv_retainedPassive_A1seed_residualFactorProduct_targetStaged_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)
    (m : ℕ) (hm : m ≤ M) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    (fderiv ℝ
      (retainedPassiveA1seedTailProductAt
        (ρ := ρ) (κ' := κ') m hm) z) v =
      retainedPassiveA1TailTargetStagedFDerivAt
        (ρ := ρ) (κ' := κ') z ((fderiv ℝ raw z) v) m hm := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let Dzv := (fderiv ℝ raw z) v
  let motive : (m : ℕ) → m ≤ M → Prop := fun m hm ↦
    (fderiv ℝ
      (retainedPassiveA1seedTailProductAt
        (ρ := ρ) (κ' := κ') m hm) z) v =
      retainedPassiveA1TailTargetStagedFDerivAt
        (ρ := ρ) (κ' := κ') z Dzv m hm
  have hbase : motive M le_rfl := by
    dsimp [motive]
    rw [retainedPassiveA1TailTargetStagedFDerivAt_self]
    let Pself : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ → Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ)
          (κ := fun _ : Fin (M + 2) ↦ ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
          (Fin.last (M + 1)) (Fin.last (M + 1)) le_rfl
    have hfun :
        retainedPassiveA1seedTailProductAt
            (ρ := ρ) (κ' := κ') M le_rfl = Pself := by
      funext y
      dsimp [retainedPassiveA1seedTailProductAt, Pself]
      calc
        ChartLocalSuffixState.residualFactorProduct (K := ℝ)
            (κ := fun _ : Fin (M + 2) ↦ ρ)
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
            (Fin.last (M + 1))
            ⟨M + 1, Nat.lt_succ_of_le (Nat.succ_le_succ (Nat.le_refl M))⟩
            (Fin.val_fin_le.mpr (Nat.succ_le_succ (Nat.le_refl M))) =
          (1 : Matrix ρ ρ ℝ) := by
            convert
              (ChartLocalSuffixState.residualFactorProduct_self
                (K := ℝ)
                (κ := fun _ : Fin (M + 2) ↦ ρ)
                (C := (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed)
                (j := Fin.last (M + 1))) using 1
        _ =
          ChartLocalSuffixState.residualFactorProduct (K := ℝ)
            (κ := fun _ : Fin (M + 2) ↦ ρ)
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
            (Fin.last (M + 1)) (Fin.last (M + 1)) le_rfl := by
            symm
            simp
    rw [hfun]
    simp [Pself]
  have hstep : ∀ n (hns : n + 1 ≤ M),
      motive (n + 1) hns → motive n (Nat.le_of_succ_le hns) := by
    intro n hns ih
    let q : Fin M := ⟨n, Nat.lt_of_succ_le hns⟩
    let p : Fin (M + 1) := q.succ
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let Psucc : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ → Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ)
          (κ := fun _ : Fin (M + 2) ↦ ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
          (Fin.last (M + 1)) p.succ p.succ.le_last
    have hactual :=
      fderiv_retainedPassive_A1seed_residualFactorProduct_succ_castSucc_apply
        (M := M) (ρ := ρ) (κ' := κ') z v q
    have hA1 :=
      retainedPassiveTargetStagedA1passiveTangentAt_fderiv_eq_source
        (ρ := ρ) (κ' := κ') hz v q
    have hstaged :=
      retainedPassiveA1TailTargetStagedFDerivAt_step
        (ρ := ρ) (κ' := κ') z Dzv n (Nat.lt_of_succ_le hns)
    calc
      (fderiv ℝ
        (retainedPassiveA1seedTailProductAt
          (ρ := ρ) (κ' := κ') n (Nat.le_of_succ_le hns)) z) v
          =
        (fderiv ℝ Psucc z) v * data.A1seed p + Psucc z * v.1 q := by
          simpa [retainedPassiveA1seedTailProductAt, q, p, data, Psucc] using hactual
      _ =
        retainedPassiveA1TailTargetStagedFDerivAt
            (ρ := ρ) (κ' := κ') z Dzv (n + 1) hns *
          data.A1seed p +
            Psucc z *
              retainedPassiveTargetStagedA1passiveTangentAt
                (ρ := ρ) (κ' := κ') z Dzv q := by
          have hih :
              (fderiv ℝ Psucc z) v =
                retainedPassiveA1TailTargetStagedFDerivAt
                  (ρ := ρ) (κ' := κ') z Dzv (n + 1) hns := by
            simpa [motive, retainedPassiveA1seedTailProductAt, q, p, Psucc] using ih
          have hA1' :
              retainedPassiveTargetStagedA1passiveTangentAt
                  (ρ := ρ) (κ' := κ') z Dzv q =
                v.1 q := by
            simpa [raw, Dzv] using hA1
          rw [hih, ← hA1']
      _ =
        retainedPassiveA1TailTargetStagedFDerivAt
          (ρ := ρ) (κ' := κ') z Dzv n (Nat.le_of_succ_le hns) := by
          simpa [data, q, p, Psucc] using hstaged.symm
  simpa [motive, raw, Dzv] using
    Nat.decreasingInduction (motive := motive) hstep hbase hm

set_option linter.style.longLine false in
/-- The derivative of the full retained-passive top-left tail after the first
edge is the first value of the target-only recursive staged derivative. -/
theorem fderiv_retainedPassive_A1TailAfterFirst_targetStaged_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let Tfun : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ → Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
    (fderiv ℝ Tfun z) v =
      retainedPassiveA1TailTargetStagedFDerivAt
        (ρ := ρ) (κ' := κ') z ((fderiv ℝ raw z) v) 0 (Nat.zero_le M) := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let Dzv := (fderiv ℝ raw z) v
  let Tfun : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ → Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
  let Pfun :=
    retainedPassiveA1seedTailProductAt
      (ρ := ρ) (κ' := κ') 0 (Nat.zero_le M)
  have htail_eq : Tfun = Pfun := by
    funext y
    simp [Tfun, Pfun, retainedPassiveA1seedTailProductAt,
      ChartLocalSuffixState.retainedPassiveA1TailAfterFirst]
  have hrec :=
    fderiv_retainedPassive_A1seed_residualFactorProduct_targetStaged_apply
      (M := M) (ρ := ρ) (κ' := κ') hz v 0 (Nat.zero_le M)
  calc
    (fderiv ℝ Tfun z) v = (fderiv ℝ Pfun z) v := by
      rw [htail_eq]
    _ =
      retainedPassiveA1TailTargetStagedFDerivAt
        (ρ := ρ) (κ' := κ') z Dzv 0 (Nat.zero_le M) := by
      simpa [raw, Dzv, Pfun] using hrec

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
/-- The first top-left branch can be target-staged using the recursive
target-only derivative of the passive top-left tail. -/
theorem Ctop_tail_recursive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    let Dzv := (fderiv ℝ raw z) v
    let Tail :=
      ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
        data.A1seed
    let dTail :=
      retainedPassiveA1TailTargetStagedFDerivAt
        (ρ := ρ) (κ' := κ') z Dzv 0 (Nat.zero_le M)
    let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
    Dzv.2.2.2.2.1
      - XsuccF2 0 * coord.solvedA3 0
      - coord.F2 (0 : Fin (M + 1)).succ *
          rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv 0
      + Tail⁻¹ * dTail * Tail⁻¹ * coord.Ctop =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.1 := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  let Tfun : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ → Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
  let Tail :=
    ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
      data.A1seed
  let dTailActual := (fderiv ℝ Tfun z) v
  let dTail :=
    retainedPassiveA1TailTargetStagedFDerivAt
      (ρ := ρ) (κ' := κ') z Dzv 0 (Nat.zero_le M)
  let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
  let XsourceF2 := retainedPassiveSourceStagedSuccessorF2 (ρ := ρ) (κ' := κ') v
  let XsourceA3 := retainedPassiveSourceStagedSuccessorA3 (ρ := ρ) (κ' := κ') v
  have hsource :=
    Ctop_tail_fderiv_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (ρ := ρ) (κ' := κ') hz v
  have hF2 :=
    retainedPassiveTargetRecoveredSuccessorF2At_fderiv_eq_sourceStagedSuccessorF2
      (ρ := ρ) (κ' := κ') hz v
  have hA3 :=
    retainedPassive_F2_succ_mul_rawEdgeTupleA3_fderiv_eq_sourceStagedSuccessorA3
      (ρ := ρ) (κ' := κ') hz v (0 : Fin (M + 1))
  have hTail :=
    fderiv_retainedPassive_A1TailAfterFirst_targetStaged_apply
      (ρ := ρ) (κ' := κ') hz v
  change XsuccF2 = XsourceF2 at hF2
  change coord.F2 (0 : Fin (M + 1)).succ *
          rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv 0 =
        coord.F2 (0 : Fin (M + 1)).succ * XsourceA3 0 at hA3
  change dTailActual = dTail at hTail
  change Dzv.2.2.2.2.1
      - XsourceF2 0 * coord.solvedA3 0
      - coord.F2 (0 : Fin (M + 1)).succ * XsourceA3 0
      + Tail⁻¹ * dTailActual * Tail⁻¹ * coord.Ctop =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.1 at hsource
  rw [← hF2] at hsource
  rw [← hA3] at hsource
  rw [hTail] at hsource
  simpa [raw, data, coord, Dzv, Tail, dTail, XsuccF2] using hsource

set_option linter.style.longLine false in
/-- The recursive target-staged first top-left branch recovers the source
`Ctop` tangent after multiplication by the passive tail. -/
theorem Ctop_tail_recursive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    let Dzv := (fderiv ℝ raw z) v
    let Tail :=
      ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
        data.A1seed
    let dTail :=
      retainedPassiveA1TailTargetStagedFDerivAt
        (ρ := ρ) (κ' := κ') z Dzv 0 (Nat.zero_le M)
    let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
    Tail *
      (Dzv.2.2.2.2.1
        - XsuccF2 0 * coord.solvedA3 0
        - coord.F2 (0 : Fin (M + 1)).succ *
            rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv 0
        + Tail⁻¹ * dTail * Tail⁻¹ * coord.Ctop) =
      v.2.2.2.2.1 := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  let Tail :=
    ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
      data.A1seed
  let dTail :=
    retainedPassiveA1TailTargetStagedFDerivAt
      (ρ := ρ) (κ' := κ') z Dzv 0 (Nat.zero_le M)
  let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
  have hCtop :=
    Ctop_tail_recursive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (ρ := ρ) (κ' := κ') hz v
  have hrec :=
    retainedPassiveFormalRawOrderJacobianAt_recovers_Ctop
      (ρ := ρ) (κ' := κ') hz v
  change Dzv.2.2.2.2.1
      - XsuccF2 0 * coord.solvedA3 0
      - coord.F2 (0 : Fin (M + 1)).succ *
          rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv 0
      + Tail⁻¹ * dTail * Tail⁻¹ * coord.Ctop =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.1 at hCtop
  change Tail *
      (Dzv.2.2.2.2.1
        - XsuccF2 0 * coord.solvedA3 0
        - coord.F2 (0 : Fin (M + 1)).succ *
            rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv 0
        + Tail⁻¹ * dTail * Tail⁻¹ * coord.Ctop) =
      v.2.2.2.2.1
  rw [hCtop]
  simpa [Tail, data] using hrec

set_option linter.style.longLine false in
/-- Source `Ctop` tangent recovered from an arbitrary target tuple by the
recursive target-staged first top-left branch. -/
def retainedPassiveTargetRecoveredSourceCtopAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    Matrix ρ ρ ℝ :=
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  let Tail :=
    ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
      data.A1seed
  let dTail :=
    retainedPassiveA1TailTargetStagedFDerivAt
      (ρ := ρ) (κ' := κ') z w 0 (Nat.zero_le M)
  let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z w
  Tail *
    (w.2.2.2.2.1
      - XsuccF2 0 * coord.solvedA3 0
      - coord.F2 (0 : Fin (M + 1)).succ *
          rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') w 0
      + Tail⁻¹ * dTail * Tail⁻¹ * coord.Ctop)

set_option linter.style.longLine false in
/-- The target-recovered source `Ctop` tangent recovers the source `Ctop`
component on raw-order Frechet derivative targets. -/
theorem retainedPassiveTargetRecoveredSourceCtopAt_fderiv_eq_sourceCtop
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    retainedPassiveTargetRecoveredSourceCtopAt
        (ρ := ρ) (κ' := κ') z ((fderiv ℝ raw z) v) =
      v.2.2.2.2.1 := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  simpa [retainedPassiveTargetRecoveredSourceCtopAt, raw] using
    Ctop_tail_recursive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop
      (ρ := ρ) (κ' := κ') hz v

set_option linter.style.longLine false in
/-- Target-only staged tangent for an arbitrary solved `A1` coordinate. -/
def retainedPassiveSolvedA1TargetStagedTangentAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)
    (m : ℕ) (hm : m < M + 1) :
    Matrix ρ ρ ℝ :=
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let Tail :=
    ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
      data.A1seed
  let dTail :=
    retainedPassiveA1TailTargetStagedFDerivAt
      (M := M) (ρ := ρ) (κ' := κ') z w 0 (Nat.zero_le M)
  if h0 : m = 0 then
    Tail⁻¹ * retainedPassiveTargetRecoveredSourceCtopAt
        (M := M) (ρ := ρ) (κ' := κ') z w
      - Tail⁻¹ * dTail * Tail⁻¹ * data.Ctop
  else
    retainedPassiveTargetStagedA1passiveTangentAt
      (M := M) (ρ := ρ) (κ' := κ') z w
      ⟨m - 1, by omega⟩

@[simp]
theorem retainedPassiveSolvedA1TargetStagedTangentAt_zero
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let Tail :=
      ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
        data.A1seed
    let dTail :=
      retainedPassiveA1TailTargetStagedFDerivAt
        (M := M) (ρ := ρ) (κ' := κ') z w 0 (Nat.zero_le M)
    retainedPassiveSolvedA1TargetStagedTangentAt
        (M := M) (ρ := ρ) (κ' := κ') z w 0 (Nat.succ_pos M) =
      Tail⁻¹ * retainedPassiveTargetRecoveredSourceCtopAt
          (M := M) (ρ := ρ) (κ' := κ') z w
        - Tail⁻¹ * dTail * Tail⁻¹ * data.Ctop := by
  simp [retainedPassiveSolvedA1TargetStagedTangentAt]

set_option linter.flexible false in
@[simp]
theorem retainedPassiveSolvedA1TargetStagedTangentAt_succ
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) (s : Fin M) :
    retainedPassiveSolvedA1TargetStagedTangentAt
        (M := M) (ρ := ρ) (κ' := κ') z w (s.val + 1)
        (Nat.succ_lt_succ s.isLt) =
      retainedPassiveTargetStagedA1passiveTangentAt
        (M := M) (ρ := ρ) (κ' := κ') z w s := by
  simp [retainedPassiveSolvedA1TargetStagedTangentAt]

set_option linter.style.longLine false in
/-- On actual raw-order Frechet derivative targets, the target-only solved
`A1` tangent agrees with the actual derivative of the solved `A1` coordinate. -/
theorem retainedPassiveSolvedA1TargetStagedTangentAt_fderiv_eq_source
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)
    (m : ℕ) (hm : m < M + 1) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let A1fun : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →
        Fin (M + 1) → Matrix ρ ρ ℝ :=
      fun y s ↦
        ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 s
    retainedPassiveSolvedA1TargetStagedTangentAt
        (M := M) (ρ := ρ) (κ' := κ') z ((fderiv ℝ raw z) v) m hm =
      (fderiv ℝ
        (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
          A1fun y ⟨m, hm⟩) z) v := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let Dzv := (fderiv ℝ raw z) v
  let A1fun : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →
      Fin (M + 1) → Matrix ρ ρ ℝ :=
    fun y s ↦
      ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 s
  by_cases h0 : m = 0
  · subst m
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let Tfun : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ → Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
    let Tail :=
      ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
        data.A1seed
    let dTailActual := (fderiv ℝ Tfun z) v
    let dTail :=
      retainedPassiveA1TailTargetStagedFDerivAt
        (M := M) (ρ := ρ) (κ' := κ') z Dzv 0 (Nat.zero_le M)
    have hCtop :=
      retainedPassiveTargetRecoveredSourceCtopAt_fderiv_eq_sourceCtop
        (M := M) (ρ := ρ) (κ' := κ') hz v
    have hTail :=
      fderiv_retainedPassive_A1TailAfterFirst_targetStaged_apply
        (M := M) (ρ := ρ) (κ' := κ') hz v
    have hzero :=
      fderiv_retainedPassive_toCoordinateData_solvedA1_zero_apply
        (M := M) (ρ := ρ) (κ' := κ') hz v
    change dTailActual = dTail at hTail
    change (fderiv ℝ (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
        A1fun y 0) z) v =
      Tail⁻¹ * v.2.2.2.2.1 - Tail⁻¹ * dTailActual * Tail⁻¹ * data.Ctop at hzero
    calc
      retainedPassiveSolvedA1TargetStagedTangentAt
          (M := M) (ρ := ρ) (κ' := κ') z Dzv 0 (Nat.succ_pos M)
          =
        Tail⁻¹ * v.2.2.2.2.1 - Tail⁻¹ * dTail * Tail⁻¹ * data.Ctop := by
          simp [retainedPassiveSolvedA1TargetStagedTangentAt, raw, Dzv, data,
            Tail, dTail, hCtop]
      _ =
        Tail⁻¹ * v.2.2.2.2.1 - Tail⁻¹ * dTailActual * Tail⁻¹ * data.Ctop := by
          rw [← hTail]
      _ =
        (fderiv ℝ (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
          A1fun y 0) z) v := hzero.symm
  · let q : Fin M := ⟨m - 1, by omega⟩
    have hidx : (⟨m, hm⟩ : Fin (M + 1)) = q.succ := by
      ext
      simp [q]
      omega
    have hA1 :=
      retainedPassiveTargetStagedA1passiveTangentAt_fderiv_eq_source
        (M := M) (ρ := ρ) (κ' := κ') hz v q
    have hsucc :=
      fderiv_retainedPassive_toCoordinateData_solvedA1_succ_apply
        (M := M) (ρ := ρ) (κ' := κ') z v q
    change retainedPassiveTargetStagedA1passiveTangentAt
        (M := M) (ρ := ρ) (κ' := κ') z Dzv q =
      v.1 q at hA1
    change (fderiv ℝ (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
        A1fun y q.succ) z) v = v.1 q at hsucc
    simp [retainedPassiveSolvedA1TargetStagedTangentAt, raw, Dzv, A1fun,
      h0, q, hA1, ← hsucc, hidx]

set_option linter.style.longLine false in
/-- Target-only recursive derivative for a suffix product of the solved `A1`
family, indexed by the first vertex included in the suffix. -/
def retainedPassiveSolvedA1SuffixTargetStagedFDerivAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)
    (m : ℕ) (hm : m ≤ M + 1) : Matrix ρ ρ ℝ :=
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  Nat.decreasingInduction
    (motive := fun _ _ ↦ Matrix ρ ρ ℝ)
    (fun n hns acc ↦
      let p : Fin (M + 1) := ⟨n, Nat.lt_of_succ_le hns⟩
      let Psucc :=
        ChartLocalSuffixState.residualFactorProduct (K := ℝ)
          (κ := fun _ : Fin (M + 2) ↦ ρ)
          data.toCoordinateData.solvedA1 (Fin.last (M + 1)) p.succ p.succ.le_last
      acc * data.toCoordinateData.solvedA1 p +
        Psucc *
          retainedPassiveSolvedA1TargetStagedTangentAt
            (M := M) (ρ := ρ) (κ' := κ') z w n (Nat.lt_of_succ_le hns))
    0
    hm

@[simp]
theorem retainedPassiveSolvedA1SuffixTargetStagedFDerivAt_self
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ) :
    retainedPassiveSolvedA1SuffixTargetStagedFDerivAt
        (M := M) (ρ := ρ) (κ' := κ') z w (M + 1) le_rfl =
      (0 : Matrix ρ ρ ℝ) := by
  simp [retainedPassiveSolvedA1SuffixTargetStagedFDerivAt]

set_option linter.style.longLine false in
/-- One-step unfold equation for the target-only solved-`A1` suffix
derivative. -/
theorem retainedPassiveSolvedA1SuffixTargetStagedFDerivAt_step
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z w : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)
    (m : ℕ) (hm : m < M + 1) :
    retainedPassiveSolvedA1SuffixTargetStagedFDerivAt
        (M := M) (ρ := ρ) (κ' := κ') z w m (Nat.le_of_lt hm) =
      let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
      let p : Fin (M + 1) := ⟨m, hm⟩
      let Psucc :=
        ChartLocalSuffixState.residualFactorProduct (K := ℝ)
          (κ := fun _ : Fin (M + 2) ↦ ρ)
          data.toCoordinateData.solvedA1 (Fin.last (M + 1)) p.succ p.succ.le_last
      retainedPassiveSolvedA1SuffixTargetStagedFDerivAt
          (M := M) (ρ := ρ) (κ' := κ') z w (m + 1) (Nat.succ_le_of_lt hm) *
        data.toCoordinateData.solvedA1 p +
          Psucc *
            retainedPassiveSolvedA1TargetStagedTangentAt
              (M := M) (ρ := ρ) (κ' := κ') z w m hm := by
  unfold retainedPassiveSolvedA1SuffixTargetStagedFDerivAt
  rw [Nat.decreasingInduction_succ_left]

set_option linter.style.longLine false in
/-- The solved `A1` suffix product beginning at vertex `m`. -/
def retainedPassiveSolvedA1SuffixProductAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (m : ℕ) (hm : m ≤ M + 1) :
    RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ → Matrix ρ ρ ℝ :=
  fun y ↦
    ChartLocalSuffixState.residualFactorProduct (K := ℝ)
      (κ := fun _ : Fin (M + 2) ↦ ρ)
      (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.solvedA1
      (Fin.last (M + 1))
      ⟨m, Nat.lt_succ_of_le hm⟩
      (Fin.val_fin_le.mpr hm)

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- The Frechet derivative of any solved-`A1` suffix product agrees with the
target-only recursive staged expression on actual raw-order derivative
targets. -/
theorem fderiv_retainedPassive_solvedA1_residualFactorProduct_targetStaged_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)
    (m : ℕ) (hm : m ≤ M + 1) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    (fderiv ℝ
      (retainedPassiveSolvedA1SuffixProductAt
        (M := M) (ρ := ρ) (κ' := κ') m hm) z) v =
      retainedPassiveSolvedA1SuffixTargetStagedFDerivAt
        (M := M) (ρ := ρ) (κ' := κ') z ((fderiv ℝ raw z) v) m hm := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let Dzv := (fderiv ℝ raw z) v
  let motive : (m : ℕ) → m ≤ M + 1 → Prop := fun m hm ↦
    (fderiv ℝ
      (retainedPassiveSolvedA1SuffixProductAt
        (M := M) (ρ := ρ) (κ' := κ') m hm) z) v =
      retainedPassiveSolvedA1SuffixTargetStagedFDerivAt
        (M := M) (ρ := ρ) (κ' := κ') z Dzv m hm
  have hbase : motive (M + 1) le_rfl := by
    dsimp [motive]
    rw [retainedPassiveSolvedA1SuffixTargetStagedFDerivAt_self]
    let Pself : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ → Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ)
          (κ := fun _ : Fin (M + 2) ↦ ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.solvedA1
          (Fin.last (M + 1)) (Fin.last (M + 1)) le_rfl
    have hfun :
        retainedPassiveSolvedA1SuffixProductAt
            (M := M) (ρ := ρ) (κ' := κ') (M + 1) le_rfl = Pself := by
      funext y
      dsimp [retainedPassiveSolvedA1SuffixProductAt, Pself]
      congr
    rw [hfun]
    simp [Pself]
  have hstep : ∀ n (hns : n + 1 ≤ M + 1),
      motive (n + 1) hns → motive n (Nat.le_of_succ_le hns) := by
    intro n hns ih
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let p : Fin (M + 1) := ⟨n, Nat.lt_of_succ_le hns⟩
    let A1fun : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ →
        Fin (M + 1) → Matrix ρ ρ ℝ :=
      fun y s ↦
        ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 s
    let Psucc : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ → Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ)
          (κ := fun _ : Fin (M + 2) ↦ ρ)
          (A1fun y) (Fin.last (M + 1)) p.succ p.succ.le_last
    have hactual :=
      fderiv_retainedPassive_solvedA1_residualFactorProduct_castSucc_apply
        (M := M) (ρ := ρ) (κ' := κ') hz v p
    have hcur :=
      retainedPassiveSolvedA1TargetStagedTangentAt_fderiv_eq_source
        (M := M) (ρ := ρ) (κ' := κ') hz v n (Nat.lt_of_succ_le hns)
    have hstaged :=
      retainedPassiveSolvedA1SuffixTargetStagedFDerivAt_step
        (M := M) (ρ := ρ) (κ' := κ') z Dzv n (Nat.lt_of_succ_le hns)
    calc
      (fderiv ℝ
        (retainedPassiveSolvedA1SuffixProductAt
          (M := M) (ρ := ρ) (κ' := κ') n (Nat.le_of_succ_le hns)) z) v
          =
        (fderiv ℝ Psucc z) v * data.toCoordinateData.solvedA1 p +
          Psucc z *
            (fderiv ℝ
              (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
                A1fun y p) z) v := by
          simpa [retainedPassiveSolvedA1SuffixProductAt, data, p, A1fun,
            Psucc] using hactual
      _ =
        retainedPassiveSolvedA1SuffixTargetStagedFDerivAt
            (M := M) (ρ := ρ) (κ' := κ') z Dzv (n + 1) hns *
          data.toCoordinateData.solvedA1 p +
            Psucc z *
              retainedPassiveSolvedA1TargetStagedTangentAt
                (M := M) (ρ := ρ) (κ' := κ') z Dzv n
                (Nat.lt_of_succ_le hns) := by
          have hih :
              (fderiv ℝ Psucc z) v =
                retainedPassiveSolvedA1SuffixTargetStagedFDerivAt
                  (M := M) (ρ := ρ) (κ' := κ') z Dzv (n + 1) hns := by
            simpa [motive, retainedPassiveSolvedA1SuffixProductAt, p, A1fun,
              Psucc] using ih
          have hcur' :
              retainedPassiveSolvedA1TargetStagedTangentAt
                  (M := M) (ρ := ρ) (κ' := κ') z Dzv n
                  (Nat.lt_of_succ_le hns) =
                (fderiv ℝ
                  (fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
                    A1fun y p) z) v := by
            simpa [raw, Dzv, A1fun, p] using hcur
          rw [hih, ← hcur']
      _ =
        retainedPassiveSolvedA1SuffixTargetStagedFDerivAt
          (M := M) (ρ := ρ) (κ' := κ') z Dzv n
          (Nat.le_of_succ_le hns) := by
          simpa [data, p, A1fun, Psucc] using hstaged.symm
  simpa [motive, raw, Dzv] using
    Nat.decreasingInduction (motive := motive) hstep hbase hm

set_option linter.style.longLine false in
/-- Target-only staged tangent for the current solved `A1` factor in the
positive-tail lower-left recurrence. -/
def retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt
    {M : ℕ} {ρ : Type*} {κ' : Fin ((M + 1) + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (z w : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ)
    (m : ℕ) (hm : m < M + 1) :
    Matrix ρ ρ ℝ :=
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let Tail :=
    ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
      data.A1seed
  let dTail :=
    retainedPassiveA1TailTargetStagedFDerivAt
      (M := M + 1) (ρ := ρ) (κ' := κ') z w 0 (Nat.zero_le (M + 1))
  if h0 : m = 0 then
    Tail⁻¹ * retainedPassiveTargetRecoveredSourceCtopAt
        (M := M + 1) (ρ := ρ) (κ' := κ') z w
      - Tail⁻¹ * dTail * Tail⁻¹ * data.Ctop
  else
    retainedPassiveTargetStagedA1passiveTangentAt
      (M := M + 1) (ρ := ρ) (κ' := κ') z w
      ⟨m - 1, by omega⟩

@[simp]
theorem retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt_zero
    {M : ℕ} {ρ : Type*} {κ' : Fin ((M + 1) + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (z w : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ) :
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let Tail :=
      ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
        data.A1seed
    let dTail :=
      retainedPassiveA1TailTargetStagedFDerivAt
        (M := M + 1) (ρ := ρ) (κ' := κ') z w 0 (Nat.zero_le (M + 1))
    retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt
        (M := M) (ρ := ρ) (κ' := κ') z w 0 (Nat.succ_pos M) =
      Tail⁻¹ * retainedPassiveTargetRecoveredSourceCtopAt
          (M := M + 1) (ρ := ρ) (κ' := κ') z w
        - Tail⁻¹ * dTail * Tail⁻¹ * data.Ctop := by
  simp [retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt]

set_option linter.flexible false in
@[simp]
theorem retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt_succ
    {M : ℕ} {ρ : Type*} {κ' : Fin ((M + 1) + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (z w : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ) (s : Fin M) :
    retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt
        (M := M) (ρ := ρ) (κ' := κ') z w (s.val + 1)
        (Nat.succ_lt_succ s.isLt) =
      retainedPassiveTargetStagedA1passiveTangentAt
        (M := M + 1) (ρ := ρ) (κ' := κ') z w s.castSucc := by
  simp [retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt]
  exact congrArg
    (fun q : Fin (M + 1) ↦
      retainedPassiveTargetStagedA1passiveTangentAt
        (M := M + 1) (ρ := ρ) (κ' := κ') z w q)
    (by ext; rfl)

set_option linter.style.longLine false in
/-- On actual raw-order Frechet derivative targets, the target-only current
solved-`A1` tangent agrees with the existing source-direction current tangent. -/
theorem retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt_fderiv_eq_source
    {M : ℕ} {ρ : Type*} {κ' : Fin ((M + 1) + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ)
    (m : ℕ) (hm : m < M + 1) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt
        (M := M) (ρ := ρ) (κ' := κ') z ((fderiv ℝ raw z) v) m hm =
      retainedPassiveLowerLeftTailCurrentTargetSolvedA1TangentAt
        (M := M) (ρ := ρ) (κ' := κ') z v m hm := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let Dzv := (fderiv ℝ raw z) v
  by_cases h0 : m = 0
  · subst m
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let Tfun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ → Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
    let Tail :=
      ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
        data.A1seed
    let dTailActual := (fderiv ℝ Tfun z) v
    let dTail :=
      retainedPassiveA1TailTargetStagedFDerivAt
        (M := M + 1) (ρ := ρ) (κ' := κ') z Dzv 0 (Nat.zero_le (M + 1))
    have hCtop :=
      retainedPassiveTargetRecoveredSourceCtopAt_fderiv_eq_sourceCtop
        (M := M + 1) (ρ := ρ) (κ' := κ') hz v
    have hTail :=
      fderiv_retainedPassive_A1TailAfterFirst_targetStaged_apply
        (M := M + 1) (ρ := ρ) (κ' := κ') hz v
    change dTailActual = dTail at hTail
    simp [retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt,
      retainedPassiveLowerLeftTailCurrentTargetSolvedA1TangentAt,
      raw, Dzv, Tfun, dTailActual, dTail, hCtop, ← hTail]
  · let q : Fin (M + 1) := ⟨m - 1, by omega⟩
    have hA1 :=
      retainedPassiveTargetStagedA1passiveTangentAt_fderiv_eq_source
        (M := M + 1) (ρ := ρ) (κ' := κ') hz v q
    change retainedPassiveTargetStagedA1passiveTangentAt
        (M := M + 1) (ρ := ρ) (κ' := κ') z Dzv q =
      v.1 q at hA1
    simp [retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt,
      retainedPassiveLowerLeftTailCurrentTargetSolvedA1TangentAt,
      raw, Dzv, h0, q, hA1]

set_option linter.style.longLine false in
/-- Target-side one-step RHS for the retained-passive lower-left tail
recurrence, with `dCnext`, current solved-`A1`, suffix-product tangent, and
recursive successor derivative supplied explicitly. -/
def retainedPassiveLowerLeftTailTargetOnlyStepCoreAt
    {M : ℕ} {ρ : Type*} {κ' : Fin ((M + 1) + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (w : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ)
    (q : Fin (M + 1))
    (dAcur dPsucc : Matrix ρ ρ ℝ)
    (dCnext : Matrix (κ' (Fin.last ((M + 1) + 1))) (κ' q.succ.succ) ℝ)
    (dNext : Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ) :
    Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ :=
  let p : Fin ((M + 1) + 1) := q.castSucc
  let r : Fin ((M + 1) + 1) := q.succ
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let A1fun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
      Fin ((M + 1) + 1) → Matrix ρ ρ ℝ :=
    fun y s ↦
      ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 s
  let A3fun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
      ∀ s : Fin ((M + 1) + 1), Matrix (κ' s.succ) ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed
  let Cfun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
      ∀ s : Fin ((M + 1) + 1), Matrix (κ' s.succ) (κ' s.castSucc) ℝ :=
    fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
  let Cprod : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
      Matrix (κ' (Fin.last ((M + 1) + 1))) (κ' r.castSucc) ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ') (Cfun y)
        (Fin.last ((M + 1) + 1)) r.castSucc r.castSucc.le_last
  let Cnext : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
      Matrix (κ' (Fin.last ((M + 1) + 1))) (κ' r.succ) ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ') (Cfun y)
        (Fin.last ((M + 1) + 1)) r.succ r.succ.le_last
  let A3p : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
      Matrix (κ' r.castSucc) ρ ℝ :=
    fun y ↦ by
      simpa [p, r] using A3fun y p
  let dCcur : Matrix (κ' r.succ) (κ' r.castSucc) ℝ :=
    retainedPassiveTargetRecoveredSourceCAt
      (M := M + 1) (ρ := ρ) (κ' := κ') hz w r
  let dG : Matrix (κ' r.castSucc) ρ ℝ := by
    simpa [p, r] using
      rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') w q.castSucc
  let Pcast : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ → Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct
        (K := ℝ) (κ := fun _ : Fin ((M + 1) + 2) ↦ ρ)
        (A1fun y) (Fin.last ((M + 1) + 1)) p.castSucc p.castSucc.le_last
  let Psucc : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ → Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct
        (K := ℝ) (κ := fun _ : Fin ((M + 1) + 2) ↦ ρ)
        (A1fun y) (Fin.last ((M + 1) + 1)) p.succ p.succ.le_last
  let step : Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ :=
    -((dCnext * data.C r + Cnext z * dCcur) * A3p z * (Pcast z)⁻¹)
      - (Cprod z * dG * (Pcast z)⁻¹)
      + Cprod z * A3p z * (Pcast z)⁻¹ *
          (dPsucc * data.toCoordinateData.solvedA1 p + Psucc z * dAcur) *
          (Pcast z)⁻¹
      + dNext
  step

set_option linter.style.longLine false in
/-- On actual raw-order Frechet derivative targets, the target-side one-step
core agrees with the existing source-direction lower-left one-step core. -/
theorem retainedPassiveLowerLeftTailTargetOnlyStepCoreAt_fderiv_eq_sourceStepCore
    {M : ℕ} {ρ : Type*} {κ' : Fin ((M + 1) + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ)
    (q : Fin (M + 1))
    (dAcur dPsucc : Matrix ρ ρ ℝ)
    (dNext : Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let r : Fin ((M + 1) + 1) := q.succ
    let Cfun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        ∀ s : Fin ((M + 1) + 1), Matrix (κ' s.succ) (κ' s.castSucc) ℝ :=
      fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
    let Cnext : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last ((M + 1) + 1))) (κ' r.succ) ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ') (Cfun y)
          (Fin.last ((M + 1) + 1)) r.succ r.succ.le_last
    retainedPassiveLowerLeftTailTargetOnlyStepCoreAt
        (M := M) (ρ := ρ) (κ' := κ') hz ((fderiv ℝ raw z) v)
        q dAcur dPsucc ((fderiv ℝ Cnext z) v) dNext =
      retainedPassiveLowerLeftTailStepCoreAt
        (M := M + 1) (ρ := ρ) (κ' := κ') z v q dAcur dPsucc dNext := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let Dzv := (fderiv ℝ raw z) v
  let r : Fin ((M + 1) + 1) := q.succ
  let Cfun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
      ∀ s : Fin ((M + 1) + 1), Matrix (κ' s.succ) (κ' s.castSucc) ℝ :=
    fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
  let Cnext : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
      Matrix (κ' (Fin.last ((M + 1) + 1))) (κ' r.succ) ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ') (Cfun y)
        (Fin.last ((M + 1) + 1)) r.succ r.succ.le_last
  have hC :=
    retainedPassiveTargetRecoveredSourceCAt_fderiv_eq_sourceC
      (M := M + 1) (ρ := ρ) (κ' := κ') hz v r
  have hGformal :=
    rawEdgeTupleA3_fderiv_topologyTupleEdgeRawOrder_castSucc_eq_formalRawOrderJacobianAt
      (M := M + 1) (ρ := ρ) (κ' := κ') hz v q
  have hGsource :
      rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q.castSucc =
        v.2.2.1 q := by
    rw [hGformal]
    dsimp [retainedPassiveFormalRawOrderJacobianAt]
    rw [retainedPassiveFormalRawOrderJacobian_apply]
  simp [retainedPassiveLowerLeftTailTargetOnlyStepCoreAt,
    retainedPassiveLowerLeftTailStepCoreAt, raw, Dzv, r, hC, hGsource]

set_option linter.style.longLine false in
/-- Target-only staged derivative of the `Cnext` suffix appearing in a
positive-tail lower-left one-step recurrence. -/
def retainedPassiveCnextTargetStagedFDerivAt
    {M : ℕ} {ρ : Type*} {κ' : Fin ((M + 1) + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (w : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ)
    (q : Fin (M + 1)) :
    Matrix (κ' (Fin.last ((M + 1) + 1))) (κ' q.succ.succ) ℝ := by
  let r : Fin ((M + 1) + 1) := q.succ
  let hm : r.succ.val ≤ (M + 1) + 1 := Fin.val_fin_le.mp r.succ.le_last
  simpa [r] using
    retainedPassiveCSuffixTargetStagedFDerivAt
      (M := M + 1) (ρ := ρ) (κ' := κ') hz w r.succ.val hm

set_option linter.style.longLine false in
/-- On actual raw-order Frechet derivative targets, the target-staged `Cnext`
suffix derivative agrees with the Frechet derivative of the concrete `Cnext`
product. -/
theorem retainedPassiveCnextTargetStagedFDerivAt_fderiv_eq_source
    {M : ℕ} {ρ : Type*} {κ' : Fin ((M + 1) + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ)
    (q : Fin (M + 1)) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let r : Fin ((M + 1) + 1) := q.succ
    let Cfun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        ∀ s : Fin ((M + 1) + 1), Matrix (κ' s.succ) (κ' s.castSucc) ℝ :=
      fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
    let Cnext : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last ((M + 1) + 1))) (κ' r.succ) ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ') (Cfun y)
          (Fin.last ((M + 1) + 1)) r.succ r.succ.le_last
    retainedPassiveCnextTargetStagedFDerivAt
        (M := M) (ρ := ρ) (κ' := κ') hz ((fderiv ℝ raw z) v) q =
      (fderiv ℝ Cnext z) v := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let Dzv := (fderiv ℝ raw z) v
  let r : Fin ((M + 1) + 1) := q.succ
  let Cfun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
      ∀ s : Fin ((M + 1) + 1), Matrix (κ' s.succ) (κ' s.castSucc) ℝ :=
    fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
  let Cnext : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
      Matrix (κ' (Fin.last ((M + 1) + 1))) (κ' r.succ) ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ') (Cfun y)
        (Fin.last ((M + 1) + 1)) r.succ r.succ.le_last
  let hm : r.succ.val ≤ (M + 1) + 1 := Fin.val_fin_le.mp r.succ.le_last
  have hrec :=
    fderiv_retainedPassive_C_residualFactorProduct_targetStaged_apply
      (M := M + 1) (ρ := ρ) (κ' := κ') hz v r.succ.val hm
  simpa [retainedPassiveCnextTargetStagedFDerivAt, retainedPassiveCSuffixProductAt,
    raw, Dzv, r, Cfun, Cnext, hm] using hrec.symm

set_option linter.style.longLine false in
/-- The lower-left one-step core with the `Cnext` suffix derivative supplied
by the target-staged `C` suffix recursion. -/
def retainedPassiveLowerLeftTailTargetOnlyStepCoreWithCnextAt
    {M : ℕ} {ρ : Type*} {κ' : Fin ((M + 1) + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (w : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ)
    (q : Fin (M + 1))
    (dAcur dPsucc : Matrix ρ ρ ℝ)
    (dNext : Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ) :
    Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ :=
  retainedPassiveLowerLeftTailTargetOnlyStepCoreAt
    (M := M) (ρ := ρ) (κ' := κ') hz w q dAcur dPsucc
    (retainedPassiveCnextTargetStagedFDerivAt
      (M := M) (ρ := ρ) (κ' := κ') hz w q)
    dNext

set_option linter.style.longLine false in
/-- On actual raw-order Frechet derivative targets, the lower-left one-step
core with target-staged `Cnext` agrees with the existing source-direction
one-step core. -/
theorem retainedPassiveLowerLeftTailTargetOnlyStepCoreWithCnextAt_fderiv_eq_sourceStepCore
    {M : ℕ} {ρ : Type*} {κ' : Fin ((M + 1) + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ)
    (q : Fin (M + 1))
    (dAcur dPsucc : Matrix ρ ρ ℝ)
    (dNext : Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    retainedPassiveLowerLeftTailTargetOnlyStepCoreWithCnextAt
        (M := M) (ρ := ρ) (κ' := κ') hz ((fderiv ℝ raw z) v)
        q dAcur dPsucc dNext =
      retainedPassiveLowerLeftTailStepCoreAt
        (M := M + 1) (ρ := ρ) (κ' := κ') z v q dAcur dPsucc dNext := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let Dzv := (fderiv ℝ raw z) v
  let r : Fin ((M + 1) + 1) := q.succ
  let Cfun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
      ∀ s : Fin ((M + 1) + 1), Matrix (κ' s.succ) (κ' s.castSucc) ℝ :=
    fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
  let Cnext : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
      Matrix (κ' (Fin.last ((M + 1) + 1))) (κ' r.succ) ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ') (Cfun y)
        (Fin.last ((M + 1) + 1)) r.succ r.succ.le_last
  have hCnext :=
    retainedPassiveCnextTargetStagedFDerivAt_fderiv_eq_source
      (M := M) (ρ := ρ) (κ' := κ') hz v q
  have hstep :=
    retainedPassiveLowerLeftTailTargetOnlyStepCoreAt_fderiv_eq_sourceStepCore
      (M := M) (ρ := ρ) (κ' := κ') hz v q dAcur dPsucc dNext
  calc
    retainedPassiveLowerLeftTailTargetOnlyStepCoreWithCnextAt
        (M := M) (ρ := ρ) (κ' := κ') hz Dzv q dAcur dPsucc dNext =
      retainedPassiveLowerLeftTailTargetOnlyStepCoreAt
        (M := M) (ρ := ρ) (κ' := κ') hz Dzv q dAcur dPsucc
        ((fderiv ℝ Cnext z) v) dNext := by
        simp [retainedPassiveLowerLeftTailTargetOnlyStepCoreWithCnextAt,
          raw, Dzv, r, Cfun, Cnext, hCnext]
    _ =
      retainedPassiveLowerLeftTailStepCoreAt
        (M := M + 1) (ρ := ρ) (κ' := κ') z v q dAcur dPsucc dNext := by
        simpa [raw, Dzv, r, Cfun, Cnext] using hstep

set_option linter.style.longLine false in
/-- Target-only recursive derivative for the retained-passive lower-left
zeroed-final tail, with `Cnext`, current solved `A1`, solved-`A1` suffix, and
successor lower-left derivative all target-staged. -/
def retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt
    {M : ℕ} {ρ : Type*} {κ' : Fin ((M + 1) + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (w : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ)
    (m : ℕ) (hm : m ≤ M + 1) :
    Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ :=
  Nat.decreasingInduction
    (motive := fun _ _ ↦ Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ)
    (fun n hns acc ↦
      let q : Fin (M + 1) := ⟨n, Nat.lt_of_succ_le hns⟩
      let p : Fin ((M + 1) + 1) := q.castSucc
      let dPsucc :=
        retainedPassiveSolvedA1SuffixTargetStagedFDerivAt
          (M := M + 1) (ρ := ρ) (κ' := κ') z w
          p.succ.val (Fin.val_fin_le.mp p.succ.le_last)
      retainedPassiveLowerLeftTailTargetOnlyStepCoreWithCnextAt
        (M := M) (ρ := ρ) (κ' := κ') hz w q
        (retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt
          (M := M) (ρ := ρ) (κ' := κ') z w n (Nat.lt_of_succ_le hns))
        dPsucc
        acc)
    0
    hm

@[simp]
theorem retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt_self
    {M : ℕ} {ρ : Type*} {κ' : Fin ((M + 1) + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (w : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ) :
    retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt
        (M := M) (ρ := ρ) (κ' := κ') hz w (M + 1) le_rfl =
      (0 : Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ) := by
  simp [retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt]

set_option linter.style.longLine false in
/-- One-step unfold equation for the recursive target-only lower-left tail
derivative. -/
theorem retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt_step
    {M : ℕ} {ρ : Type*} {κ' : Fin ((M + 1) + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (w : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ)
    (m : ℕ) (hm : m < M + 1) :
    retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt
        (M := M) (ρ := ρ) (κ' := κ') hz w m (Nat.le_of_lt hm) =
      let q : Fin (M + 1) := ⟨m, hm⟩
      let p : Fin ((M + 1) + 1) := q.castSucc
      let dPsucc :=
        retainedPassiveSolvedA1SuffixTargetStagedFDerivAt
          (M := M + 1) (ρ := ρ) (κ' := κ') z w
          p.succ.val (Fin.val_fin_le.mp p.succ.le_last)
      retainedPassiveLowerLeftTailTargetOnlyStepCoreWithCnextAt
        (M := M) (ρ := ρ) (κ' := κ') hz w q
        (retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt
          (M := M) (ρ := ρ) (κ' := κ') z w m hm)
        dPsucc
        (retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt
          (M := M) (ρ := ρ) (κ' := κ') hz w (m + 1) (Nat.succ_le_of_lt hm)) := by
  unfold retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt
  rw [Nat.decreasingInduction_succ_left]

set_option linter.style.longLine false in
/-- First-index unfold equation for the recursive target-only lower-left tail
derivative. -/
theorem retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt_zero
    {M : ℕ} {ρ : Type*} {κ' : Fin ((M + 1) + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (w : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ) :
    let q : Fin (M + 1) := 0
    let p : Fin ((M + 1) + 1) := q.castSucc
    let dPsucc :=
      retainedPassiveSolvedA1SuffixTargetStagedFDerivAt
        (M := M + 1) (ρ := ρ) (κ' := κ') z w
        p.succ.val (Fin.val_fin_le.mp p.succ.le_last)
    retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt
        (M := M) (ρ := ρ) (κ' := κ') hz w 0 (Nat.zero_le (M + 1)) =
      retainedPassiveLowerLeftTailTargetOnlyStepCoreWithCnextAt
        (M := M) (ρ := ρ) (κ' := κ') hz w q
        (retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt
          (M := M) (ρ := ρ) (κ' := κ') z w 0 (Nat.succ_pos M))
        dPsucc
        (retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt
          (M := M) (ρ := ρ) (κ' := κ') hz w 1
          (Nat.succ_le_succ (Nat.zero_le M))) := by
  simpa using
    retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt_step
      (M := M) (ρ := ρ) (κ' := κ') hz w 0 (Nat.succ_pos M)

set_option linter.style.longLine false in
/-- Successor-index unfold equation for the recursive target-only lower-left
tail derivative. -/
theorem retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt_succ
    {M : ℕ} {ρ : Type*} {κ' : Fin ((M + 1) + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (w : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ)
    (s : Fin M) :
    let q : Fin (M + 1) := s.succ
    let p : Fin ((M + 1) + 1) := q.castSucc
    let dPsucc :=
      retainedPassiveSolvedA1SuffixTargetStagedFDerivAt
        (M := M + 1) (ρ := ρ) (κ' := κ') z w
        p.succ.val (Fin.val_fin_le.mp p.succ.le_last)
    retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt
        (M := M) (ρ := ρ) (κ' := κ') hz w (s.val + 1)
        (Nat.le_of_lt (Nat.succ_lt_succ s.isLt)) =
      retainedPassiveLowerLeftTailTargetOnlyStepCoreWithCnextAt
        (M := M) (ρ := ρ) (κ' := κ') hz w q
        (retainedPassiveTargetStagedA1passiveTangentAt
          (M := M + 1) (ρ := ρ) (κ' := κ') z w s.castSucc)
        dPsucc
        (retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt
          (M := M) (ρ := ρ) (κ' := κ') hz w (s.val + 2)
          (Nat.succ_le_of_lt (Nat.succ_lt_succ s.isLt))) := by
  simpa [retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt_succ] using
    retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt_step
      (M := M) (ρ := ρ) (κ' := κ') hz w (s.val + 1)
      (Nat.succ_lt_succ s.isLt)

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- On actual raw-order Frechet derivative targets, the recursive target-only
lower-left expression agrees with the existing source-staged recursion. -/
theorem retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt_fderiv_eq_sourceStaged
    {M : ℕ} {ρ : Type*} {κ' : Fin ((M + 1) + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ)
    (m : ℕ) (hm : m ≤ M + 1) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt
        (M := M) (ρ := ρ) (κ' := κ') hz ((fderiv ℝ raw z) v) m hm =
      retainedPassiveLowerLeftProductTailTargetStagedFDerivAt
        (M := M) (ρ := ρ) (κ' := κ') z v m hm := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let Dzv := (fderiv ℝ raw z) v
  let motive : (m : ℕ) → m ≤ M + 1 → Prop := fun m hm ↦
    retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt
        (M := M) (ρ := ρ) (κ' := κ') hz Dzv m hm =
      retainedPassiveLowerLeftProductTailTargetStagedFDerivAt
        (M := M) (ρ := ρ) (κ' := κ') z v m hm
  have hbase : motive (M + 1) le_rfl := by
    dsimp [motive]
    simp
  have hstep : ∀ n (hns : n + 1 ≤ M + 1),
      motive (n + 1) hns → motive n (Nat.le_of_succ_le hns) := by
    intro n hns ih
    let q : Fin (M + 1) := ⟨n, Nat.lt_of_succ_le hns⟩
    let p : Fin ((M + 1) + 1) := q.castSucc
    let A1fun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        Fin ((M + 1) + 1) → Matrix ρ ρ ℝ :=
      fun y t ↦
        ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 t
    let Psucc : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ → Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ)
          (κ := fun _ : Fin ((M + 1) + 2) ↦ ρ)
          (A1fun y) (Fin.last ((M + 1) + 1)) p.succ p.succ.le_last
    let hpSucc : p.succ.val ≤ (M + 1) + 1 := Fin.val_fin_le.mp p.succ.le_last
    let dAcur :=
      retainedPassiveLowerLeftTailCurrentTargetSolvedA1TangentAt
        (M := M) (ρ := ρ) (κ' := κ') z v n (Nat.lt_of_succ_le hns)
    let dPsucc := (fderiv ℝ Psucc z) v
    let dNext :=
      retainedPassiveLowerLeftProductTailTargetStagedFDerivAt
        (M := M) (ρ := ρ) (κ' := κ') z v (n + 1) hns
    let targetPsucc :=
      retainedPassiveSolvedA1SuffixTargetStagedFDerivAt
        (M := M + 1) (ρ := ρ) (κ' := κ') z Dzv p.succ.val hpSucc
    let targetNext :=
      retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt
        (M := M) (ρ := ρ) (κ' := κ') hz Dzv (n + 1) hns
    have htargetStep :=
      retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt_step
        (M := M) (ρ := ρ) (κ' := κ') hz Dzv n (Nat.lt_of_succ_le hns)
    have hsourceStep :=
      retainedPassiveLowerLeftProductTailTargetStagedFDerivAt_step
        (M := M) (ρ := ρ) (κ' := κ') z v n (Nat.lt_of_succ_le hns)
    have hAcur :=
      retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt_fderiv_eq_source
        (M := M) (ρ := ρ) (κ' := κ') hz v n (Nat.lt_of_succ_le hns)
    have hPsuccBridge :=
      fderiv_retainedPassive_solvedA1_residualFactorProduct_targetStaged_apply
        (M := M + 1) (ρ := ρ) (κ' := κ') hz v p.succ.val hpSucc
    have hPsucc :
        targetPsucc = dPsucc := by
      simpa [retainedPassiveSolvedA1SuffixProductAt, raw, Dzv, A1fun, Psucc,
        dPsucc, targetPsucc, hpSucc] using hPsuccBridge.symm
    have hNext : targetNext = dNext := by
      simpa [targetNext, dNext] using ih
    have hcore :=
      retainedPassiveLowerLeftTailTargetOnlyStepCoreWithCnextAt_fderiv_eq_sourceStepCore
        (M := M) (ρ := ρ) (κ' := κ') hz v q dAcur dPsucc dNext
    calc
      retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt
          (M := M) (ρ := ρ) (κ' := κ') hz Dzv n (Nat.le_of_succ_le hns)
          =
        retainedPassiveLowerLeftTailTargetOnlyStepCoreWithCnextAt
          (M := M) (ρ := ρ) (κ' := κ') hz Dzv q
          (retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt
            (M := M) (ρ := ρ) (κ' := κ') z Dzv n (Nat.lt_of_succ_le hns))
          targetPsucc
          targetNext := by
          simpa [motive, raw, Dzv, q, p, A1fun, Psucc, hpSucc, dAcur, dPsucc,
            dNext, targetPsucc, targetNext] using htargetStep
      _ =
        retainedPassiveLowerLeftTailTargetOnlyStepCoreWithCnextAt
          (M := M) (ρ := ρ) (κ' := κ') hz Dzv q dAcur dPsucc dNext := by
          rw [hAcur, hPsucc, hNext]
      _ =
        retainedPassiveLowerLeftTailStepCoreAt
          (M := M + 1) (ρ := ρ) (κ' := κ') z v q dAcur dPsucc dNext := by
          simpa [raw, Dzv, dAcur, dPsucc, dNext] using hcore
      _ =
        retainedPassiveLowerLeftProductTailTargetStagedFDerivAt
          (M := M) (ρ := ρ) (κ' := κ') z v n (Nat.le_of_succ_le hns) := by
          simpa [q, p, A1fun, Psucc, dAcur, dPsucc, dNext] using hsourceStep.symm
  simpa [motive, raw, Dzv] using
    Nat.decreasingInduction (motive := motive) hstep hbase hm

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- The Frechet derivative of the retained-passive zeroed-final lower-left
tail is the recursive target-only staged expression on the determinant chart. -/
theorem fderiv_retainedPassiveLowerLeftProductTailSum_targetOnly_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin ((M + 1) + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ)
    (m : ℕ) (hm : m ≤ M + 1) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let A1fun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        Fin ((M + 1) + 1) → Matrix ρ ρ ℝ :=
      fun y t ↦
        ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 t
    let A3fun :
        RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
          ∀ t : Fin ((M + 1) + 1), Matrix (κ' t.succ) ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed
    let Cfun :
        RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
          ∀ t : Fin ((M + 1) + 1), Matrix (κ' t.succ) (κ' t.castSucc) ℝ :=
      fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
    let Tailfun :
        RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
          Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
          (K := ℝ) (ρ := ρ) (κ := κ')
          (A1fun y) (A3fun y) (Cfun y) m (hm.trans (Nat.le_succ (M + 1)))
    (fderiv ℝ Tailfun z) v =
      retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt
        (M := M) (ρ := ρ) (κ' := κ') hz ((fderiv ℝ raw z) v) m hm := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let Dzv := (fderiv ℝ raw z) v
  have hsource :=
    fderiv_retainedPassiveLowerLeftProductTailSum_targetStaged_apply
      (M := M) (ρ := ρ) (κ' := κ') hz v m hm
  have htarget :=
    retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt_fderiv_eq_sourceStaged
      (M := M) (ρ := ρ) (κ' := κ') hz v m hm
  calc
    (let A1fun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
          Fin ((M + 1) + 1) → Matrix ρ ρ ℝ :=
        fun y t ↦
          ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 t
      let A3fun :
          RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
            ∀ t : Fin ((M + 1) + 1), Matrix (κ' t.succ) ρ ℝ :=
        fun y ↦
          ChartLocalSuffixState.retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed
      let Cfun :
          RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
            ∀ t : Fin ((M + 1) + 1), Matrix (κ' t.succ) (κ' t.castSucc) ℝ :=
        fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
      let Tailfun :
          RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
            Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ :=
        fun y ↦
          ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
            (K := ℝ) (ρ := ρ) (κ := κ')
            (A1fun y) (A3fun y) (Cfun y) m (hm.trans (Nat.le_succ (M + 1)))
      (fderiv ℝ Tailfun z) v)
        =
      retainedPassiveLowerLeftProductTailTargetStagedFDerivAt
        (M := M) (ρ := ρ) (κ' := κ') z v m hm := by
        simpa [raw] using hsource
    _ =
      retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt
        (M := M) (ρ := ρ) (κ' := κ') hz Dzv m hm := by
        simpa [raw, Dzv] using htarget.symm

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
/-- In the single-edge case, the first top-left branch can be staged using the
target-recovered successor `F2` family and the raw lower-left target readout.
The lower-left readout is used only under the terminal zero extended `F2`
multiplier. -/
theorem Ctop_tail_zero_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
    {ρ : Type*} {κ' : Fin 2 → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := 0) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := 0) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    let Dzv := (fderiv ℝ raw z) v
    let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
    Dzv.2.2.2.2.1
      - XsuccF2 0 * coord.solvedA3 0
      - coord.F2 (0 : Fin 1).succ *
          rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv 0 =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.1 := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
  let XsourceF2 := retainedPassiveSourceStagedSuccessorF2 (ρ := ρ) (κ' := κ') v
  let XsourceA3 := retainedPassiveSourceStagedSuccessorA3 (ρ := ρ) (κ' := κ') v
  have hsource :=
    Ctop_tail_zero_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (ρ := ρ) (κ' := κ') hz v
  have hF2 :=
    retainedPassiveTargetRecoveredSuccessorF2At_fderiv_eq_sourceStagedSuccessorF2
      (ρ := ρ) (κ' := κ') hz v
  have hA3 :=
    retainedPassive_F2_succ_mul_rawEdgeTupleA3_fderiv_eq_sourceStagedSuccessorA3
      (ρ := ρ) (κ' := κ') hz v (0 : Fin 1)
  change XsuccF2 = XsourceF2 at hF2
  change coord.F2 (0 : Fin 1).succ *
          rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv 0 =
        coord.F2 (0 : Fin 1).succ * XsourceA3 0 at hA3
  change Dzv.2.2.2.2.1
      - XsourceF2 0 * coord.solvedA3 0
      - coord.F2 (0 : Fin 1).succ * XsourceA3 0 =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.1 at hsource
  change Dzv.2.2.2.2.1
      - XsuccF2 0 * coord.solvedA3 0
      - coord.F2 (0 : Fin 1).succ *
          rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv 0 =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.1
  rw [hF2]
  rw [hA3]
  exact hsource

set_option linter.style.longLine false in
/-- For positive passive-tail length, the first top-left branch can be staged
using target-recovered successor `F2` and the raw lower-left target readout,
while preserving the explicit first suffix-derivative recurrence term. -/
theorem Ctop_tail_pos_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
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
    let Dzv := (fderiv ℝ raw z) v
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
    let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
    Dzv.2.2.2.2.1
      - XsuccF2 0 * coord.solvedA3 0
      - coord.F2 (0 : Fin (M + 1)).succ *
          rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv 0
      + Tail⁻¹ * ((fderiv ℝ Psucc z) v * data.A1seed p + Psucc z * v.1 q) *
          Tail⁻¹ * coord.Ctop =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.1 := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
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
  let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
  let XsourceF2 := retainedPassiveSourceStagedSuccessorF2 (ρ := ρ) (κ' := κ') v
  let XsourceA3 := retainedPassiveSourceStagedSuccessorA3 (ρ := ρ) (κ' := κ') v
  have hsource :=
    Ctop_tail_pos_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (ρ := ρ) (κ' := κ') hM hz v
  have hF2 :=
    retainedPassiveTargetRecoveredSuccessorF2At_fderiv_eq_sourceStagedSuccessorF2
      (ρ := ρ) (κ' := κ') hz v
  have hA3 :=
    retainedPassive_F2_succ_mul_rawEdgeTupleA3_fderiv_eq_sourceStagedSuccessorA3
      (ρ := ρ) (κ' := κ') hz v (0 : Fin (M + 1))
  change XsuccF2 = XsourceF2 at hF2
  change coord.F2 (0 : Fin (M + 1)).succ *
          rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv 0 =
        coord.F2 (0 : Fin (M + 1)).succ * XsourceA3 0 at hA3
  change Dzv.2.2.2.2.1
      - XsourceF2 0 * coord.solvedA3 0
      - coord.F2 (0 : Fin (M + 1)).succ * XsourceA3 0
      + Tail⁻¹ * ((fderiv ℝ Psucc z) v * data.A1seed p + Psucc z * v.1 q) *
          Tail⁻¹ * coord.Ctop =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.1 at hsource
  change Dzv.2.2.2.2.1
      - XsuccF2 0 * coord.solvedA3 0
      - coord.F2 (0 : Fin (M + 1)).succ *
          rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv 0
      + Tail⁻¹ * ((fderiv ℝ Psucc z) v * data.A1seed p + Psucc z * v.1 q) *
          Tail⁻¹ * coord.Ctop =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.1
  rw [hF2]
  rw [hA3]
  exact hsource

set_option linter.style.longLine false in
/-- For positive passive-tail length, additionally target-stage the first
passive `A1` tangent in the explicit first suffix-derivative recurrence term. -/
theorem Ctop_tail_pos_firstA1_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
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
    let Dzv := (fderiv ℝ raw z) v
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
    let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
    Dzv.2.2.2.2.1
      - XsuccF2 0 * coord.solvedA3 0
      - coord.F2 (0 : Fin (M + 1)).succ *
          rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv 0
      + Tail⁻¹ *
          ((fderiv ℝ Psucc z) v * data.A1seed p +
            Psucc z *
              (Dzv.1 q
                - XsuccF2 q.succ * coord.solvedA3 q.succ
                - coord.F2 q.succ.succ *
                    rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q.succ)) *
          Tail⁻¹ * coord.Ctop =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.1 := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
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
  let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
  have hCtop :=
    Ctop_tail_pos_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (ρ := ρ) (κ' := κ') hM hz v
  have hA1 :=
    A1passive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_A1passive
      (ρ := ρ) (κ' := κ') hz v q
  change Dzv.1 q
      - XsuccF2 q.succ * coord.solvedA3 q.succ
      - coord.F2 q.succ.succ *
          rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q.succ =
      v.1 q at hA1
  change Dzv.2.2.2.2.1
      - XsuccF2 0 * coord.solvedA3 0
      - coord.F2 (0 : Fin (M + 1)).succ *
          rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv 0
      + Tail⁻¹ * ((fderiv ℝ Psucc z) v * data.A1seed p + Psucc z * v.1 q) *
          Tail⁻¹ * coord.Ctop =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.1 at hCtop
  rw [← hA1] at hCtop
  simpa [raw, data, coord, Dzv, Tail, q, p, Psucc, XsuccF2, add_assoc] using hCtop

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- For passive tail length at least two, recurse once into the remaining
suffix derivative in the first-`A1` target-staged `Ctop` bridge and
target-stage the second passive `A1` tangent. -/
theorem Ctop_tail_pos_pos_firstA1_nextA1_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (((M + 1) + 1) + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    let Dzv := (fderiv ℝ raw z) v
    let Tail :=
      ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
        data.A1seed
    let q0 : Fin ((M + 1) + 1) := 0
    let p0 : Fin (((M + 1) + 1) + 1) := q0.succ
    let s0 : Fin (M + 1) := 0
    let q1 : Fin ((M + 1) + 1) := s0.succ
    let p1 : Fin (((M + 1) + 1) + 1) := q1.succ
    let Psucc : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ)
          (κ := fun _ : Fin (((M + 1) + 1) + 2) ↦ ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
          (Fin.last (((M + 1) + 1) + 1)) p0.succ p0.succ.le_last
    let Psucc1 : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ)
          (κ := fun _ : Fin (((M + 1) + 1) + 2) ↦ ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
          (Fin.last (((M + 1) + 1) + 1)) p1.succ p1.succ.le_last
    let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
    Dzv.2.2.2.2.1
      - XsuccF2 0 * coord.solvedA3 0
      - coord.F2 (0 : Fin (((M + 1) + 1) + 1)).succ *
          rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv 0
      + Tail⁻¹ *
          (((fderiv ℝ Psucc1 z) v * data.A1seed p1 +
              Psucc1 z *
                (Dzv.1 q1
                  - XsuccF2 q1.succ * coord.solvedA3 q1.succ
                  - coord.F2 q1.succ.succ *
                      rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q1.succ)) *
            data.A1seed p0 +
              Psucc z *
                (Dzv.1 q0
                  - XsuccF2 q0.succ * coord.solvedA3 q0.succ
                  - coord.F2 q0.succ.succ *
                      rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q0.succ)) *
          Tail⁻¹ * coord.Ctop =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.1 := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  let Tail :=
    ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
      data.A1seed
  let q0 : Fin ((M + 1) + 1) := 0
  let p0 : Fin (((M + 1) + 1) + 1) := q0.succ
  let s0 : Fin (M + 1) := 0
  let q1 : Fin ((M + 1) + 1) := s0.succ
  let p1 : Fin (((M + 1) + 1) + 1) := q1.succ
  let Psucc : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ)
        (κ := fun _ : Fin (((M + 1) + 1) + 2) ↦ ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
        (Fin.last (((M + 1) + 1) + 1)) p0.succ p0.succ.le_last
  let Psucc1 : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ)
        (κ := fun _ : Fin (((M + 1) + 1) + 2) ↦ ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
        (Fin.last (((M + 1) + 1) + 1)) p1.succ p1.succ.le_last
  let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
  have hTail : 0 < (M + 1) + 1 := Nat.succ_pos (M + 1)
  have hCtopBase :=
    Ctop_tail_pos_firstA1_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (M := (M + 1) + 1) (ρ := ρ) (κ' := κ') hTail hz v
  have hCtop :
      Dzv.2.2.2.2.1
        - XsuccF2 0 * coord.solvedA3 0
        - coord.F2 (0 : Fin (((M + 1) + 1) + 1)).succ *
            rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv 0
        + Tail⁻¹ *
            ((fderiv ℝ Psucc z) v * data.A1seed p0 +
              Psucc z *
                (Dzv.1 q0
                  - XsuccF2 q0.succ * coord.solvedA3 q0.succ
                  - coord.F2 q0.succ.succ *
                      rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q0.succ)) *
            Tail⁻¹ * coord.Ctop =
        ((retainedPassiveFormalRawOrderJacobianAt
            (ρ := ρ) (κ' := κ') z) v).2.2.2.2.1 := by
    simpa [raw, data, coord, Dzv, Tail, q0, p0, Psucc, XsuccF2, hTail,
      add_assoc] using hCtopBase
  have hNextBase :=
    fderiv_retainedPassive_A1seed_residualFactorProduct_succ_castSucc_target_staged_apply
      (M := (M + 1) + 1) (ρ := ρ) (κ' := κ') hz v q1
  have hNext : (fderiv ℝ Psucc z) v =
      (fderiv ℝ Psucc1 z) v * data.A1seed p1 +
        Psucc1 z *
          (Dzv.1 q1
            - XsuccF2 q1.succ * coord.solvedA3 q1.succ
            - coord.F2 q1.succ.succ *
                rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q1.succ) := by
    simpa [raw, data, coord, Dzv, q0, p0, s0, q1, p1, Psucc, Psucc1,
      XsuccF2] using hNextBase
  rw [hNext] at hCtop
  simpa [raw, data, coord, Dzv, Tail, q0, p0, s0, q1, p1, Psucc, Psucc1,
    XsuccF2, add_assoc] using hCtop

set_option linter.style.longLine false in
/-- In the single-edge case, the target-staged first top-left branch recovers
the source `Ctop` tangent after multiplication by the passive tail. -/
theorem Ctop_tail_zero_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop
    {ρ : Type*} {κ' : Fin 2 → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := 0) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := 0) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    let Dzv := (fderiv ℝ raw z) v
    let Tail :=
      ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
        data.A1seed
    let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
    Tail *
      (Dzv.2.2.2.2.1
        - XsuccF2 0 * coord.solvedA3 0
        - coord.F2 (0 : Fin 1).succ *
            rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv 0) =
      v.2.2.2.2.1 := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  let Tail :=
    ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
      data.A1seed
  let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
  have hCtop :=
    Ctop_tail_zero_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (ρ := ρ) (κ' := κ') hz v
  have hrec :=
    retainedPassiveFormalRawOrderJacobianAt_recovers_Ctop
      (ρ := ρ) (κ' := κ') hz v
  change Tail *
      (Dzv.2.2.2.2.1
        - XsuccF2 0 * coord.solvedA3 0
        - coord.F2 (0 : Fin 1).succ *
            rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv 0) =
      v.2.2.2.2.1
  change Dzv.2.2.2.2.1
      - XsuccF2 0 * coord.solvedA3 0
      - coord.F2 (0 : Fin 1).succ *
          rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv 0 =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.1 at hCtop
  rw [hCtop]
  simpa [Tail, data] using hrec

set_option linter.style.longLine false in
/-- For positive passive-tail length, the target-staged first top-left branch
with the first tail-derivative recurrence substituted recovers the source
`Ctop` tangent after multiplication by the passive tail. -/
theorem Ctop_tail_pos_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop
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
    let Dzv := (fderiv ℝ raw z) v
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
    let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
    Tail *
      (Dzv.2.2.2.2.1
        - XsuccF2 0 * coord.solvedA3 0
        - coord.F2 (0 : Fin (M + 1)).succ *
            rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv 0
        + Tail⁻¹ * ((fderiv ℝ Psucc z) v * data.A1seed p + Psucc z * v.1 q) *
            Tail⁻¹ * coord.Ctop) =
      v.2.2.2.2.1 := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
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
  let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
  have hCtop :=
    Ctop_tail_pos_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (ρ := ρ) (κ' := κ') hM hz v
  have hrec :=
    retainedPassiveFormalRawOrderJacobianAt_recovers_Ctop
      (ρ := ρ) (κ' := κ') hz v
  change Tail *
      (Dzv.2.2.2.2.1
        - XsuccF2 0 * coord.solvedA3 0
        - coord.F2 (0 : Fin (M + 1)).succ *
            rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv 0
        + Tail⁻¹ * ((fderiv ℝ Psucc z) v * data.A1seed p + Psucc z * v.1 q) *
            Tail⁻¹ * coord.Ctop) =
      v.2.2.2.2.1
  change Dzv.2.2.2.2.1
      - XsuccF2 0 * coord.solvedA3 0
      - coord.F2 (0 : Fin (M + 1)).succ *
          rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv 0
      + Tail⁻¹ * ((fderiv ℝ Psucc z) v * data.A1seed p + Psucc z * v.1 q) *
          Tail⁻¹ * coord.Ctop =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.1 at hCtop
  rw [hCtop]
  simpa [Tail, data] using hrec

set_option linter.style.longLine false in
/-- For positive passive-tail length, the first-`A1` target-staged first
top-left branch recovers the source `Ctop` tangent after multiplication by the
passive tail. -/
theorem Ctop_tail_pos_firstA1_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop
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
    let Dzv := (fderiv ℝ raw z) v
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
    let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
    Tail *
      (Dzv.2.2.2.2.1
        - XsuccF2 0 * coord.solvedA3 0
        - coord.F2 (0 : Fin (M + 1)).succ *
            rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv 0
        + Tail⁻¹ *
            ((fderiv ℝ Psucc z) v * data.A1seed p +
              Psucc z *
                (Dzv.1 q
                  - XsuccF2 q.succ * coord.solvedA3 q.succ
                  - coord.F2 q.succ.succ *
                      rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q.succ)) *
            Tail⁻¹ * coord.Ctop) =
      v.2.2.2.2.1 := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
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
  let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
  have hCtop :=
    Ctop_tail_pos_firstA1_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (ρ := ρ) (κ' := κ') hM hz v
  have hrec :=
    retainedPassiveFormalRawOrderJacobianAt_recovers_Ctop
      (ρ := ρ) (κ' := κ') hz v
  change Tail *
      (Dzv.2.2.2.2.1
        - XsuccF2 0 * coord.solvedA3 0
        - coord.F2 (0 : Fin (M + 1)).succ *
            rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv 0
        + Tail⁻¹ *
            ((fderiv ℝ Psucc z) v * data.A1seed p +
              Psucc z *
                (Dzv.1 q
                  - XsuccF2 q.succ * coord.solvedA3 q.succ
                  - coord.F2 q.succ.succ *
                      rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q.succ)) *
            Tail⁻¹ * coord.Ctop) =
      v.2.2.2.2.1
  change Dzv.2.2.2.2.1
      - XsuccF2 0 * coord.solvedA3 0
      - coord.F2 (0 : Fin (M + 1)).succ *
          rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv 0
      + Tail⁻¹ *
          ((fderiv ℝ Psucc z) v * data.A1seed p +
            Psucc z *
              (Dzv.1 q
                - XsuccF2 q.succ * coord.solvedA3 q.succ
                - coord.F2 q.succ.succ *
                    rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q.succ)) *
          Tail⁻¹ * coord.Ctop =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.1 at hCtop
  rw [hCtop]
  simpa [Tail, data] using hrec

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- For passive tail length at least two, the two-stage target-staged `Ctop`
bridge recovers the source `Ctop` tangent after multiplication by the passive
tail. -/
theorem Ctop_tail_pos_pos_firstA1_nextA1_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop
    {M : ℕ} {ρ : Type*} {κ' : Fin (((M + 1) + 1) + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    let Dzv := (fderiv ℝ raw z) v
    let Tail :=
      ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
        data.A1seed
    let q0 : Fin ((M + 1) + 1) := 0
    let p0 : Fin (((M + 1) + 1) + 1) := q0.succ
    let s0 : Fin (M + 1) := 0
    let q1 : Fin ((M + 1) + 1) := s0.succ
    let p1 : Fin (((M + 1) + 1) + 1) := q1.succ
    let Psucc : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ)
          (κ := fun _ : Fin (((M + 1) + 1) + 2) ↦ ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
          (Fin.last (((M + 1) + 1) + 1)) p0.succ p0.succ.le_last
    let Psucc1 : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ)
          (κ := fun _ : Fin (((M + 1) + 1) + 2) ↦ ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
          (Fin.last (((M + 1) + 1) + 1)) p1.succ p1.succ.le_last
    let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
    Tail *
      (Dzv.2.2.2.2.1
        - XsuccF2 0 * coord.solvedA3 0
        - coord.F2 (0 : Fin (((M + 1) + 1) + 1)).succ *
            rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv 0
        + Tail⁻¹ *
            (((fderiv ℝ Psucc1 z) v * data.A1seed p1 +
                Psucc1 z *
                  (Dzv.1 q1
                    - XsuccF2 q1.succ * coord.solvedA3 q1.succ
                    - coord.F2 q1.succ.succ *
                        rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q1.succ)) *
              data.A1seed p0 +
                Psucc z *
                  (Dzv.1 q0
                    - XsuccF2 q0.succ * coord.solvedA3 q0.succ
                    - coord.F2 q0.succ.succ *
                        rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q0.succ)) *
            Tail⁻¹ * coord.Ctop) =
      v.2.2.2.2.1 := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  let Tail :=
    ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
      data.A1seed
  let q0 : Fin ((M + 1) + 1) := 0
  let p0 : Fin (((M + 1) + 1) + 1) := q0.succ
  let s0 : Fin (M + 1) := 0
  let q1 : Fin ((M + 1) + 1) := s0.succ
  let p1 : Fin (((M + 1) + 1) + 1) := q1.succ
  let Psucc : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ)
        (κ := fun _ : Fin (((M + 1) + 1) + 2) ↦ ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
        (Fin.last (((M + 1) + 1) + 1)) p0.succ p0.succ.le_last
  let Psucc1 : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ)
        (κ := fun _ : Fin (((M + 1) + 1) + 2) ↦ ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
        (Fin.last (((M + 1) + 1) + 1)) p1.succ p1.succ.le_last
  let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
  have hCtop :=
    Ctop_tail_pos_pos_firstA1_nextA1_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (M := M) (ρ := ρ) (κ' := κ') hz v
  have hrec :=
    retainedPassiveFormalRawOrderJacobianAt_recovers_Ctop
      (ρ := ρ) (κ' := κ') hz v
  change Tail *
      (Dzv.2.2.2.2.1
        - XsuccF2 0 * coord.solvedA3 0
        - coord.F2 (0 : Fin (((M + 1) + 1) + 1)).succ *
            rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv 0
        + Tail⁻¹ *
            (((fderiv ℝ Psucc1 z) v * data.A1seed p1 +
                Psucc1 z *
                  (Dzv.1 q1
                    - XsuccF2 q1.succ * coord.solvedA3 q1.succ
                    - coord.F2 q1.succ.succ *
                        rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q1.succ)) *
              data.A1seed p0 +
                Psucc z *
                  (Dzv.1 q0
                    - XsuccF2 q0.succ * coord.solvedA3 q0.succ
                    - coord.F2 q0.succ.succ *
                        rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q0.succ)) *
            Tail⁻¹ * coord.Ctop) =
      v.2.2.2.2.1
  change Dzv.2.2.2.2.1
      - XsuccF2 0 * coord.solvedA3 0
      - coord.F2 (0 : Fin (((M + 1) + 1) + 1)).succ *
          rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv 0
      + Tail⁻¹ *
          (((fderiv ℝ Psucc1 z) v * data.A1seed p1 +
              Psucc1 z *
                (Dzv.1 q1
                  - XsuccF2 q1.succ * coord.solvedA3 q1.succ
                  - coord.F2 q1.succ.succ *
                      rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q1.succ)) *
            data.A1seed p0 +
              Psucc z *
                (Dzv.1 q0
                  - XsuccF2 q0.succ * coord.solvedA3 q0.succ
                  - coord.F2 q0.succ.succ *
                      rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q0.succ)) *
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

set_option linter.style.longLine false in
/-- For positive passive-tail length, the terminal `dLast` factor in the `F3`
bridge can be staged using the target-recovered successor `F2` family and the
raw lower-left target readout at the terminal edge.  The early-tail derivative
remains explicit. -/
theorem F3_tail_pos_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)
    (q : Fin M) (hq : q.succ = Fin.last M) :
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
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    let Dzv := (fderiv ℝ raw z) v
    let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
    Dzv.2.2.2.2.2
      - (fderiv ℝ Earlyfun z) v * coord.solvedA1 (Fin.last M)
      + (coord.F3 - Earlyfun z) *
          (Dzv.1 q
            - XsuccF2 q.succ * coord.solvedA3 q.succ
            - coord.F2 q.succ.succ *
                rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q.succ) =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.2 := by
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
  let Dzv := (fderiv ℝ raw z) v
  let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
  have hF3 :=
    F3_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (ρ := ρ) (κ' := κ') hz v
  have hLastfun :
      Lastfun =
        fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
          ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1
            (Fin.last M) := by
    funext y
    let A : Fin (M + 1) → Matrix ρ ρ ℝ :=
      fun p ↦
        ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p
    have hlast :=
      retainedPassiveLastTopResidualFactorProduct_eq
        (K := ℝ) (ρ := ρ) (M := M) A
    change
      ChartLocalSuffixState.residualFactorProduct
          (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ) A
          (Fin.last (M + 1)) (Fin.last M).castSucc
            (Fin.last M).castSucc.le_last =
        ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1
          (Fin.last M)
    exact hlast
  have hLastfun_q :
      Lastfun =
        fun y : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ ↦
          ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1
            q.succ := by
    rw [hLastfun]
    funext y
    rw [hq]
  have hLastz : Lastfun z = coord.solvedA1 (Fin.last M) := by
    rw [hLastfun]
  have hdLast : (fderiv ℝ Lastfun z) v = v.1 q := by
    rw [hLastfun_q]
    exact
      fderiv_retainedPassive_toCoordinateData_solvedA1_succ_apply
        (ρ := ρ) (κ' := κ') z v q
  have hA1 :=
    A1passive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_A1passive
      (ρ := ρ) (κ' := κ') hz v q
  change Dzv.1 q
      - XsuccF2 q.succ * coord.solvedA3 q.succ
      - coord.F2 q.succ.succ *
          rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q.succ =
      v.1 q at hA1
  change Dzv.2.2.2.2.2
      - (fderiv ℝ Earlyfun z) v * Lastfun z
      + (coord.F3 - Earlyfun z) * (fderiv ℝ Lastfun z) v =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.2 at hF3
  rw [hLastz, hdLast] at hF3
  rw [← hA1] at hF3
  exact hF3

set_option linter.style.longLine false in
/-- For positive passive-tail length, the `F3` bridge with only the terminal
`dLast` factor target-staged recovers the source `F3` tangent by the usual
right-multiplication with the inverse of the negative terminal solved top-left
factor. -/
theorem F3_tail_pos_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M) ρ κ' ℝ)
    (q : Fin M) (hq : q.succ = Fin.last M) :
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
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    let Dzv := (fderiv ℝ raw z) v
    let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
    (Dzv.2.2.2.2.2
      - (fderiv ℝ Earlyfun z) v * coord.solvedA1 (Fin.last M)
      + (coord.F3 - Earlyfun z) *
          (Dzv.1 q
            - XsuccF2 q.succ * coord.solvedA3 q.succ
            - coord.F2 q.succ.succ *
                rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q.succ)) *
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
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
  have hF3 :=
    F3_tail_pos_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (ρ := ρ) (κ' := κ') hz v q hq
  have hrec :=
    retainedPassiveFormalRawOrderJacobianAt_recovers_F3
      (ρ := ρ) (κ' := κ') hz v
  change Dzv.2.2.2.2.2
      - (fderiv ℝ Earlyfun z) v * coord.solvedA1 (Fin.last M)
      + (coord.F3 - Earlyfun z) *
          (Dzv.1 q
            - XsuccF2 q.succ * coord.solvedA3 q.succ
            - coord.F2 q.succ.succ *
                rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q.succ) =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.2 at hF3
  change (Dzv.2.2.2.2.2
      - (fderiv ℝ Earlyfun z) v * coord.solvedA1 (Fin.last M)
      + (coord.F3 - Earlyfun z) *
          (Dzv.1 q
            - XsuccF2 q.succ * coord.solvedA3 q.succ
            - coord.F2 q.succ.succ *
                rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv q.succ)) *
        (-(coord.solvedA1 (Fin.last M)))⁻¹ =
      v.2.2.2.2.2
  rw [hF3]
  simpa [coord, data] using hrec

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- For positive passive-tail length, the `F3` bridge can use the recursive
target-staged expression for the whole early lower-left tail derivative. -/
theorem F3_tail_pos_recursive_dEarly_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
    {M : ℕ} {ρ : Type*} {κ' : Fin ((M + 1) + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    let Dzv := (fderiv ℝ raw z) v
    let qLast : Fin (M + 1) := Fin.last M
    let q0 : Fin (M + 1) := 0
    let p0 : Fin ((M + 1) + 1) := q0.castSucc
    let A1fun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        Fin ((M + 1) + 1) → Matrix ρ ρ ℝ :=
      fun y p ↦
        ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p
    let A3fun :
        RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
          ∀ p : Fin ((M + 1) + 1), Matrix (κ' p.succ) ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed
    let Cfun :
        RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
          ∀ p : Fin ((M + 1) + 1), Matrix (κ' p.succ) (κ' p.castSucc) ℝ :=
      fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
    let Earlyfun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
          (K := ℝ) (ρ := ρ) (κ := κ')
          (A1fun y) (A3fun y) (Cfun y) p0.val (Nat.le_of_lt p0.isLt)
    let dEarly : Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ :=
      retainedPassiveLowerLeftProductTailTargetStagedFDerivAt
        (M := M) (ρ := ρ) (κ' := κ') z v 0 (Nat.zero_le (M + 1))
    let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
    Dzv.2.2.2.2.2
      - dEarly * coord.solvedA1 (Fin.last (M + 1))
      + (coord.F3 - Earlyfun z) *
          (Dzv.1 qLast
            - XsuccF2 qLast.succ * coord.solvedA3 qLast.succ
            - coord.F2 qLast.succ.succ *
                rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv qLast.succ) =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.2 := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  let qLast : Fin (M + 1) := Fin.last M
  let q0 : Fin (M + 1) := 0
  let p0 : Fin ((M + 1) + 1) := q0.castSucc
  let A1fun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
      Fin ((M + 1) + 1) → Matrix ρ ρ ℝ :=
    fun y p ↦
      ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p
  let A3fun :
      RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        ∀ p : Fin ((M + 1) + 1), Matrix (κ' p.succ) ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed
  let Cfun :
      RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        ∀ p : Fin ((M + 1) + 1), Matrix (κ' p.succ) (κ' p.castSucc) ℝ :=
    fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
  let Earlyfun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
      Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
        (K := ℝ) (ρ := ρ) (κ := κ')
        (A1fun y) (A3fun y) (Cfun y) p0.val (Nat.le_of_lt p0.isLt)
  let dEarly : Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ :=
    retainedPassiveLowerLeftProductTailTargetStagedFDerivAt
      (M := M) (ρ := ρ) (κ' := κ') z v 0 (Nat.zero_le (M + 1))
  let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
  have hqLast : qLast.succ = Fin.last (M + 1) := rfl
  have hF3base :=
    F3_tail_pos_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (M := M + 1) (ρ := ρ) (κ' := κ') hz v qLast hqLast
  have hF3 :
      Dzv.2.2.2.2.2
        - (fderiv ℝ Earlyfun z) v * coord.solvedA1 (Fin.last (M + 1))
        + (coord.F3 - Earlyfun z) *
            (Dzv.1 qLast
              - XsuccF2 qLast.succ * coord.solvedA3 qLast.succ
              - coord.F2 qLast.succ.succ *
                  rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv qLast.succ) =
        ((retainedPassiveFormalRawOrderJacobianAt
            (ρ := ρ) (κ' := κ') z) v).2.2.2.2.2 := by
    simpa [A1fun, A3fun, Cfun, Earlyfun, data, coord, Dzv, XsuccF2,
      qLast, q0, p0] using hF3base
  have hEarlyBase :=
    fderiv_retainedPassiveLowerLeftProductTailSum_targetStaged_apply
      (M := M) (ρ := ρ) (κ' := κ') hz v 0 (Nat.zero_le (M + 1))
  have hEarly : (fderiv ℝ Earlyfun z) v = dEarly := by
    simpa [A1fun, A3fun, Cfun, Earlyfun, dEarly, q0, p0] using hEarlyBase
  rw [hEarly] at hF3
  exact hF3

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- The positive-tail `F3` bridge with recursive `dEarly` recovers the source
`F3` tangent by the usual right-multiplication with the inverse of the
negative terminal solved top-left factor. -/
theorem F3_tail_pos_recursive_dEarly_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3
    {M : ℕ} {ρ : Type*} {κ' : Fin ((M + 1) + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    let Dzv := (fderiv ℝ raw z) v
    let qLast : Fin (M + 1) := Fin.last M
    let q0 : Fin (M + 1) := 0
    let p0 : Fin ((M + 1) + 1) := q0.castSucc
    let A1fun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        Fin ((M + 1) + 1) → Matrix ρ ρ ℝ :=
      fun y p ↦
        ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p
    let A3fun :
        RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
          ∀ p : Fin ((M + 1) + 1), Matrix (κ' p.succ) ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed
    let Cfun :
        RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
          ∀ p : Fin ((M + 1) + 1), Matrix (κ' p.succ) (κ' p.castSucc) ℝ :=
      fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
    let Earlyfun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
          (K := ℝ) (ρ := ρ) (κ := κ')
          (A1fun y) (A3fun y) (Cfun y) p0.val (Nat.le_of_lt p0.isLt)
    let dEarly : Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ :=
      retainedPassiveLowerLeftProductTailTargetStagedFDerivAt
        (M := M) (ρ := ρ) (κ' := κ') z v 0 (Nat.zero_le (M + 1))
    let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
    (Dzv.2.2.2.2.2
      - dEarly * coord.solvedA1 (Fin.last (M + 1))
      + (coord.F3 - Earlyfun z) *
          (Dzv.1 qLast
            - XsuccF2 qLast.succ * coord.solvedA3 qLast.succ
            - coord.F2 qLast.succ.succ *
                rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv qLast.succ)) *
        (-(coord.solvedA1 (Fin.last (M + 1))))⁻¹ =
      v.2.2.2.2.2 := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  let qLast : Fin (M + 1) := Fin.last M
  let q0 : Fin (M + 1) := 0
  let p0 : Fin ((M + 1) + 1) := q0.castSucc
  let A1fun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
      Fin ((M + 1) + 1) → Matrix ρ ρ ℝ :=
    fun y p ↦
      ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p
  let A3fun :
      RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        ∀ p : Fin ((M + 1) + 1), Matrix (κ' p.succ) ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed
  let Cfun :
      RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        ∀ p : Fin ((M + 1) + 1), Matrix (κ' p.succ) (κ' p.castSucc) ℝ :=
    fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
  let Earlyfun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
      Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
        (K := ℝ) (ρ := ρ) (κ := κ')
        (A1fun y) (A3fun y) (Cfun y) p0.val (Nat.le_of_lt p0.isLt)
  let dEarly : Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ :=
    retainedPassiveLowerLeftProductTailTargetStagedFDerivAt
      (M := M) (ρ := ρ) (κ' := κ') z v 0 (Nat.zero_le (M + 1))
  let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
  have hF3 :=
    F3_tail_pos_recursive_dEarly_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (M := M) (ρ := ρ) (κ' := κ') hz v
  have hrec :=
    retainedPassiveFormalRawOrderJacobianAt_recovers_F3
      (ρ := ρ) (κ' := κ') hz v
  change Dzv.2.2.2.2.2
      - dEarly * coord.solvedA1 (Fin.last (M + 1))
      + (coord.F3 - Earlyfun z) *
          (Dzv.1 qLast
            - XsuccF2 qLast.succ * coord.solvedA3 qLast.succ
            - coord.F2 qLast.succ.succ *
                rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv qLast.succ) =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.2 at hF3
  change (Dzv.2.2.2.2.2
      - dEarly * coord.solvedA1 (Fin.last (M + 1))
      + (coord.F3 - Earlyfun z) *
          (Dzv.1 qLast
            - XsuccF2 qLast.succ * coord.solvedA3 qLast.succ
            - coord.F2 qLast.succ.succ *
                rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv qLast.succ)) *
        (-(coord.solvedA1 (Fin.last (M + 1))))⁻¹ =
      v.2.2.2.2.2
  rw [hF3]
  simpa [coord, data] using hrec

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- For positive passive-tail length, the `F3` bridge can use the target-only
recursive lower-left derivative in the whole early-tail slot. -/
theorem F3_tail_pos_targetOnly_dEarly_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
    {M : ℕ} {ρ : Type*} {κ' : Fin ((M + 1) + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    let Dzv := (fderiv ℝ raw z) v
    let qLast : Fin (M + 1) := Fin.last M
    let q0 : Fin (M + 1) := 0
    let p0 : Fin ((M + 1) + 1) := q0.castSucc
    let A1fun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        Fin ((M + 1) + 1) → Matrix ρ ρ ℝ :=
      fun y p ↦
        ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p
    let A3fun :
        RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
          ∀ p : Fin ((M + 1) + 1), Matrix (κ' p.succ) ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed
    let Cfun :
        RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
          ∀ p : Fin ((M + 1) + 1), Matrix (κ' p.succ) (κ' p.castSucc) ℝ :=
      fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
    let Earlyfun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
          (K := ℝ) (ρ := ρ) (κ := κ')
          (A1fun y) (A3fun y) (Cfun y) p0.val (Nat.le_of_lt p0.isLt)
    let dEarly : Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ :=
      retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt
        (M := M) (ρ := ρ) (κ' := κ') hz Dzv 0 (Nat.zero_le (M + 1))
    let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
    Dzv.2.2.2.2.2
      - dEarly * coord.solvedA1 (Fin.last (M + 1))
      + (coord.F3 - Earlyfun z) *
          (Dzv.1 qLast
            - XsuccF2 qLast.succ * coord.solvedA3 qLast.succ
            - coord.F2 qLast.succ.succ *
                rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv qLast.succ) =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.2 := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  let qLast : Fin (M + 1) := Fin.last M
  let q0 : Fin (M + 1) := 0
  let p0 : Fin ((M + 1) + 1) := q0.castSucc
  let A1fun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
      Fin ((M + 1) + 1) → Matrix ρ ρ ℝ :=
    fun y p ↦
      ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p
  let A3fun :
      RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        ∀ p : Fin ((M + 1) + 1), Matrix (κ' p.succ) ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed
  let Cfun :
      RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        ∀ p : Fin ((M + 1) + 1), Matrix (κ' p.succ) (κ' p.castSucc) ℝ :=
    fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
  let Earlyfun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
      Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
        (K := ℝ) (ρ := ρ) (κ := κ')
        (A1fun y) (A3fun y) (Cfun y) p0.val (Nat.le_of_lt p0.isLt)
  let dEarly : Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ :=
    retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt
      (M := M) (ρ := ρ) (κ' := κ') hz Dzv 0 (Nat.zero_le (M + 1))
  let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
  have hF3 :=
    F3_tail_pos_recursive_dEarly_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (M := M) (ρ := ρ) (κ' := κ') hz v
  have hEarly :=
    retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt_fderiv_eq_sourceStaged
      (M := M) (ρ := ρ) (κ' := κ') hz v 0 (Nat.zero_le (M + 1))
  simpa [A1fun, A3fun, Cfun, Earlyfun, dEarly, data, coord, Dzv, XsuccF2,
    qLast, q0, p0, hEarly] using hF3

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- The positive-tail `F3` bridge with target-only `dEarly` recovers the source
`F3` tangent by the usual right-multiplication with the inverse of the
negative terminal solved top-left factor. -/
theorem F3_tail_pos_targetOnly_dEarly_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3
    {M : ℕ} {ρ : Type*} {κ' : Fin ((M + 1) + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    let Dzv := (fderiv ℝ raw z) v
    let qLast : Fin (M + 1) := Fin.last M
    let q0 : Fin (M + 1) := 0
    let p0 : Fin ((M + 1) + 1) := q0.castSucc
    let A1fun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        Fin ((M + 1) + 1) → Matrix ρ ρ ℝ :=
      fun y p ↦
        ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p
    let A3fun :
        RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
          ∀ p : Fin ((M + 1) + 1), Matrix (κ' p.succ) ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed
    let Cfun :
        RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
          ∀ p : Fin ((M + 1) + 1), Matrix (κ' p.succ) (κ' p.castSucc) ℝ :=
      fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
    let Earlyfun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
          (K := ℝ) (ρ := ρ) (κ := κ')
          (A1fun y) (A3fun y) (Cfun y) p0.val (Nat.le_of_lt p0.isLt)
    let dEarly : Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ :=
      retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt
        (M := M) (ρ := ρ) (κ' := κ') hz Dzv 0 (Nat.zero_le (M + 1))
    let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
    (Dzv.2.2.2.2.2
      - dEarly * coord.solvedA1 (Fin.last (M + 1))
      + (coord.F3 - Earlyfun z) *
          (Dzv.1 qLast
            - XsuccF2 qLast.succ * coord.solvedA3 qLast.succ
            - coord.F2 qLast.succ.succ *
                rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv qLast.succ)) *
        (-(coord.solvedA1 (Fin.last (M + 1))))⁻¹ =
      v.2.2.2.2.2 := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  let qLast : Fin (M + 1) := Fin.last M
  let q0 : Fin (M + 1) := 0
  let p0 : Fin ((M + 1) + 1) := q0.castSucc
  let A1fun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
      Fin ((M + 1) + 1) → Matrix ρ ρ ℝ :=
    fun y p ↦
      ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p
  let A3fun :
      RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        ∀ p : Fin ((M + 1) + 1), Matrix (κ' p.succ) ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed
  let Cfun :
      RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        ∀ p : Fin ((M + 1) + 1), Matrix (κ' p.succ) (κ' p.castSucc) ℝ :=
    fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
  let Earlyfun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
      Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
        (K := ℝ) (ρ := ρ) (κ := κ')
        (A1fun y) (A3fun y) (Cfun y) p0.val (Nat.le_of_lt p0.isLt)
  let dEarly : Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ :=
    retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt
      (M := M) (ρ := ρ) (κ' := κ') hz Dzv 0 (Nat.zero_le (M + 1))
  let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
  have hF3 :=
    F3_tail_pos_recursive_dEarly_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3
      (M := M) (ρ := ρ) (κ' := κ') hz v
  have hEarly :=
    retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt_fderiv_eq_sourceStaged
      (M := M) (ρ := ρ) (κ' := κ') hz v 0 (Nat.zero_le (M + 1))
  simpa [A1fun, A3fun, Cfun, Earlyfun, dEarly, data, coord, Dzv, XsuccF2,
    qLast, q0, p0, hEarly] using hF3

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- For a positive passive tail written as `M+1`, substitute the first-index
`dEarly` recurrence into the `F3` bridge whose terminal `dLast` factor is
already target-staged. -/
theorem F3_tail_pos_dEarly_zero_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
    {M : ℕ} {ρ : Type*} {κ' : Fin ((M + 1) + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    let Dzv := (fderiv ℝ raw z) v
    let qLast : Fin (M + 1) := Fin.last M
    let q0 : Fin (M + 1) := 0
    let p0 : Fin ((M + 1) + 1) := q0.castSucc
    let r0 : Fin ((M + 1) + 1) := q0.succ
    let A1fun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        Fin ((M + 1) + 1) → Matrix ρ ρ ℝ :=
      fun y p ↦
        ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p
    let A3fun :
        RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
          ∀ p : Fin ((M + 1) + 1), Matrix (κ' p.succ) ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed
    let Cfun :
        RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
          ∀ p : Fin ((M + 1) + 1), Matrix (κ' p.succ) (κ' p.castSucc) ℝ :=
      fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
    let Earlyfun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
          (K := ℝ) (ρ := ρ) (κ := κ')
          (A1fun y) (A3fun y) (Cfun y) p0.val (Nat.le_of_lt p0.isLt)
    let Cprod :
        RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
          Matrix (κ' (Fin.last ((M + 1) + 1))) (κ' r0.castSucc) ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
          (Cfun y) (Fin.last ((M + 1) + 1)) r0.castSucc r0.castSucc.le_last
    let Cnext :
        RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
          Matrix (κ' (Fin.last ((M + 1) + 1))) (κ' r0.succ) ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
          (Cfun y) (Fin.last ((M + 1) + 1)) r0.succ r0.succ.le_last
    let A3p :
        RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
          Matrix (κ' r0.castSucc) ρ ℝ :=
      fun y ↦ by
        simpa [p0, r0] using A3fun y p0
    let dG : Matrix (κ' r0.castSucc) ρ ℝ := by
      simpa [p0, r0] using v.2.2.1 q0
    let Pcast : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct
          (K := ℝ) (κ := fun _ : Fin ((M + 1) + 2) ↦ ρ)
          (A1fun y) (Fin.last ((M + 1) + 1)) p0.castSucc p0.castSucc.le_last
    let Psucc : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct
          (K := ℝ) (κ := fun _ : Fin ((M + 1) + 2) ↦ ρ)
          (A1fun y) (Fin.last ((M + 1) + 1)) p0.succ p0.succ.le_last
    let dPsucc := (fderiv ℝ Psucc z) v
    let Tfun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
    let Tail := ChartLocalSuffixState.retainedPassiveA1TailAfterFirst
      (K := ℝ) (ρ := ρ) data.A1seed
    let dTail := (fderiv ℝ Tfun z) v
    let Nextfun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
          (K := ℝ) (ρ := ρ) (κ := κ')
          (A1fun y) (A3fun y) (Cfun y) (p0.val + 1)
          (Nat.succ_le_of_lt p0.isLt)
    let dEarly : Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ :=
      -(((fderiv ℝ Cnext z) v * data.C r0 + Cnext z * v.2.2.2.1 r0) *
          A3p z * (Pcast z)⁻¹)
        - (Cprod z * dG * (Pcast z)⁻¹)
        + Cprod z * A3p z * (Pcast z)⁻¹ *
            (dPsucc * coord.solvedA1 p0 +
              Psucc z *
                (Tail⁻¹ * v.2.2.2.2.1 -
                  Tail⁻¹ * dTail * Tail⁻¹ * data.Ctop)) *
            (Pcast z)⁻¹
        + (fderiv ℝ Nextfun z) v
    let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
    Dzv.2.2.2.2.2
      - dEarly * coord.solvedA1 (Fin.last (M + 1))
      + (coord.F3 - Earlyfun z) *
          (Dzv.1 qLast
            - XsuccF2 qLast.succ * coord.solvedA3 qLast.succ
            - coord.F2 qLast.succ.succ *
                rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv qLast.succ) =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.2 := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  let qLast : Fin (M + 1) := Fin.last M
  let q0 : Fin (M + 1) := 0
  let p0 : Fin ((M + 1) + 1) := q0.castSucc
  let r0 : Fin ((M + 1) + 1) := q0.succ
  let A1fun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
      Fin ((M + 1) + 1) → Matrix ρ ρ ℝ :=
    fun y p ↦
      ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p
  let A3fun :
      RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        ∀ p : Fin ((M + 1) + 1), Matrix (κ' p.succ) ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed
  let Cfun :
      RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        ∀ p : Fin ((M + 1) + 1), Matrix (κ' p.succ) (κ' p.castSucc) ℝ :=
    fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
  let Earlyfun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
      Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
        (K := ℝ) (ρ := ρ) (κ := κ')
        (A1fun y) (A3fun y) (Cfun y) p0.val (Nat.le_of_lt p0.isLt)
  let Cprod :
      RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last ((M + 1) + 1))) (κ' r0.castSucc) ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
        (Cfun y) (Fin.last ((M + 1) + 1)) r0.castSucc r0.castSucc.le_last
  let Cnext :
      RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last ((M + 1) + 1))) (κ' r0.succ) ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
        (Cfun y) (Fin.last ((M + 1) + 1)) r0.succ r0.succ.le_last
  let A3p :
      RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        Matrix (κ' r0.castSucc) ρ ℝ :=
    fun y ↦ by
      simpa [p0, r0] using A3fun y p0
  let dG : Matrix (κ' r0.castSucc) ρ ℝ := by
    simpa [p0, r0] using v.2.2.1 q0
  let Pcast : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct
        (K := ℝ) (κ := fun _ : Fin ((M + 1) + 2) ↦ ρ)
        (A1fun y) (Fin.last ((M + 1) + 1)) p0.castSucc p0.castSucc.le_last
  let Psucc : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct
        (K := ℝ) (κ := fun _ : Fin ((M + 1) + 2) ↦ ρ)
        (A1fun y) (Fin.last ((M + 1) + 1)) p0.succ p0.succ.le_last
  let dPsucc := (fderiv ℝ Psucc z) v
  let Tfun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
  let Tail := ChartLocalSuffixState.retainedPassiveA1TailAfterFirst
    (K := ℝ) (ρ := ρ) data.A1seed
  let dTail := (fderiv ℝ Tfun z) v
  let Nextfun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
      Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
        (K := ℝ) (ρ := ρ) (κ := κ')
        (A1fun y) (A3fun y) (Cfun y) (p0.val + 1)
        (Nat.succ_le_of_lt p0.isLt)
  let dEarly : Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ :=
    -(((fderiv ℝ Cnext z) v * data.C r0 + Cnext z * v.2.2.2.1 r0) *
        A3p z * (Pcast z)⁻¹)
      - (Cprod z * dG * (Pcast z)⁻¹)
      + Cprod z * A3p z * (Pcast z)⁻¹ *
          (dPsucc * coord.solvedA1 p0 +
            Psucc z *
              (Tail⁻¹ * v.2.2.2.2.1 -
                Tail⁻¹ * dTail * Tail⁻¹ * data.Ctop)) *
          (Pcast z)⁻¹
      + (fderiv ℝ Nextfun z) v
  let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
  have hqLast : qLast.succ = Fin.last (M + 1) := rfl
  have hF3base :=
    F3_tail_pos_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (M := M + 1) (ρ := ρ) (κ' := κ') hz v qLast hqLast
  have hF3 :
      Dzv.2.2.2.2.2
        - (fderiv ℝ Earlyfun z) v * coord.solvedA1 (Fin.last (M + 1))
        + (coord.F3 - Earlyfun z) *
            (Dzv.1 qLast
              - XsuccF2 qLast.succ * coord.solvedA3 qLast.succ
              - coord.F2 qLast.succ.succ *
                  rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv qLast.succ) =
        ((retainedPassiveFormalRawOrderJacobianAt
            (ρ := ρ) (κ' := κ') z) v).2.2.2.2.2 := by
    simpa [A1fun, A3fun, Cfun, Earlyfun, data, coord, Dzv, XsuccF2, qLast,
      q0, p0] using hF3base
  have hEarlyBase :=
    fderiv_retainedPassiveLowerLeftProductTailSum_zero_product_dCprod_dG_dPcast_apply
      (M := M) (ρ := ρ) (κ' := κ') hz v
  have hEarly : (fderiv ℝ Earlyfun z) v = dEarly := by
    simpa [A1fun, A3fun, Cfun, Earlyfun, Cprod, Cnext, A3p, dG, Pcast,
      Psucc, dPsucc, Tfun, Tail, dTail, Nextfun, dEarly, data, coord, q0, p0,
      r0] using hEarlyBase
  rw [hEarly] at hF3
  exact hF3

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- The positive-tail `F3` bridge with the first-index `dEarly` recurrence
substituted recovers the source `F3` tangent by the usual right-multiplication
with the inverse of the negative terminal solved top-left factor. -/
theorem F3_tail_pos_dEarly_zero_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3
    {M : ℕ} {ρ : Type*} {κ' : Fin ((M + 1) + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    let Dzv := (fderiv ℝ raw z) v
    let qLast : Fin (M + 1) := Fin.last M
    let q0 : Fin (M + 1) := 0
    let p0 : Fin ((M + 1) + 1) := q0.castSucc
    let r0 : Fin ((M + 1) + 1) := q0.succ
    let A1fun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        Fin ((M + 1) + 1) → Matrix ρ ρ ℝ :=
      fun y p ↦
        ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p
    let A3fun :
        RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
          ∀ p : Fin ((M + 1) + 1), Matrix (κ' p.succ) ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed
    let Cfun :
        RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
          ∀ p : Fin ((M + 1) + 1), Matrix (κ' p.succ) (κ' p.castSucc) ℝ :=
      fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
    let Earlyfun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
          (K := ℝ) (ρ := ρ) (κ := κ')
          (A1fun y) (A3fun y) (Cfun y) p0.val (Nat.le_of_lt p0.isLt)
    let Cprod :
        RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
          Matrix (κ' (Fin.last ((M + 1) + 1))) (κ' r0.castSucc) ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
          (Cfun y) (Fin.last ((M + 1) + 1)) r0.castSucc r0.castSucc.le_last
    let Cnext :
        RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
          Matrix (κ' (Fin.last ((M + 1) + 1))) (κ' r0.succ) ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
          (Cfun y) (Fin.last ((M + 1) + 1)) r0.succ r0.succ.le_last
    let A3p :
        RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
          Matrix (κ' r0.castSucc) ρ ℝ :=
      fun y ↦ by
        simpa [p0, r0] using A3fun y p0
    let dG : Matrix (κ' r0.castSucc) ρ ℝ := by
      simpa [p0, r0] using v.2.2.1 q0
    let Pcast : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct
          (K := ℝ) (κ := fun _ : Fin ((M + 1) + 2) ↦ ρ)
          (A1fun y) (Fin.last ((M + 1) + 1)) p0.castSucc p0.castSucc.le_last
    let Psucc : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct
          (K := ℝ) (κ := fun _ : Fin ((M + 1) + 2) ↦ ρ)
          (A1fun y) (Fin.last ((M + 1) + 1)) p0.succ p0.succ.le_last
    let dPsucc := (fderiv ℝ Psucc z) v
    let Tfun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
    let Tail := ChartLocalSuffixState.retainedPassiveA1TailAfterFirst
      (K := ℝ) (ρ := ρ) data.A1seed
    let dTail := (fderiv ℝ Tfun z) v
    let Nextfun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
          (K := ℝ) (ρ := ρ) (κ := κ')
          (A1fun y) (A3fun y) (Cfun y) (p0.val + 1)
          (Nat.succ_le_of_lt p0.isLt)
    let dEarly : Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ :=
      -(((fderiv ℝ Cnext z) v * data.C r0 + Cnext z * v.2.2.2.1 r0) *
          A3p z * (Pcast z)⁻¹)
        - (Cprod z * dG * (Pcast z)⁻¹)
        + Cprod z * A3p z * (Pcast z)⁻¹ *
            (dPsucc * coord.solvedA1 p0 +
              Psucc z *
                (Tail⁻¹ * v.2.2.2.2.1 -
                  Tail⁻¹ * dTail * Tail⁻¹ * data.Ctop)) *
            (Pcast z)⁻¹
        + (fderiv ℝ Nextfun z) v
    let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
    (Dzv.2.2.2.2.2
      - dEarly * coord.solvedA1 (Fin.last (M + 1))
      + (coord.F3 - Earlyfun z) *
          (Dzv.1 qLast
            - XsuccF2 qLast.succ * coord.solvedA3 qLast.succ
            - coord.F2 qLast.succ.succ *
                rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv qLast.succ)) *
        (-(coord.solvedA1 (Fin.last (M + 1))))⁻¹ =
      v.2.2.2.2.2 := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  let qLast : Fin (M + 1) := Fin.last M
  let q0 : Fin (M + 1) := 0
  let p0 : Fin ((M + 1) + 1) := q0.castSucc
  let r0 : Fin ((M + 1) + 1) := q0.succ
  let A1fun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
      Fin ((M + 1) + 1) → Matrix ρ ρ ℝ :=
    fun y p ↦
      ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p
  let A3fun :
      RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        ∀ p : Fin ((M + 1) + 1), Matrix (κ' p.succ) ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed
  let Cfun :
      RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        ∀ p : Fin ((M + 1) + 1), Matrix (κ' p.succ) (κ' p.castSucc) ℝ :=
    fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
  let Earlyfun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
      Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
        (K := ℝ) (ρ := ρ) (κ := κ')
        (A1fun y) (A3fun y) (Cfun y) p0.val (Nat.le_of_lt p0.isLt)
  let Cprod :
      RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last ((M + 1) + 1))) (κ' r0.castSucc) ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
        (Cfun y) (Fin.last ((M + 1) + 1)) r0.castSucc r0.castSucc.le_last
  let Cnext :
      RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last ((M + 1) + 1))) (κ' r0.succ) ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
        (Cfun y) (Fin.last ((M + 1) + 1)) r0.succ r0.succ.le_last
  let A3p :
      RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
        Matrix (κ' r0.castSucc) ρ ℝ :=
    fun y ↦ by
      simpa [p0, r0] using A3fun y p0
  let dG : Matrix (κ' r0.castSucc) ρ ℝ := by
    simpa [p0, r0] using v.2.2.1 q0
  let Pcast : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct
        (K := ℝ) (κ := fun _ : Fin ((M + 1) + 2) ↦ ρ)
        (A1fun y) (Fin.last ((M + 1) + 1)) p0.castSucc p0.castSucc.le_last
  let Psucc : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct
        (K := ℝ) (κ := fun _ : Fin ((M + 1) + 2) ↦ ρ)
        (A1fun y) (Fin.last ((M + 1) + 1)) p0.succ p0.succ.le_last
  let dPsucc := (fderiv ℝ Psucc z) v
  let Tfun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
  let Tail := ChartLocalSuffixState.retainedPassiveA1TailAfterFirst
    (K := ℝ) (ρ := ρ) data.A1seed
  let dTail := (fderiv ℝ Tfun z) v
  let Nextfun : RetainedPassiveRawTopologyTuple (M := M + 1) ρ κ' ℝ →
      Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
        (K := ℝ) (ρ := ρ) (κ := κ')
        (A1fun y) (A3fun y) (Cfun y) (p0.val + 1)
        (Nat.succ_le_of_lt p0.isLt)
  let dEarly : Matrix (κ' (Fin.last ((M + 1) + 1))) ρ ℝ :=
    -(((fderiv ℝ Cnext z) v * data.C r0 + Cnext z * v.2.2.2.1 r0) *
        A3p z * (Pcast z)⁻¹)
      - (Cprod z * dG * (Pcast z)⁻¹)
      + Cprod z * A3p z * (Pcast z)⁻¹ *
          (dPsucc * coord.solvedA1 p0 +
            Psucc z *
              (Tail⁻¹ * v.2.2.2.2.1 -
                Tail⁻¹ * dTail * Tail⁻¹ * data.Ctop)) *
          (Pcast z)⁻¹
      + (fderiv ℝ Nextfun z) v
  let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
  have hF3 :=
    F3_tail_pos_dEarly_zero_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (M := M) (ρ := ρ) (κ' := κ') hz v
  have hrec :=
    retainedPassiveFormalRawOrderJacobianAt_recovers_F3
      (ρ := ρ) (κ' := κ') hz v
  change Dzv.2.2.2.2.2
      - dEarly * coord.solvedA1 (Fin.last (M + 1))
      + (coord.F3 - Earlyfun z) *
          (Dzv.1 qLast
            - XsuccF2 qLast.succ * coord.solvedA3 qLast.succ
            - coord.F2 qLast.succ.succ *
                rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv qLast.succ) =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.2 at hF3
  change (Dzv.2.2.2.2.2
      - dEarly * coord.solvedA1 (Fin.last (M + 1))
      + (coord.F3 - Earlyfun z) *
          (Dzv.1 qLast
            - XsuccF2 qLast.succ * coord.solvedA3 qLast.succ
            - coord.F2 qLast.succ.succ *
                rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv qLast.succ)) *
        (-(coord.solvedA1 (Fin.last (M + 1))))⁻¹ =
      v.2.2.2.2.2
  rw [hF3]
  simpa [coord, data] using hrec

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- For passive tail length at least two, recurse once into the `Nextfun`
summand of the first-index `dEarly` expansion in the positive-tail `F3`
bridge, using the successor-index retained-passive `dEarly` theorem at
`0 : Fin (M+1)`. -/
theorem F3_tail_pos_pos_dEarly_zero_next_succ_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (((M + 1) + 1) + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    let Dzv := (fderiv ℝ raw z) v
    let qLast : Fin ((M + 1) + 1) := Fin.last (M + 1)
    let q0 : Fin ((M + 1) + 1) := 0
    let p0 : Fin (((M + 1) + 1) + 1) := q0.castSucc
    let r0 : Fin (((M + 1) + 1) + 1) := q0.succ
    let s0 : Fin (M + 1) := 0
    let q1 : Fin ((M + 1) + 1) := s0.succ
    let u1 : Fin ((M + 1) + 1) := s0.castSucc
    let p1 : Fin (((M + 1) + 1) + 1) := q1.castSucc
    let r1 : Fin (((M + 1) + 1) + 1) := q1.succ
    let A1fun : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        Fin (((M + 1) + 1) + 1) → Matrix ρ ρ ℝ :=
      fun y p ↦
        ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p
    let A3fun :
        RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
          ∀ p : Fin (((M + 1) + 1) + 1), Matrix (κ' p.succ) ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed
    let Cfun :
        RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
          ∀ p : Fin (((M + 1) + 1) + 1), Matrix (κ' p.succ) (κ' p.castSucc) ℝ :=
      fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
    let Earlyfun : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last (((M + 1) + 1) + 1))) ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
          (K := ℝ) (ρ := ρ) (κ := κ')
          (A1fun y) (A3fun y) (Cfun y) p0.val (Nat.le_of_lt p0.isLt)
    let Cprod :
        RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
          Matrix (κ' (Fin.last (((M + 1) + 1) + 1))) (κ' r0.castSucc) ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
          (Cfun y) (Fin.last (((M + 1) + 1) + 1)) r0.castSucc r0.castSucc.le_last
    let Cnext :
        RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
          Matrix (κ' (Fin.last (((M + 1) + 1) + 1))) (κ' r0.succ) ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
          (Cfun y) (Fin.last (((M + 1) + 1) + 1)) r0.succ r0.succ.le_last
    let A3p :
        RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
          Matrix (κ' r0.castSucc) ρ ℝ :=
      fun y ↦ by
        simpa [p0, r0] using A3fun y p0
    let dG : Matrix (κ' r0.castSucc) ρ ℝ := by
      simpa [p0, r0] using v.2.2.1 q0
    let Pcast : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct
          (K := ℝ) (κ := fun _ : Fin (((M + 1) + 1) + 2) ↦ ρ)
          (A1fun y) (Fin.last (((M + 1) + 1) + 1)) p0.castSucc
          p0.castSucc.le_last
    let Psucc : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct
          (K := ℝ) (κ := fun _ : Fin (((M + 1) + 1) + 2) ↦ ρ)
          (A1fun y) (Fin.last (((M + 1) + 1) + 1)) p0.succ p0.succ.le_last
    let dPsucc := (fderiv ℝ Psucc z) v
    let Tfun : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
    let Tail := ChartLocalSuffixState.retainedPassiveA1TailAfterFirst
      (K := ℝ) (ρ := ρ) data.A1seed
    let dTail := (fderiv ℝ Tfun z) v
    let Cprod1 :
        RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
          Matrix (κ' (Fin.last (((M + 1) + 1) + 1))) (κ' r1.castSucc) ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
          (Cfun y) (Fin.last (((M + 1) + 1) + 1)) r1.castSucc r1.castSucc.le_last
    let Cnext1 :
        RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
          Matrix (κ' (Fin.last (((M + 1) + 1) + 1))) (κ' r1.succ) ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
          (Cfun y) (Fin.last (((M + 1) + 1) + 1)) r1.succ r1.succ.le_last
    let A3p1 :
        RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
          Matrix (κ' r1.castSucc) ρ ℝ :=
      fun y ↦ by
        simpa [p1, r1] using A3fun y p1
    let dG1 : Matrix (κ' r1.castSucc) ρ ℝ := by
      simpa [p1, r1] using v.2.2.1 q1
    let Pcast1 : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct
          (K := ℝ) (κ := fun _ : Fin (((M + 1) + 1) + 2) ↦ ρ)
          (A1fun y) (Fin.last (((M + 1) + 1) + 1)) p1.castSucc
          p1.castSucc.le_last
    let Psucc1 : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct
          (K := ℝ) (κ := fun _ : Fin (((M + 1) + 1) + 2) ↦ ρ)
          (A1fun y) (Fin.last (((M + 1) + 1) + 1)) p1.succ p1.succ.le_last
    let dPsucc1 := (fderiv ℝ Psucc1 z) v
    let NextNextfun : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last (((M + 1) + 1) + 1))) ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
          (K := ℝ) (ρ := ρ) (κ := κ')
          (A1fun y) (A3fun y) (Cfun y) (p1.val + 1)
          (Nat.succ_le_of_lt p1.isLt)
    let dNext : Matrix (κ' (Fin.last (((M + 1) + 1) + 1))) ρ ℝ :=
      -(((fderiv ℝ Cnext1 z) v * data.C r1 + Cnext1 z * v.2.2.2.1 r1) *
          A3p1 z * (Pcast1 z)⁻¹)
        - (Cprod1 z * dG1 * (Pcast1 z)⁻¹)
        + Cprod1 z * A3p1 z * (Pcast1 z)⁻¹ *
            (dPsucc1 * coord.solvedA1 p1 + Psucc1 z * v.1 u1) *
            (Pcast1 z)⁻¹
        + (fderiv ℝ NextNextfun z) v
    let dEarly : Matrix (κ' (Fin.last (((M + 1) + 1) + 1))) ρ ℝ :=
      -(((fderiv ℝ Cnext z) v * data.C r0 + Cnext z * v.2.2.2.1 r0) *
          A3p z * (Pcast z)⁻¹)
        - (Cprod z * dG * (Pcast z)⁻¹)
        + Cprod z * A3p z * (Pcast z)⁻¹ *
            (dPsucc * coord.solvedA1 p0 +
              Psucc z *
                (Tail⁻¹ * v.2.2.2.2.1 -
                  Tail⁻¹ * dTail * Tail⁻¹ * data.Ctop)) *
            (Pcast z)⁻¹
        + dNext
    let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
    Dzv.2.2.2.2.2
      - dEarly * coord.solvedA1 (Fin.last ((M + 1) + 1))
      + (coord.F3 - Earlyfun z) *
          (Dzv.1 qLast
            - XsuccF2 qLast.succ * coord.solvedA3 qLast.succ
            - coord.F2 qLast.succ.succ *
                rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv qLast.succ) =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.2 := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  let qLast : Fin ((M + 1) + 1) := Fin.last (M + 1)
  let q0 : Fin ((M + 1) + 1) := 0
  let p0 : Fin (((M + 1) + 1) + 1) := q0.castSucc
  let r0 : Fin (((M + 1) + 1) + 1) := q0.succ
  let s0 : Fin (M + 1) := 0
  let q1 : Fin ((M + 1) + 1) := s0.succ
  let u1 : Fin ((M + 1) + 1) := s0.castSucc
  let p1 : Fin (((M + 1) + 1) + 1) := q1.castSucc
  let r1 : Fin (((M + 1) + 1) + 1) := q1.succ
  let A1fun : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
      Fin (((M + 1) + 1) + 1) → Matrix ρ ρ ℝ :=
    fun y p ↦
      ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p
  let A3fun :
      RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        ∀ p : Fin (((M + 1) + 1) + 1), Matrix (κ' p.succ) ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed
  let Cfun :
      RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        ∀ p : Fin (((M + 1) + 1) + 1), Matrix (κ' p.succ) (κ' p.castSucc) ℝ :=
    fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
  let Earlyfun : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
      Matrix (κ' (Fin.last (((M + 1) + 1) + 1))) ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
        (K := ℝ) (ρ := ρ) (κ := κ')
        (A1fun y) (A3fun y) (Cfun y) p0.val (Nat.le_of_lt p0.isLt)
  let Cprod :
      RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last (((M + 1) + 1) + 1))) (κ' r0.castSucc) ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
        (Cfun y) (Fin.last (((M + 1) + 1) + 1)) r0.castSucc r0.castSucc.le_last
  let Cnext :
      RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last (((M + 1) + 1) + 1))) (κ' r0.succ) ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
        (Cfun y) (Fin.last (((M + 1) + 1) + 1)) r0.succ r0.succ.le_last
  let A3p :
      RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        Matrix (κ' r0.castSucc) ρ ℝ :=
    fun y ↦ by
      simpa [p0, r0] using A3fun y p0
  let dG : Matrix (κ' r0.castSucc) ρ ℝ := by
    simpa [p0, r0] using v.2.2.1 q0
  let Pcast : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct
        (K := ℝ) (κ := fun _ : Fin (((M + 1) + 1) + 2) ↦ ρ)
        (A1fun y) (Fin.last (((M + 1) + 1) + 1)) p0.castSucc p0.castSucc.le_last
  let Psucc : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct
        (K := ℝ) (κ := fun _ : Fin (((M + 1) + 1) + 2) ↦ ρ)
        (A1fun y) (Fin.last (((M + 1) + 1) + 1)) p0.succ p0.succ.le_last
  let dPsucc := (fderiv ℝ Psucc z) v
  let Tfun : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
  let Tail := ChartLocalSuffixState.retainedPassiveA1TailAfterFirst
    (K := ℝ) (ρ := ρ) data.A1seed
  let dTail := (fderiv ℝ Tfun z) v
  let Nextfun : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
      Matrix (κ' (Fin.last (((M + 1) + 1) + 1))) ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
        (K := ℝ) (ρ := ρ) (κ := κ')
        (A1fun y) (A3fun y) (Cfun y) (p0.val + 1) (Nat.succ_le_of_lt p0.isLt)
  let Cprod1 :
      RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last (((M + 1) + 1) + 1))) (κ' r1.castSucc) ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
        (Cfun y) (Fin.last (((M + 1) + 1) + 1)) r1.castSucc r1.castSucc.le_last
  let Cnext1 :
      RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last (((M + 1) + 1) + 1))) (κ' r1.succ) ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
        (Cfun y) (Fin.last (((M + 1) + 1) + 1)) r1.succ r1.succ.le_last
  let A3p1 :
      RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        Matrix (κ' r1.castSucc) ρ ℝ :=
    fun y ↦ by
      simpa [p1, r1] using A3fun y p1
  let dG1 : Matrix (κ' r1.castSucc) ρ ℝ := by
    simpa [p1, r1] using v.2.2.1 q1
  let Pcast1 : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct
        (K := ℝ) (κ := fun _ : Fin (((M + 1) + 1) + 2) ↦ ρ)
        (A1fun y) (Fin.last (((M + 1) + 1) + 1)) p1.castSucc p1.castSucc.le_last
  let Psucc1 : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct
        (K := ℝ) (κ := fun _ : Fin (((M + 1) + 1) + 2) ↦ ρ)
        (A1fun y) (Fin.last (((M + 1) + 1) + 1)) p1.succ p1.succ.le_last
  let dPsucc1 := (fderiv ℝ Psucc1 z) v
  let NextNextfun : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
      Matrix (κ' (Fin.last (((M + 1) + 1) + 1))) ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
        (K := ℝ) (ρ := ρ) (κ := κ')
        (A1fun y) (A3fun y) (Cfun y) (p1.val + 1) (Nat.succ_le_of_lt p1.isLt)
  let dNext : Matrix (κ' (Fin.last (((M + 1) + 1) + 1))) ρ ℝ :=
    -(((fderiv ℝ Cnext1 z) v * data.C r1 + Cnext1 z * v.2.2.2.1 r1) *
        A3p1 z * (Pcast1 z)⁻¹)
      - (Cprod1 z * dG1 * (Pcast1 z)⁻¹)
      + Cprod1 z * A3p1 z * (Pcast1 z)⁻¹ *
          (dPsucc1 * coord.solvedA1 p1 + Psucc1 z * v.1 u1) *
          (Pcast1 z)⁻¹
      + (fderiv ℝ NextNextfun z) v
  let dEarly : Matrix (κ' (Fin.last (((M + 1) + 1) + 1))) ρ ℝ :=
    -(((fderiv ℝ Cnext z) v * data.C r0 + Cnext z * v.2.2.2.1 r0) *
        A3p z * (Pcast z)⁻¹)
      - (Cprod z * dG * (Pcast z)⁻¹)
      + Cprod z * A3p z * (Pcast z)⁻¹ *
          (dPsucc * coord.solvedA1 p0 +
            Psucc z *
              (Tail⁻¹ * v.2.2.2.2.1 -
                Tail⁻¹ * dTail * Tail⁻¹ * data.Ctop)) *
          (Pcast z)⁻¹
      + dNext
  let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
  have hF3base :=
    F3_tail_pos_dEarly_zero_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (M := M + 1) (ρ := ρ) (κ' := κ') hz v
  have hF3 :
      Dzv.2.2.2.2.2
        - (-(((fderiv ℝ Cnext z) v * data.C r0 + Cnext z * v.2.2.2.1 r0) *
              A3p z * (Pcast z)⁻¹)
            - (Cprod z * dG * (Pcast z)⁻¹)
            + Cprod z * A3p z * (Pcast z)⁻¹ *
                (dPsucc * coord.solvedA1 p0 +
                  Psucc z *
                    (Tail⁻¹ * v.2.2.2.2.1 -
                      Tail⁻¹ * dTail * Tail⁻¹ * data.Ctop)) *
                (Pcast z)⁻¹
            + (fderiv ℝ Nextfun z) v) * coord.solvedA1 (Fin.last ((M + 1) + 1))
        + (coord.F3 - Earlyfun z) *
            (Dzv.1 qLast
              - XsuccF2 qLast.succ * coord.solvedA3 qLast.succ
              - coord.F2 qLast.succ.succ *
                  rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv qLast.succ) =
        ((retainedPassiveFormalRawOrderJacobianAt
            (ρ := ρ) (κ' := κ') z) v).2.2.2.2.2 := by
    simpa [A1fun, A3fun, Cfun, Earlyfun, Cprod, Cnext, A3p, dG, Pcast,
      Psucc, dPsucc, Tfun, Tail, dTail, Nextfun, data, coord, Dzv, XsuccF2,
      qLast, q0, p0, r0] using hF3base
  have hNextBase :=
    fderiv_retainedPassiveLowerLeftProductTailSum_succ_product_dCprod_dG_dPcast_apply
      (M := M + 1) (ρ := ρ) (κ' := κ') hz v s0
  have hNext : (fderiv ℝ Nextfun z) v = dNext := by
    simpa [A1fun, A3fun, Cfun, Nextfun, Cprod1, Cnext1, A3p1, dG1,
      Pcast1, Psucc1, dPsucc1, NextNextfun, dNext, data, coord, s0, q1, u1,
      p1, r1, q0, p0] using hNextBase
  rw [hNext] at hF3
  simpa [A1fun, A3fun, Cfun, Earlyfun, Cprod, Cnext, A3p, dG, Pcast,
    Psucc, dPsucc, Tfun, Tail, dTail, Nextfun, Cprod1, Cnext1, A3p1, dG1,
    Pcast1, Psucc1, dPsucc1, NextNextfun, dNext, dEarly, data, coord, Dzv,
    XsuccF2, qLast, q0, p0, r0, s0, q1, u1, p1, r1] using hF3

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- The two-positive-tail `F3` bridge with the first recursive `Nextfun`
successor recurrence substituted recovers the source `F3` tangent by
right-multiplication with the inverse of the negative terminal solved top-left
factor. -/
theorem F3_tail_pos_pos_dEarly_zero_next_succ_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3
    {M : ℕ} {ρ : Type*} {κ' : Fin (((M + 1) + 1) + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    let Dzv := (fderiv ℝ raw z) v
    let qLast : Fin ((M + 1) + 1) := Fin.last (M + 1)
    let q0 : Fin ((M + 1) + 1) := 0
    let p0 : Fin (((M + 1) + 1) + 1) := q0.castSucc
    let r0 : Fin (((M + 1) + 1) + 1) := q0.succ
    let s0 : Fin (M + 1) := 0
    let q1 : Fin ((M + 1) + 1) := s0.succ
    let u1 : Fin ((M + 1) + 1) := s0.castSucc
    let p1 : Fin (((M + 1) + 1) + 1) := q1.castSucc
    let r1 : Fin (((M + 1) + 1) + 1) := q1.succ
    let A1fun : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        Fin (((M + 1) + 1) + 1) → Matrix ρ ρ ℝ :=
      fun y p ↦
        ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p
    let A3fun :
        RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
          ∀ p : Fin (((M + 1) + 1) + 1), Matrix (κ' p.succ) ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed
    let Cfun :
        RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
          ∀ p : Fin (((M + 1) + 1) + 1), Matrix (κ' p.succ) (κ' p.castSucc) ℝ :=
      fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
    let Earlyfun : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last (((M + 1) + 1) + 1))) ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
          (K := ℝ) (ρ := ρ) (κ := κ')
          (A1fun y) (A3fun y) (Cfun y) p0.val (Nat.le_of_lt p0.isLt)
    let Cprod :
        RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
          Matrix (κ' (Fin.last (((M + 1) + 1) + 1))) (κ' r0.castSucc) ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
          (Cfun y) (Fin.last (((M + 1) + 1) + 1)) r0.castSucc r0.castSucc.le_last
    let Cnext :
        RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
          Matrix (κ' (Fin.last (((M + 1) + 1) + 1))) (κ' r0.succ) ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
          (Cfun y) (Fin.last (((M + 1) + 1) + 1)) r0.succ r0.succ.le_last
    let A3p :
        RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
          Matrix (κ' r0.castSucc) ρ ℝ :=
      fun y ↦ by
        simpa [p0, r0] using A3fun y p0
    let dG : Matrix (κ' r0.castSucc) ρ ℝ := by
      simpa [p0, r0] using v.2.2.1 q0
    let Pcast : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct
          (K := ℝ) (κ := fun _ : Fin (((M + 1) + 1) + 2) ↦ ρ)
          (A1fun y) (Fin.last (((M + 1) + 1) + 1)) p0.castSucc
          p0.castSucc.le_last
    let Psucc : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct
          (K := ℝ) (κ := fun _ : Fin (((M + 1) + 1) + 2) ↦ ρ)
          (A1fun y) (Fin.last (((M + 1) + 1) + 1)) p0.succ p0.succ.le_last
    let dPsucc := (fderiv ℝ Psucc z) v
    let Tfun : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
    let Tail := ChartLocalSuffixState.retainedPassiveA1TailAfterFirst
      (K := ℝ) (ρ := ρ) data.A1seed
    let dTail := (fderiv ℝ Tfun z) v
    let Cprod1 :
        RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
          Matrix (κ' (Fin.last (((M + 1) + 1) + 1))) (κ' r1.castSucc) ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
          (Cfun y) (Fin.last (((M + 1) + 1) + 1)) r1.castSucc r1.castSucc.le_last
    let Cnext1 :
        RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
          Matrix (κ' (Fin.last (((M + 1) + 1) + 1))) (κ' r1.succ) ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
          (Cfun y) (Fin.last (((M + 1) + 1) + 1)) r1.succ r1.succ.le_last
    let A3p1 :
        RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
          Matrix (κ' r1.castSucc) ρ ℝ :=
      fun y ↦ by
        simpa [p1, r1] using A3fun y p1
    let dG1 : Matrix (κ' r1.castSucc) ρ ℝ := by
      simpa [p1, r1] using v.2.2.1 q1
    let Pcast1 : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct
          (K := ℝ) (κ := fun _ : Fin (((M + 1) + 1) + 2) ↦ ρ)
          (A1fun y) (Fin.last (((M + 1) + 1) + 1)) p1.castSucc
          p1.castSucc.le_last
    let Psucc1 : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct
          (K := ℝ) (κ := fun _ : Fin (((M + 1) + 1) + 2) ↦ ρ)
          (A1fun y) (Fin.last (((M + 1) + 1) + 1)) p1.succ p1.succ.le_last
    let dPsucc1 := (fderiv ℝ Psucc1 z) v
    let NextNextfun : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last (((M + 1) + 1) + 1))) ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
          (K := ℝ) (ρ := ρ) (κ := κ')
          (A1fun y) (A3fun y) (Cfun y) (p1.val + 1)
          (Nat.succ_le_of_lt p1.isLt)
    let dNext : Matrix (κ' (Fin.last (((M + 1) + 1) + 1))) ρ ℝ :=
      -(((fderiv ℝ Cnext1 z) v * data.C r1 + Cnext1 z * v.2.2.2.1 r1) *
          A3p1 z * (Pcast1 z)⁻¹)
        - (Cprod1 z * dG1 * (Pcast1 z)⁻¹)
        + Cprod1 z * A3p1 z * (Pcast1 z)⁻¹ *
            (dPsucc1 * coord.solvedA1 p1 + Psucc1 z * v.1 u1) *
            (Pcast1 z)⁻¹
        + (fderiv ℝ NextNextfun z) v
    let dEarly : Matrix (κ' (Fin.last (((M + 1) + 1) + 1))) ρ ℝ :=
      -(((fderiv ℝ Cnext z) v * data.C r0 + Cnext z * v.2.2.2.1 r0) *
          A3p z * (Pcast z)⁻¹)
        - (Cprod z * dG * (Pcast z)⁻¹)
        + Cprod z * A3p z * (Pcast z)⁻¹ *
            (dPsucc * coord.solvedA1 p0 +
              Psucc z *
                (Tail⁻¹ * v.2.2.2.2.1 -
                  Tail⁻¹ * dTail * Tail⁻¹ * data.Ctop)) *
            (Pcast z)⁻¹
        + dNext
    let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
    (Dzv.2.2.2.2.2
      - dEarly * coord.solvedA1 (Fin.last ((M + 1) + 1))
      + (coord.F3 - Earlyfun z) *
          (Dzv.1 qLast
            - XsuccF2 qLast.succ * coord.solvedA3 qLast.succ
            - coord.F2 qLast.succ.succ *
                rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv qLast.succ)) *
        (-(coord.solvedA1 (Fin.last ((M + 1) + 1))))⁻¹ =
      v.2.2.2.2.2 := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  let qLast : Fin ((M + 1) + 1) := Fin.last (M + 1)
  let q0 : Fin ((M + 1) + 1) := 0
  let p0 : Fin (((M + 1) + 1) + 1) := q0.castSucc
  let r0 : Fin (((M + 1) + 1) + 1) := q0.succ
  let s0 : Fin (M + 1) := 0
  let q1 : Fin ((M + 1) + 1) := s0.succ
  let u1 : Fin ((M + 1) + 1) := s0.castSucc
  let p1 : Fin (((M + 1) + 1) + 1) := q1.castSucc
  let r1 : Fin (((M + 1) + 1) + 1) := q1.succ
  let A1fun : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
      Fin (((M + 1) + 1) + 1) → Matrix ρ ρ ℝ :=
    fun y p ↦
      ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p
  let A3fun :
      RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        ∀ p : Fin (((M + 1) + 1) + 1), Matrix (κ' p.succ) ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed
  let Cfun :
      RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        ∀ p : Fin (((M + 1) + 1) + 1), Matrix (κ' p.succ) (κ' p.castSucc) ℝ :=
    fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
  let Earlyfun : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
      Matrix (κ' (Fin.last (((M + 1) + 1) + 1))) ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
        (K := ℝ) (ρ := ρ) (κ := κ')
        (A1fun y) (A3fun y) (Cfun y) p0.val (Nat.le_of_lt p0.isLt)
  let Cprod :
      RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last (((M + 1) + 1) + 1))) (κ' r0.castSucc) ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
        (Cfun y) (Fin.last (((M + 1) + 1) + 1)) r0.castSucc r0.castSucc.le_last
  let Cnext :
      RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last (((M + 1) + 1) + 1))) (κ' r0.succ) ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
        (Cfun y) (Fin.last (((M + 1) + 1) + 1)) r0.succ r0.succ.le_last
  let A3p :
      RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        Matrix (κ' r0.castSucc) ρ ℝ :=
    fun y ↦ by
      simpa [p0, r0] using A3fun y p0
  let dG : Matrix (κ' r0.castSucc) ρ ℝ := by
    simpa [p0, r0] using v.2.2.1 q0
  let Pcast : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct
        (K := ℝ) (κ := fun _ : Fin (((M + 1) + 1) + 2) ↦ ρ)
        (A1fun y) (Fin.last (((M + 1) + 1) + 1)) p0.castSucc
        p0.castSucc.le_last
  let Psucc : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct
        (K := ℝ) (κ := fun _ : Fin (((M + 1) + 1) + 2) ↦ ρ)
        (A1fun y) (Fin.last (((M + 1) + 1) + 1)) p0.succ p0.succ.le_last
  let dPsucc := (fderiv ℝ Psucc z) v
  let Tfun : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
  let Tail := ChartLocalSuffixState.retainedPassiveA1TailAfterFirst
    (K := ℝ) (ρ := ρ) data.A1seed
  let dTail := (fderiv ℝ Tfun z) v
  let Cprod1 :
      RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last (((M + 1) + 1) + 1))) (κ' r1.castSucc) ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
        (Cfun y) (Fin.last (((M + 1) + 1) + 1)) r1.castSucc r1.castSucc.le_last
  let Cnext1 :
      RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last (((M + 1) + 1) + 1))) (κ' r1.succ) ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
        (Cfun y) (Fin.last (((M + 1) + 1) + 1)) r1.succ r1.succ.le_last
  let A3p1 :
      RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
        Matrix (κ' r1.castSucc) ρ ℝ :=
    fun y ↦ by
      simpa [p1, r1] using A3fun y p1
  let dG1 : Matrix (κ' r1.castSucc) ρ ℝ := by
    simpa [p1, r1] using v.2.2.1 q1
  let Pcast1 : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct
        (K := ℝ) (κ := fun _ : Fin (((M + 1) + 1) + 2) ↦ ρ)
        (A1fun y) (Fin.last (((M + 1) + 1) + 1)) p1.castSucc
        p1.castSucc.le_last
  let Psucc1 : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct
        (K := ℝ) (κ := fun _ : Fin (((M + 1) + 1) + 2) ↦ ρ)
        (A1fun y) (Fin.last (((M + 1) + 1) + 1)) p1.succ p1.succ.le_last
  let dPsucc1 := (fderiv ℝ Psucc1 z) v
  let NextNextfun : RetainedPassiveRawTopologyTuple (M := (M + 1) + 1) ρ κ' ℝ →
      Matrix (κ' (Fin.last (((M + 1) + 1) + 1))) ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
        (K := ℝ) (ρ := ρ) (κ := κ')
        (A1fun y) (A3fun y) (Cfun y) (p1.val + 1)
        (Nat.succ_le_of_lt p1.isLt)
  let dNext : Matrix (κ' (Fin.last (((M + 1) + 1) + 1))) ρ ℝ :=
    -(((fderiv ℝ Cnext1 z) v * data.C r1 + Cnext1 z * v.2.2.2.1 r1) *
        A3p1 z * (Pcast1 z)⁻¹)
      - (Cprod1 z * dG1 * (Pcast1 z)⁻¹)
      + Cprod1 z * A3p1 z * (Pcast1 z)⁻¹ *
          (dPsucc1 * coord.solvedA1 p1 + Psucc1 z * v.1 u1) *
          (Pcast1 z)⁻¹
      + (fderiv ℝ NextNextfun z) v
  let dEarly : Matrix (κ' (Fin.last (((M + 1) + 1) + 1))) ρ ℝ :=
    -(((fderiv ℝ Cnext z) v * data.C r0 + Cnext z * v.2.2.2.1 r0) *
        A3p z * (Pcast z)⁻¹)
      - (Cprod z * dG * (Pcast z)⁻¹)
      + Cprod z * A3p z * (Pcast z)⁻¹ *
          (dPsucc * coord.solvedA1 p0 +
            Psucc z *
              (Tail⁻¹ * v.2.2.2.2.1 -
                Tail⁻¹ * dTail * Tail⁻¹ * data.Ctop)) *
          (Pcast z)⁻¹
      + dNext
  let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
  have hF3 :=
    F3_tail_pos_pos_dEarly_zero_next_succ_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (M := M) (ρ := ρ) (κ' := κ') hz v
  have hrec :=
    retainedPassiveFormalRawOrderJacobianAt_recovers_F3
      (ρ := ρ) (κ' := κ') hz v
  change Dzv.2.2.2.2.2
      - dEarly * coord.solvedA1 (Fin.last ((M + 1) + 1))
      + (coord.F3 - Earlyfun z) *
          (Dzv.1 qLast
            - XsuccF2 qLast.succ * coord.solvedA3 qLast.succ
            - coord.F2 qLast.succ.succ *
                rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv qLast.succ) =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.2 at hF3
  change (Dzv.2.2.2.2.2
      - dEarly * coord.solvedA1 (Fin.last ((M + 1) + 1))
      + (coord.F3 - Earlyfun z) *
          (Dzv.1 qLast
            - XsuccF2 qLast.succ * coord.solvedA3 qLast.succ
            - coord.F2 qLast.succ.succ *
                rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv qLast.succ)) *
        (-(coord.solvedA1 (Fin.last ((M + 1) + 1))))⁻¹ =
      v.2.2.2.2.2
  rw [hF3]
  simpa [coord, data] using hrec

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- For passive tail length at least three, recurse once more into the
`NextNextfun` summand of the two-positive-tail `F3` bridge, using the
successor-index retained-passive `dEarly` theorem at the second successor
position. -/
theorem F3_tail_pos_pos_pos_dEarly_zero_next_succ_next_succ_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
    {M : ℕ} {ρ : Type*} {κ' : Fin ((((M + 1) + 1) + 1) + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    let Dzv := (fderiv ℝ raw z) v
    let qLast : Fin (((M + 1) + 1) + 1) := Fin.last ((M + 1) + 1)
    let q0 : Fin (((M + 1) + 1) + 1) := 0
    let p0 : Fin ((((M + 1) + 1) + 1) + 1) := q0.castSucc
    let r0 : Fin ((((M + 1) + 1) + 1) + 1) := q0.succ
    let s0 : Fin ((M + 1) + 1) := 0
    let q1 : Fin (((M + 1) + 1) + 1) := s0.succ
    let u1 : Fin (((M + 1) + 1) + 1) := s0.castSucc
    let p1 : Fin ((((M + 1) + 1) + 1) + 1) := q1.castSucc
    let r1 : Fin ((((M + 1) + 1) + 1) + 1) := q1.succ
    let t0 : Fin (M + 1) := 0
    let s1 : Fin ((M + 1) + 1) := t0.succ
    let q2 : Fin (((M + 1) + 1) + 1) := s1.succ
    let u2 : Fin (((M + 1) + 1) + 1) := s1.castSucc
    let p2 : Fin ((((M + 1) + 1) + 1) + 1) := q2.castSucc
    let r2 : Fin ((((M + 1) + 1) + 1) + 1) := q2.succ
    let A1fun : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Fin ((((M + 1) + 1) + 1) + 1) → Matrix ρ ρ ℝ :=
      fun y p ↦
        ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p
    let A3fun :
        RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
          ∀ p : Fin ((((M + 1) + 1) + 1) + 1), Matrix (κ' p.succ) ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed
    let Cfun :
        RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
          ∀ p : Fin ((((M + 1) + 1) + 1) + 1), Matrix (κ' p.succ) (κ' p.castSucc) ℝ :=
      fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
    let Earlyfun : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
          (K := ℝ) (ρ := ρ) (κ := κ')
          (A1fun y) (A3fun y) (Cfun y) p0.val (Nat.le_of_lt p0.isLt)
    let Cprod :
        RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
          Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) (κ' r0.castSucc) ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
          (Cfun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) r0.castSucc r0.castSucc.le_last
    let Cnext :
        RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
          Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) (κ' r0.succ) ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
          (Cfun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) r0.succ r0.succ.le_last
    let A3p :
        RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
          Matrix (κ' r0.castSucc) ρ ℝ :=
      fun y ↦ by
        simpa [p0, r0] using A3fun y p0
    let dG : Matrix (κ' r0.castSucc) ρ ℝ := by
      simpa [p0, r0] using v.2.2.1 q0
    let Pcast : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct
          (K := ℝ) (κ := fun _ : Fin ((((M + 1) + 1) + 1) + 2) ↦ ρ)
          (A1fun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) p0.castSucc
          p0.castSucc.le_last
    let Psucc : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct
          (K := ℝ) (κ := fun _ : Fin ((((M + 1) + 1) + 1) + 2) ↦ ρ)
          (A1fun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) p0.succ p0.succ.le_last
    let dPsucc := (fderiv ℝ Psucc z) v
    let Tfun : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
    let Tail := ChartLocalSuffixState.retainedPassiveA1TailAfterFirst
      (K := ℝ) (ρ := ρ) data.A1seed
    let dTail := (fderiv ℝ Tfun z) v
    let Cprod1 :
        RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
          Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) (κ' r1.castSucc) ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
          (Cfun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) r1.castSucc r1.castSucc.le_last
    let Cnext1 :
        RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
          Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) (κ' r1.succ) ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
          (Cfun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) r1.succ r1.succ.le_last
    let A3p1 :
        RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
          Matrix (κ' r1.castSucc) ρ ℝ :=
      fun y ↦ by
        simpa [p1, r1] using A3fun y p1
    let dG1 : Matrix (κ' r1.castSucc) ρ ℝ := by
      simpa [p1, r1] using v.2.2.1 q1
    let Pcast1 : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct
          (K := ℝ) (κ := fun _ : Fin ((((M + 1) + 1) + 1) + 2) ↦ ρ)
          (A1fun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) p1.castSucc
          p1.castSucc.le_last
    let Psucc1 : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct
          (K := ℝ) (κ := fun _ : Fin ((((M + 1) + 1) + 1) + 2) ↦ ρ)
          (A1fun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) p1.succ p1.succ.le_last
    let dPsucc1 := (fderiv ℝ Psucc1 z) v
    let Cprod2 :
        RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
          Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) (κ' r2.castSucc) ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
          (Cfun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) r2.castSucc r2.castSucc.le_last
    let Cnext2 :
        RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
          Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) (κ' r2.succ) ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
          (Cfun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) r2.succ r2.succ.le_last
    let A3p2 :
        RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
          Matrix (κ' r2.castSucc) ρ ℝ :=
      fun y ↦ by
        simpa [p2, r2] using A3fun y p2
    let dG2 : Matrix (κ' r2.castSucc) ρ ℝ := by
      simpa [p2, r2] using v.2.2.1 q2
    let Pcast2 : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct
          (K := ℝ) (κ := fun _ : Fin ((((M + 1) + 1) + 1) + 2) ↦ ρ)
          (A1fun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) p2.castSucc
          p2.castSucc.le_last
    let Psucc2 : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct
          (K := ℝ) (κ := fun _ : Fin ((((M + 1) + 1) + 1) + 2) ↦ ρ)
          (A1fun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) p2.succ p2.succ.le_last
    let dPsucc2 := (fderiv ℝ Psucc2 z) v
    let NextNextNextfun : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
          (K := ℝ) (ρ := ρ) (κ := κ')
          (A1fun y) (A3fun y) (Cfun y) (p2.val + 1)
          (Nat.succ_le_of_lt p2.isLt)
    let dNext2 : Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) ρ ℝ :=
      -(((fderiv ℝ Cnext2 z) v * data.C r2 + Cnext2 z * v.2.2.2.1 r2) *
          A3p2 z * (Pcast2 z)⁻¹)
        - (Cprod2 z * dG2 * (Pcast2 z)⁻¹)
        + Cprod2 z * A3p2 z * (Pcast2 z)⁻¹ *
            (dPsucc2 * coord.solvedA1 p2 + Psucc2 z * v.1 u2) *
            (Pcast2 z)⁻¹
        + (fderiv ℝ NextNextNextfun z) v
    let dNext1 : Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) ρ ℝ :=
      -(((fderiv ℝ Cnext1 z) v * data.C r1 + Cnext1 z * v.2.2.2.1 r1) *
          A3p1 z * (Pcast1 z)⁻¹)
        - (Cprod1 z * dG1 * (Pcast1 z)⁻¹)
        + Cprod1 z * A3p1 z * (Pcast1 z)⁻¹ *
            (dPsucc1 * coord.solvedA1 p1 + Psucc1 z * v.1 u1) *
            (Pcast1 z)⁻¹
        + dNext2
    let dEarly : Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) ρ ℝ :=
      -(((fderiv ℝ Cnext z) v * data.C r0 + Cnext z * v.2.2.2.1 r0) *
          A3p z * (Pcast z)⁻¹)
        - (Cprod z * dG * (Pcast z)⁻¹)
        + Cprod z * A3p z * (Pcast z)⁻¹ *
            (dPsucc * coord.solvedA1 p0 +
              Psucc z *
                (Tail⁻¹ * v.2.2.2.2.1 -
                  Tail⁻¹ * dTail * Tail⁻¹ * data.Ctop)) *
            (Pcast z)⁻¹
        + dNext1
    let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
    Dzv.2.2.2.2.2
      - dEarly * coord.solvedA1 (Fin.last (((M + 1) + 1) + 1))
      + (coord.F3 - Earlyfun z) *
          (Dzv.1 qLast
            - XsuccF2 qLast.succ * coord.solvedA3 qLast.succ
            - coord.F2 qLast.succ.succ *
                rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv qLast.succ) =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.2 := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  let qLast : Fin (((M + 1) + 1) + 1) := Fin.last ((M + 1) + 1)
  let q0 : Fin (((M + 1) + 1) + 1) := 0
  let p0 : Fin ((((M + 1) + 1) + 1) + 1) := q0.castSucc
  let r0 : Fin ((((M + 1) + 1) + 1) + 1) := q0.succ
  let s0 : Fin ((M + 1) + 1) := 0
  let q1 : Fin (((M + 1) + 1) + 1) := s0.succ
  let u1 : Fin (((M + 1) + 1) + 1) := s0.castSucc
  let p1 : Fin ((((M + 1) + 1) + 1) + 1) := q1.castSucc
  let r1 : Fin ((((M + 1) + 1) + 1) + 1) := q1.succ
  let t0 : Fin (M + 1) := 0
  let s1 : Fin ((M + 1) + 1) := t0.succ
  let q2 : Fin (((M + 1) + 1) + 1) := s1.succ
  let u2 : Fin (((M + 1) + 1) + 1) := s1.castSucc
  let p2 : Fin ((((M + 1) + 1) + 1) + 1) := q2.castSucc
  let r2 : Fin ((((M + 1) + 1) + 1) + 1) := q2.succ
  let A1fun : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
      Fin ((((M + 1) + 1) + 1) + 1) → Matrix ρ ρ ℝ :=
    fun y p ↦
      ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p
  let A3fun :
      RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        ∀ p : Fin ((((M + 1) + 1) + 1) + 1), Matrix (κ' p.succ) ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed
  let Cfun :
      RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        ∀ p : Fin ((((M + 1) + 1) + 1) + 1), Matrix (κ' p.succ) (κ' p.castSucc) ℝ :=
    fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
  let Earlyfun : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
      Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
        (K := ℝ) (ρ := ρ) (κ := κ')
        (A1fun y) (A3fun y) (Cfun y) p0.val (Nat.le_of_lt p0.isLt)
  let Cprod :
      RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) (κ' r0.castSucc) ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
        (Cfun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) r0.castSucc r0.castSucc.le_last
  let Cnext :
      RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) (κ' r0.succ) ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
        (Cfun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) r0.succ r0.succ.le_last
  let A3p :
      RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix (κ' r0.castSucc) ρ ℝ :=
    fun y ↦ by
      simpa [p0, r0] using A3fun y p0
  let dG : Matrix (κ' r0.castSucc) ρ ℝ := by
    simpa [p0, r0] using v.2.2.1 q0
  let Pcast : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct
        (K := ℝ) (κ := fun _ : Fin ((((M + 1) + 1) + 1) + 2) ↦ ρ)
        (A1fun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) p0.castSucc
        p0.castSucc.le_last
  let Psucc : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct
        (K := ℝ) (κ := fun _ : Fin ((((M + 1) + 1) + 1) + 2) ↦ ρ)
        (A1fun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) p0.succ p0.succ.le_last
  let dPsucc := (fderiv ℝ Psucc z) v
  let Tfun : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
  let Tail := ChartLocalSuffixState.retainedPassiveA1TailAfterFirst
    (K := ℝ) (ρ := ρ) data.A1seed
  let dTail := (fderiv ℝ Tfun z) v
  let Cprod1 :
      RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) (κ' r1.castSucc) ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
        (Cfun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) r1.castSucc r1.castSucc.le_last
  let Cnext1 :
      RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) (κ' r1.succ) ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
        (Cfun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) r1.succ r1.succ.le_last
  let A3p1 :
      RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix (κ' r1.castSucc) ρ ℝ :=
    fun y ↦ by
      simpa [p1, r1] using A3fun y p1
  let dG1 : Matrix (κ' r1.castSucc) ρ ℝ := by
    simpa [p1, r1] using v.2.2.1 q1
  let Pcast1 : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct
        (K := ℝ) (κ := fun _ : Fin ((((M + 1) + 1) + 1) + 2) ↦ ρ)
        (A1fun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) p1.castSucc
        p1.castSucc.le_last
  let Psucc1 : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct
        (K := ℝ) (κ := fun _ : Fin ((((M + 1) + 1) + 1) + 2) ↦ ρ)
        (A1fun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) p1.succ p1.succ.le_last
  let dPsucc1 := (fderiv ℝ Psucc1 z) v
  let NextNextfun : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
      Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
        (K := ℝ) (ρ := ρ) (κ := κ')
        (A1fun y) (A3fun y) (Cfun y) (p1.val + 1)
        (Nat.succ_le_of_lt p1.isLt)
  let Cprod2 :
      RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) (κ' r2.castSucc) ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
        (Cfun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) r2.castSucc r2.castSucc.le_last
  let Cnext2 :
      RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) (κ' r2.succ) ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
        (Cfun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) r2.succ r2.succ.le_last
  let A3p2 :
      RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix (κ' r2.castSucc) ρ ℝ :=
    fun y ↦ by
      simpa [p2, r2] using A3fun y p2
  let dG2 : Matrix (κ' r2.castSucc) ρ ℝ := by
    simpa [p2, r2] using v.2.2.1 q2
  let Pcast2 : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct
        (K := ℝ) (κ := fun _ : Fin ((((M + 1) + 1) + 1) + 2) ↦ ρ)
        (A1fun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) p2.castSucc
        p2.castSucc.le_last
  let Psucc2 : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct
        (K := ℝ) (κ := fun _ : Fin ((((M + 1) + 1) + 1) + 2) ↦ ρ)
        (A1fun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) p2.succ p2.succ.le_last
  let dPsucc2 := (fderiv ℝ Psucc2 z) v
  let NextNextNextfun : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
      Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
        (K := ℝ) (ρ := ρ) (κ := κ')
        (A1fun y) (A3fun y) (Cfun y) (p2.val + 1)
        (Nat.succ_le_of_lt p2.isLt)
  let dNext2 : Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) ρ ℝ :=
    -(((fderiv ℝ Cnext2 z) v * data.C r2 + Cnext2 z * v.2.2.2.1 r2) *
        A3p2 z * (Pcast2 z)⁻¹)
      - (Cprod2 z * dG2 * (Pcast2 z)⁻¹)
      + Cprod2 z * A3p2 z * (Pcast2 z)⁻¹ *
          (dPsucc2 * coord.solvedA1 p2 + Psucc2 z * v.1 u2) *
          (Pcast2 z)⁻¹
      + (fderiv ℝ NextNextNextfun z) v
  let dNext1 : Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) ρ ℝ :=
    -(((fderiv ℝ Cnext1 z) v * data.C r1 + Cnext1 z * v.2.2.2.1 r1) *
        A3p1 z * (Pcast1 z)⁻¹)
      - (Cprod1 z * dG1 * (Pcast1 z)⁻¹)
      + Cprod1 z * A3p1 z * (Pcast1 z)⁻¹ *
          (dPsucc1 * coord.solvedA1 p1 + Psucc1 z * v.1 u1) *
          (Pcast1 z)⁻¹
      + dNext2
  let dEarly : Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) ρ ℝ :=
    -(((fderiv ℝ Cnext z) v * data.C r0 + Cnext z * v.2.2.2.1 r0) *
        A3p z * (Pcast z)⁻¹)
      - (Cprod z * dG * (Pcast z)⁻¹)
      + Cprod z * A3p z * (Pcast z)⁻¹ *
          (dPsucc * coord.solvedA1 p0 +
            Psucc z *
              (Tail⁻¹ * v.2.2.2.2.1 -
                Tail⁻¹ * dTail * Tail⁻¹ * data.Ctop)) *
          (Pcast z)⁻¹
      + dNext1
  let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
  have hF3base :=
    F3_tail_pos_pos_dEarly_zero_next_succ_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (M := M + 1) (ρ := ρ) (κ' := κ') hz v
  have hF3 :
      Dzv.2.2.2.2.2
        - (-(((fderiv ℝ Cnext z) v * data.C r0 + Cnext z * v.2.2.2.1 r0) *
              A3p z * (Pcast z)⁻¹)
            - (Cprod z * dG * (Pcast z)⁻¹)
            + Cprod z * A3p z * (Pcast z)⁻¹ *
                (dPsucc * coord.solvedA1 p0 +
                  Psucc z *
                    (Tail⁻¹ * v.2.2.2.2.1 -
                      Tail⁻¹ * dTail * Tail⁻¹ * data.Ctop)) *
                (Pcast z)⁻¹
            + (-(((fderiv ℝ Cnext1 z) v * data.C r1 + Cnext1 z * v.2.2.2.1 r1) *
                  A3p1 z * (Pcast1 z)⁻¹)
                - (Cprod1 z * dG1 * (Pcast1 z)⁻¹)
                + Cprod1 z * A3p1 z * (Pcast1 z)⁻¹ *
                    (dPsucc1 * coord.solvedA1 p1 + Psucc1 z * v.1 u1) *
                    (Pcast1 z)⁻¹
                + (fderiv ℝ NextNextfun z) v)) *
            coord.solvedA1 (Fin.last (((M + 1) + 1) + 1))
        + (coord.F3 - Earlyfun z) *
            (Dzv.1 qLast
              - XsuccF2 qLast.succ * coord.solvedA3 qLast.succ
              - coord.F2 qLast.succ.succ *
                  rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv qLast.succ) =
        ((retainedPassiveFormalRawOrderJacobianAt
            (ρ := ρ) (κ' := κ') z) v).2.2.2.2.2 := by
    simpa [A1fun, A3fun, Cfun, Earlyfun, Cprod, Cnext, A3p, dG, Pcast,
      Psucc, dPsucc, Tfun, Tail, dTail, Cprod1, Cnext1, A3p1, dG1,
      Pcast1, Psucc1, dPsucc1, NextNextfun, data, coord, Dzv, XsuccF2,
      qLast, q0, p0, r0, s0, q1, u1, p1, r1] using hF3base
  have hNextNextBase :=
    fderiv_retainedPassiveLowerLeftProductTailSum_succ_product_dCprod_dG_dPcast_apply
      (M := (M + 1) + 1) (ρ := ρ) (κ' := κ') hz v s1
  have hNextNext : (fderiv ℝ NextNextfun z) v = dNext2 := by
    simpa [A1fun, A3fun, Cfun, NextNextfun, Cprod2, Cnext2, A3p2, dG2,
      Pcast2, Psucc2, dPsucc2, NextNextNextfun, dNext2, data, coord, t0, s1,
      q2, u2, p2, r2, s0, q1, p1] using hNextNextBase
  rw [hNextNext] at hF3
  simpa [A1fun, A3fun, Cfun, Earlyfun, Cprod, Cnext, A3p, dG, Pcast,
    Psucc, dPsucc, Tfun, Tail, dTail, Cprod1, Cnext1, A3p1, dG1, Pcast1,
    Psucc1, dPsucc1, NextNextfun, Cprod2, Cnext2, A3p2, dG2, Pcast2,
    Psucc2, dPsucc2, NextNextNextfun, dNext2, dNext1, dEarly, data, coord,
    Dzv, XsuccF2, qLast, q0, p0, r0, s0, q1, u1, p1, r1, t0, s1, q2, u2,
    p2, r2] using hF3

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- The three-positive-tail `F3` bridge with the first two recursive successor
recurrences substituted recovers the source `F3` tangent by right-multiplying
with the inverse of the negative terminal solved top-left factor. -/
theorem F3_tail_pos_pos_pos_dEarly_zero_next_succ_next_succ_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3
    {M : ℕ} {ρ : Type*} {κ' : Fin ((((M + 1) + 1) + 1) + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    let Dzv := (fderiv ℝ raw z) v
    let qLast : Fin (((M + 1) + 1) + 1) := Fin.last ((M + 1) + 1)
    let q0 : Fin (((M + 1) + 1) + 1) := 0
    let p0 : Fin ((((M + 1) + 1) + 1) + 1) := q0.castSucc
    let r0 : Fin ((((M + 1) + 1) + 1) + 1) := q0.succ
    let s0 : Fin ((M + 1) + 1) := 0
    let q1 : Fin (((M + 1) + 1) + 1) := s0.succ
    let u1 : Fin (((M + 1) + 1) + 1) := s0.castSucc
    let p1 : Fin ((((M + 1) + 1) + 1) + 1) := q1.castSucc
    let r1 : Fin ((((M + 1) + 1) + 1) + 1) := q1.succ
    let t0 : Fin (M + 1) := 0
    let s1 : Fin ((M + 1) + 1) := t0.succ
    let q2 : Fin (((M + 1) + 1) + 1) := s1.succ
    let u2 : Fin (((M + 1) + 1) + 1) := s1.castSucc
    let p2 : Fin ((((M + 1) + 1) + 1) + 1) := q2.castSucc
    let r2 : Fin ((((M + 1) + 1) + 1) + 1) := q2.succ
    let A1fun : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Fin ((((M + 1) + 1) + 1) + 1) → Matrix ρ ρ ℝ :=
      fun y p ↦
        ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p
    let A3fun :
        RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
          ∀ p : Fin ((((M + 1) + 1) + 1) + 1), Matrix (κ' p.succ) ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed
    let Cfun :
        RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
          ∀ p : Fin ((((M + 1) + 1) + 1) + 1), Matrix (κ' p.succ) (κ' p.castSucc) ℝ :=
      fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
    let Earlyfun : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
          (K := ℝ) (ρ := ρ) (κ := κ')
          (A1fun y) (A3fun y) (Cfun y) p0.val (Nat.le_of_lt p0.isLt)
    let Cprod :
        RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
          Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) (κ' r0.castSucc) ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
          (Cfun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) r0.castSucc r0.castSucc.le_last
    let Cnext :
        RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
          Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) (κ' r0.succ) ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
          (Cfun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) r0.succ r0.succ.le_last
    let A3p :
        RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
          Matrix (κ' r0.castSucc) ρ ℝ :=
      fun y ↦ by
        simpa [p0, r0] using A3fun y p0
    let dG : Matrix (κ' r0.castSucc) ρ ℝ := by
      simpa [p0, r0] using v.2.2.1 q0
    let Pcast : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct
          (K := ℝ) (κ := fun _ : Fin ((((M + 1) + 1) + 1) + 2) ↦ ρ)
          (A1fun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) p0.castSucc
          p0.castSucc.le_last
    let Psucc : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct
          (K := ℝ) (κ := fun _ : Fin ((((M + 1) + 1) + 1) + 2) ↦ ρ)
          (A1fun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) p0.succ p0.succ.le_last
    let dPsucc := (fderiv ℝ Psucc z) v
    let Tfun : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
    let Tail := ChartLocalSuffixState.retainedPassiveA1TailAfterFirst
      (K := ℝ) (ρ := ρ) data.A1seed
    let dTail := (fderiv ℝ Tfun z) v
    let Cprod1 :
        RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
          Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) (κ' r1.castSucc) ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
          (Cfun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) r1.castSucc r1.castSucc.le_last
    let Cnext1 :
        RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
          Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) (κ' r1.succ) ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
          (Cfun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) r1.succ r1.succ.le_last
    let A3p1 :
        RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
          Matrix (κ' r1.castSucc) ρ ℝ :=
      fun y ↦ by
        simpa [p1, r1] using A3fun y p1
    let dG1 : Matrix (κ' r1.castSucc) ρ ℝ := by
      simpa [p1, r1] using v.2.2.1 q1
    let Pcast1 : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct
          (K := ℝ) (κ := fun _ : Fin ((((M + 1) + 1) + 1) + 2) ↦ ρ)
          (A1fun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) p1.castSucc
          p1.castSucc.le_last
    let Psucc1 : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct
          (K := ℝ) (κ := fun _ : Fin ((((M + 1) + 1) + 1) + 2) ↦ ρ)
          (A1fun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) p1.succ p1.succ.le_last
    let dPsucc1 := (fderiv ℝ Psucc1 z) v
    let Cprod2 :
        RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
          Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) (κ' r2.castSucc) ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
          (Cfun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) r2.castSucc r2.castSucc.le_last
    let Cnext2 :
        RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
          Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) (κ' r2.succ) ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
          (Cfun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) r2.succ r2.succ.le_last
    let A3p2 :
        RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
          Matrix (κ' r2.castSucc) ρ ℝ :=
      fun y ↦ by
        simpa [p2, r2] using A3fun y p2
    let dG2 : Matrix (κ' r2.castSucc) ρ ℝ := by
      simpa [p2, r2] using v.2.2.1 q2
    let Pcast2 : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct
          (K := ℝ) (κ := fun _ : Fin ((((M + 1) + 1) + 1) + 2) ↦ ρ)
          (A1fun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) p2.castSucc
          p2.castSucc.le_last
    let Psucc2 : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix ρ ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.residualFactorProduct
          (K := ℝ) (κ := fun _ : Fin ((((M + 1) + 1) + 1) + 2) ↦ ρ)
          (A1fun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) p2.succ p2.succ.le_last
    let dPsucc2 := (fderiv ℝ Psucc2 z) v
    let NextNextNextfun : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) ρ ℝ :=
      fun y ↦
        ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
          (K := ℝ) (ρ := ρ) (κ := κ')
          (A1fun y) (A3fun y) (Cfun y) (p2.val + 1)
          (Nat.succ_le_of_lt p2.isLt)
    let dNext2 : Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) ρ ℝ :=
      -(((fderiv ℝ Cnext2 z) v * data.C r2 + Cnext2 z * v.2.2.2.1 r2) *
          A3p2 z * (Pcast2 z)⁻¹)
        - (Cprod2 z * dG2 * (Pcast2 z)⁻¹)
        + Cprod2 z * A3p2 z * (Pcast2 z)⁻¹ *
            (dPsucc2 * coord.solvedA1 p2 + Psucc2 z * v.1 u2) *
            (Pcast2 z)⁻¹
        + (fderiv ℝ NextNextNextfun z) v
    let dNext1 : Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) ρ ℝ :=
      -(((fderiv ℝ Cnext1 z) v * data.C r1 + Cnext1 z * v.2.2.2.1 r1) *
          A3p1 z * (Pcast1 z)⁻¹)
        - (Cprod1 z * dG1 * (Pcast1 z)⁻¹)
        + Cprod1 z * A3p1 z * (Pcast1 z)⁻¹ *
            (dPsucc1 * coord.solvedA1 p1 + Psucc1 z * v.1 u1) *
            (Pcast1 z)⁻¹
        + dNext2
    let dEarly : Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) ρ ℝ :=
      -(((fderiv ℝ Cnext z) v * data.C r0 + Cnext z * v.2.2.2.1 r0) *
          A3p z * (Pcast z)⁻¹)
        - (Cprod z * dG * (Pcast z)⁻¹)
        + Cprod z * A3p z * (Pcast z)⁻¹ *
            (dPsucc * coord.solvedA1 p0 +
              Psucc z *
                (Tail⁻¹ * v.2.2.2.2.1 -
                  Tail⁻¹ * dTail * Tail⁻¹ * data.Ctop)) *
            (Pcast z)⁻¹
        + dNext1
    let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
    (Dzv.2.2.2.2.2
      - dEarly * coord.solvedA1 (Fin.last (((M + 1) + 1) + 1))
      + (coord.F3 - Earlyfun z) *
          (Dzv.1 qLast
            - XsuccF2 qLast.succ * coord.solvedA3 qLast.succ
            - coord.F2 qLast.succ.succ *
                rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv qLast.succ)) *
        (-(coord.solvedA1 (Fin.last (((M + 1) + 1) + 1))))⁻¹ =
      v.2.2.2.2.2 := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  let qLast : Fin (((M + 1) + 1) + 1) := Fin.last ((M + 1) + 1)
  let q0 : Fin (((M + 1) + 1) + 1) := 0
  let p0 : Fin ((((M + 1) + 1) + 1) + 1) := q0.castSucc
  let r0 : Fin ((((M + 1) + 1) + 1) + 1) := q0.succ
  let s0 : Fin ((M + 1) + 1) := 0
  let q1 : Fin (((M + 1) + 1) + 1) := s0.succ
  let u1 : Fin (((M + 1) + 1) + 1) := s0.castSucc
  let p1 : Fin ((((M + 1) + 1) + 1) + 1) := q1.castSucc
  let r1 : Fin ((((M + 1) + 1) + 1) + 1) := q1.succ
  let t0 : Fin (M + 1) := 0
  let s1 : Fin ((M + 1) + 1) := t0.succ
  let q2 : Fin (((M + 1) + 1) + 1) := s1.succ
  let u2 : Fin (((M + 1) + 1) + 1) := s1.castSucc
  let p2 : Fin ((((M + 1) + 1) + 1) + 1) := q2.castSucc
  let r2 : Fin ((((M + 1) + 1) + 1) + 1) := q2.succ
  let A1fun : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
      Fin ((((M + 1) + 1) + 1) + 1) → Matrix ρ ρ ℝ :=
    fun y p ↦
      ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p
  let A3fun :
      RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        ∀ p : Fin ((((M + 1) + 1) + 1) + 1), Matrix (κ' p.succ) ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed
  let Cfun :
      RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        ∀ p : Fin ((((M + 1) + 1) + 1) + 1), Matrix (κ' p.succ) (κ' p.castSucc) ℝ :=
    fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
  let Earlyfun : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
      Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
        (K := ℝ) (ρ := ρ) (κ := κ')
        (A1fun y) (A3fun y) (Cfun y) p0.val (Nat.le_of_lt p0.isLt)
  let Cprod :
      RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) (κ' r0.castSucc) ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
        (Cfun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) r0.castSucc r0.castSucc.le_last
  let Cnext :
      RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) (κ' r0.succ) ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
        (Cfun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) r0.succ r0.succ.le_last
  let A3p :
      RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix (κ' r0.castSucc) ρ ℝ :=
    fun y ↦ by
      simpa [p0, r0] using A3fun y p0
  let dG : Matrix (κ' r0.castSucc) ρ ℝ := by
    simpa [p0, r0] using v.2.2.1 q0
  let Pcast : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct
        (K := ℝ) (κ := fun _ : Fin ((((M + 1) + 1) + 1) + 2) ↦ ρ)
        (A1fun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) p0.castSucc
        p0.castSucc.le_last
  let Psucc : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct
        (K := ℝ) (κ := fun _ : Fin ((((M + 1) + 1) + 1) + 2) ↦ ρ)
        (A1fun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) p0.succ p0.succ.le_last
  let dPsucc := (fderiv ℝ Psucc z) v
  let Tfun : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
  let Tail := ChartLocalSuffixState.retainedPassiveA1TailAfterFirst
    (K := ℝ) (ρ := ρ) data.A1seed
  let dTail := (fderiv ℝ Tfun z) v
  let Cprod1 :
      RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) (κ' r1.castSucc) ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
        (Cfun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) r1.castSucc r1.castSucc.le_last
  let Cnext1 :
      RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) (κ' r1.succ) ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
        (Cfun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) r1.succ r1.succ.le_last
  let A3p1 :
      RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix (κ' r1.castSucc) ρ ℝ :=
    fun y ↦ by
      simpa [p1, r1] using A3fun y p1
  let dG1 : Matrix (κ' r1.castSucc) ρ ℝ := by
    simpa [p1, r1] using v.2.2.1 q1
  let Pcast1 : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct
        (K := ℝ) (κ := fun _ : Fin ((((M + 1) + 1) + 1) + 2) ↦ ρ)
        (A1fun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) p1.castSucc
        p1.castSucc.le_last
  let Psucc1 : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct
        (K := ℝ) (κ := fun _ : Fin ((((M + 1) + 1) + 1) + 2) ↦ ρ)
        (A1fun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) p1.succ p1.succ.le_last
  let dPsucc1 := (fderiv ℝ Psucc1 z) v
  let Cprod2 :
      RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) (κ' r2.castSucc) ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
        (Cfun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) r2.castSucc r2.castSucc.le_last
  let Cnext2 :
      RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) (κ' r2.succ) ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct (K := ℝ) (κ := κ')
        (Cfun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) r2.succ r2.succ.le_last
  let A3p2 :
      RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
        Matrix (κ' r2.castSucc) ρ ℝ :=
    fun y ↦ by
      simpa [p2, r2] using A3fun y p2
  let dG2 : Matrix (κ' r2.castSucc) ρ ℝ := by
    simpa [p2, r2] using v.2.2.1 q2
  let Pcast2 : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct
        (K := ℝ) (κ := fun _ : Fin ((((M + 1) + 1) + 1) + 2) ↦ ρ)
        (A1fun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) p2.castSucc
        p2.castSucc.le_last
  let Psucc2 : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct
        (K := ℝ) (κ := fun _ : Fin ((((M + 1) + 1) + 1) + 2) ↦ ρ)
        (A1fun y) (Fin.last ((((M + 1) + 1) + 1) + 1)) p2.succ p2.succ.le_last
  let dPsucc2 := (fderiv ℝ Psucc2 z) v
  let NextNextNextfun : RetainedPassiveRawTopologyTuple (M := ((M + 1) + 1) + 1) ρ κ' ℝ →
      Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
        (K := ℝ) (ρ := ρ) (κ := κ')
        (A1fun y) (A3fun y) (Cfun y) (p2.val + 1)
        (Nat.succ_le_of_lt p2.isLt)
  let dNext2 : Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) ρ ℝ :=
    -(((fderiv ℝ Cnext2 z) v * data.C r2 + Cnext2 z * v.2.2.2.1 r2) *
        A3p2 z * (Pcast2 z)⁻¹)
      - (Cprod2 z * dG2 * (Pcast2 z)⁻¹)
      + Cprod2 z * A3p2 z * (Pcast2 z)⁻¹ *
          (dPsucc2 * coord.solvedA1 p2 + Psucc2 z * v.1 u2) *
          (Pcast2 z)⁻¹
      + (fderiv ℝ NextNextNextfun z) v
  let dNext1 : Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) ρ ℝ :=
    -(((fderiv ℝ Cnext1 z) v * data.C r1 + Cnext1 z * v.2.2.2.1 r1) *
        A3p1 z * (Pcast1 z)⁻¹)
      - (Cprod1 z * dG1 * (Pcast1 z)⁻¹)
      + Cprod1 z * A3p1 z * (Pcast1 z)⁻¹ *
          (dPsucc1 * coord.solvedA1 p1 + Psucc1 z * v.1 u1) *
          (Pcast1 z)⁻¹
      + dNext2
  let dEarly : Matrix (κ' (Fin.last ((((M + 1) + 1) + 1) + 1))) ρ ℝ :=
    -(((fderiv ℝ Cnext z) v * data.C r0 + Cnext z * v.2.2.2.1 r0) *
        A3p z * (Pcast z)⁻¹)
      - (Cprod z * dG * (Pcast z)⁻¹)
      + Cprod z * A3p z * (Pcast z)⁻¹ *
          (dPsucc * coord.solvedA1 p0 +
            Psucc z *
              (Tail⁻¹ * v.2.2.2.2.1 -
                Tail⁻¹ * dTail * Tail⁻¹ * data.Ctop)) *
          (Pcast z)⁻¹
      + dNext1
  let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
  have hF3 :=
    F3_tail_pos_pos_pos_dEarly_zero_next_succ_next_succ_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (M := M) (ρ := ρ) (κ' := κ') hz v
  have hrec :=
    retainedPassiveFormalRawOrderJacobianAt_recovers_F3
      (ρ := ρ) (κ' := κ') hz v
  change Dzv.2.2.2.2.2
      - dEarly * coord.solvedA1 (Fin.last (((M + 1) + 1) + 1))
      + (coord.F3 - Earlyfun z) *
          (Dzv.1 qLast
            - XsuccF2 qLast.succ * coord.solvedA3 qLast.succ
            - coord.F2 qLast.succ.succ *
                rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv qLast.succ) =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.2 at hF3
  change (Dzv.2.2.2.2.2
      - dEarly * coord.solvedA1 (Fin.last (((M + 1) + 1) + 1))
      + (coord.F3 - Earlyfun z) *
          (Dzv.1 qLast
            - XsuccF2 qLast.succ * coord.solvedA3 qLast.succ
            - coord.F2 qLast.succ.succ *
                rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv qLast.succ)) *
        (-(coord.solvedA1 (Fin.last (((M + 1) + 1) + 1))))⁻¹ =
      v.2.2.2.2.2
  rw [hF3]
  simpa [coord, data] using hrec

set_option linter.style.longLine false in
/-- In the single-edge case, the terminal `F3` shear can be staged with the
target-recovered first top-left branch.  No positive-tail lower-left product
derivative recurrence is used. -/
theorem F3_tail_zero_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
    {ρ : Type*} {κ' : Fin 2 → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := 0) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := 0) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    let Dzv := (fderiv ℝ raw z) v
    let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
    Dzv.2.2.2.2.2
      + coord.F3 *
          (Dzv.2.2.2.2.1
            - XsuccF2 0 * coord.solvedA3 0
            - coord.F2 (0 : Fin 1).succ *
                rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv 0) =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.2 := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
  let A1fun : RetainedPassiveRawTopologyTuple (M := 0) ρ κ' ℝ →
      Fin 1 → Matrix ρ ρ ℝ :=
    fun y p ↦
      ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p
  let Earlyfun : RetainedPassiveRawTopologyTuple (M := 0) ρ κ' ℝ →
      Matrix (κ' (Fin.last 1)) ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
        (K := ℝ) (ρ := ρ) (κ := κ')
        (A1fun y)
        (ChartLocalSuffixState.retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
        0 (Nat.zero_le 1)
  let Lastfun : RetainedPassiveRawTopologyTuple (M := 0) ρ κ' ℝ →
      Matrix ρ ρ ℝ :=
    fun y ↦
      ChartLocalSuffixState.residualFactorProduct
        (K := ℝ) (κ := fun _ : Fin 2 ↦ ρ)
        (A1fun y) (Fin.last 1) (Fin.last 0).castSucc
          (Fin.last 0).castSucc.le_last
  have hF3 :=
    F3_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (ρ := ρ) (κ' := κ') hz v
  have hCtop :=
    Ctop_tail_zero_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop
      (ρ := ρ) (κ' := κ') hz v
  have hEarlyfun : Earlyfun = fun _ ↦ 0 := by
    funext y
    simp [Earlyfun]
  have hdEarly : (fderiv ℝ Earlyfun z) v = 0 := by
    rw [hEarlyfun]
    rw [fderiv_const_apply]
    rfl
  have hEarlyz : Earlyfun z = 0 := by
    simp [hEarlyfun]
  have hLastfun :
      Lastfun =
        fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.Ctop := by
    funext y
    let A : Fin 1 → Matrix ρ ρ ℝ :=
      fun p ↦
        ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p
    have hlast :=
      retainedPassiveLastTopResidualFactorProduct_eq
        (K := ℝ) (ρ := ρ) (M := 0) A
    have hA0 :
        A (Fin.last 0) =
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.Ctop := by
      simp [A, ChartLocalSuffixState.RetainedPassiveCoordinateData.solvedA1,
        ChartLocalSuffixState.retainedPassiveA1TailAfterFirst]
    change
      ChartLocalSuffixState.residualFactorProduct
          (K := ℝ) (κ := fun _ : Fin 2 ↦ ρ) A
          (Fin.last 1) (Fin.last 0).castSucc (Fin.last 0).castSucc.le_last =
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.Ctop
    exact hlast.trans hA0
  have hdLast : (fderiv ℝ Lastfun z) v = v.2.2.2.2.1 := by
    rw [hLastfun]
    change (fderiv ℝ
        (fun y : RetainedPassiveRawTopologyTuple (M := 0) ρ κ' ℝ ↦
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).Ctop) z) v =
      v.2.2.2.2.1
    change (fderiv ℝ
        (fun y : RetainedPassiveRawTopologyTuple (M := 0) ρ κ' ℝ ↦
          y.2.2.2.2.1) z) v = v.2.2.2.2.1
    let LCtop : RetainedPassiveRawTopologyTuple (M := 0) ρ κ' ℝ →L[ℝ] Matrix ρ ρ ℝ :=
      { toLinearMap :=
          { toFun := fun y ↦ y.2.2.2.2.1
            map_add' := by
              intro x y
              rfl
            map_smul' := by
              intro a y
              rfl }
        cont := by fun_prop }
    have hLCtop :
        fderiv ℝ
            (fun y : RetainedPassiveRawTopologyTuple (M := 0) ρ κ' ℝ ↦
              y.2.2.2.2.1) z = LCtop :=
      LCtop.fderiv
    rw [hLCtop]
    rfl
  change Dzv.2.2.2.2.2
      - (fderiv ℝ Earlyfun z) v * Lastfun z
      + (coord.F3 - Earlyfun z) * (fderiv ℝ Lastfun z) v =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.2 at hF3
  rw [hdEarly, hEarlyz, hdLast] at hF3
  have hF3zero :
      Dzv.2.2.2.2.2 + coord.F3 * v.2.2.2.2.1 =
        ((retainedPassiveFormalRawOrderJacobianAt
            (ρ := ρ) (κ' := κ') z) v).2.2.2.2.2 := by
    calc
      Dzv.2.2.2.2.2 + coord.F3 * v.2.2.2.2.1 =
          Dzv.2.2.2.2.2
            - (0 : Matrix (κ' (Fin.last 1)) ρ ℝ) * Lastfun z
            + (coord.F3 - 0) * v.2.2.2.2.1 := by
              rw [Matrix.zero_mul, sub_zero, sub_zero]
      _ =
          ((retainedPassiveFormalRawOrderJacobianAt
              (ρ := ρ) (κ' := κ') z) v).2.2.2.2.2 := hF3
  have hCtop' :
      Dzv.2.2.2.2.1
        - XsuccF2 0 * coord.solvedA3 0
        - coord.F2 (0 : Fin 1).succ *
            rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv 0 =
      v.2.2.2.2.1 := by
    change
      ChartLocalSuffixState.retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
          data.A1seed *
        (Dzv.2.2.2.2.1
          - XsuccF2 0 * coord.solvedA3 0
          - coord.F2 (0 : Fin 1).succ *
              rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv 0) =
        v.2.2.2.2.1 at hCtop
    simpa [data, ChartLocalSuffixState.retainedPassiveA1TailAfterFirst] using hCtop
  change Dzv.2.2.2.2.2
      + coord.F3 *
          (Dzv.2.2.2.2.1
            - XsuccF2 0 * coord.solvedA3 0
            - coord.F2 (0 : Fin 1).succ *
                rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv 0) =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.2
  rw [hCtop']
  exact hF3zero

set_option linter.style.longLine false in
/-- In the single-edge case, the target-staged terminal `F3` branch recovers
the source `F3` tangent by right-multiplying by the inverse of `-Ctop`. -/
theorem F3_tail_zero_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3
    {ρ : Type*} {κ' : Fin 2 → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : RetainedPassiveRawTopologyTuple (M := 0) ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : RetainedPassiveRawTopologyTuple (M := 0) ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    let Dzv := (fderiv ℝ raw z) v
    let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
    (Dzv.2.2.2.2.2
      + coord.F3 *
          (Dzv.2.2.2.2.1
            - XsuccF2 0 * coord.solvedA3 0
            - coord.F2 (0 : Fin 1).succ *
                rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv 0)) *
        (-(coord.Ctop))⁻¹ =
      v.2.2.2.2.2 := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let coord := data.toCoordinateData
  let Dzv := (fderiv ℝ raw z) v
  let XsuccF2 := retainedPassiveTargetRecoveredSuccessorF2At (ρ := ρ) (κ' := κ') z Dzv
  have hF3 :=
    F3_tail_zero_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
      (ρ := ρ) (κ' := κ') hz v
  have hrec :=
    retainedPassiveFormalRawOrderJacobianAt_recovers_F3
      (ρ := ρ) (κ' := κ') hz v
  change Dzv.2.2.2.2.2
      + coord.F3 *
          (Dzv.2.2.2.2.1
            - XsuccF2 0 * coord.solvedA3 0
            - coord.F2 (0 : Fin 1).succ *
                rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv 0) =
      ((retainedPassiveFormalRawOrderJacobianAt
          (ρ := ρ) (κ' := κ') z) v).2.2.2.2.2 at hF3
  change (Dzv.2.2.2.2.2
      + coord.F3 *
          (Dzv.2.2.2.2.1
            - XsuccF2 0 * coord.solvedA3 0
            - coord.F2 (0 : Fin 1).succ *
                rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') Dzv 0)) *
        (-(coord.Ctop))⁻¹ =
      v.2.2.2.2.2
  rw [hF3]
  simpa [coord, data, ChartLocalSuffixState.RetainedPassiveCoordinateData.solvedA1,
    ChartLocalSuffixState.retainedPassiveSolvedA1,
    ChartLocalSuffixState.retainedPassiveA1TailAfterFirst] using hrec

end Aoyagi
end DLN
end DLNFibre
