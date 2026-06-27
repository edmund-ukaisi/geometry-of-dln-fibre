import DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesTopology
import DLNFibre.DLN.Aoyagi.RetainedPassiveFormalLinearDeterminant

/-!
# Formal retained-passive blocks in raw tuple order

This file records the linear regrouping between the determinant-friendly formal
block order and the retained-passive `TopologyTuple` product order.  It is
pure product-coordinate bookkeeping: no analytic derivative theorem, no
Jacobian determinant formula for the raw map, no measure transport, no normal
crossings, and no RLCT extraction.
-/

noncomputable section

open Matrix

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- Abbreviation for the retained-passive raw `TopologyTuple` product order. -/
abbrev RetainedPassiveRawTopologyTuple
    {M : ℕ} (ρ : Type*) (κ' : Fin (M + 2) → Type*) (K : Type*) :=
  ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.TopologyTuple ρ κ' K

section EdgeRegrouping

variable {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*} [Semiring K]

/-- Regroup a dependent family of edge-local `(F,C)` pairs as separate
raw-order `F2` and `C` families. -/
def retainedPassiveFormalEdgeTangentLinearEquiv :
    RetainedPassiveFormalEdgeTangent (ρ := ρ) (κ' := κ') (K := K) ≃ₗ[K]
      ((∀ p : Fin (M + 1), Matrix ρ (κ' p.castSucc) K) ×
        (∀ p : Fin (M + 1), Matrix (κ' p.succ) (κ' p.castSucc) K)) where
  toFun v := (fun p => (v p).1, fun p => (v p).2)
  invFun v := fun p => (v.1 p, v.2 p)
  left_inv v := by
    funext p
    rfl
  right_inv v := by
    rcases v with ⟨F2, C⟩
    rfl
  map_add' v w := by
    rfl
  map_smul' a v := by
    rfl

@[simp]
theorem retainedPassiveFormalEdgeTangentLinearEquiv_apply
    (v : RetainedPassiveFormalEdgeTangent (ρ := ρ) (κ' := κ') (K := K)) :
    retainedPassiveFormalEdgeTangentLinearEquiv
        (ρ := ρ) (κ' := κ') (K := K) v =
      (fun p => (v p).1, fun p => (v p).2) :=
  rfl

@[simp]
theorem retainedPassiveFormalEdgeTangentLinearEquiv_symm_apply
    (v :
      (∀ p : Fin (M + 1), Matrix ρ (κ' p.castSucc) K) ×
        (∀ p : Fin (M + 1), Matrix (κ' p.succ) (κ' p.castSucc) K)) :
    (retainedPassiveFormalEdgeTangentLinearEquiv
        (ρ := ρ) (κ' := κ') (K := K)).symm v =
      fun p => (v.1 p, v.2 p) :=
  rfl

end EdgeRegrouping

section EdgePairRawEquiv

variable {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*} [CommRing K]
variable [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]

/-- The edge-local product equivalence transported to separated raw-order
`(F2,C)` families. -/
def retainedPassiveFormalRawF2CLinearEquiv
    (A : Fin (M + 1) → Matrix ρ ρ K)
    (H : ∀ p : Fin (M + 1), Matrix ρ (κ' p.succ) K)
    (G : ∀ p : Fin (M + 1), Matrix (κ' p.succ) ρ K)
    (hA : ∀ p : Fin (M + 1), IsUnit (A p).det) :
    ((∀ p : Fin (M + 1), Matrix ρ (κ' p.castSucc) K) ×
        (∀ p : Fin (M + 1), Matrix (κ' p.succ) (κ' p.castSucc) K)) ≃ₗ[K]
      ((∀ p : Fin (M + 1), Matrix ρ (κ' p.castSucc) K) ×
        (∀ p : Fin (M + 1), Matrix (κ' p.succ) (κ' p.castSucc) K)) :=
  ((retainedPassiveFormalEdgeTangentLinearEquiv
      (ρ := ρ) (κ' := κ') (K := K)).symm.trans
    (edgeLocalFCPairPiLinearEquiv
      (ρ := ρ) (κ' := κ') (K := K) A H G hA)).trans
    (retainedPassiveFormalEdgeTangentLinearEquiv
      (ρ := ρ) (κ' := κ') (K := K))

/-- Forward formula for the raw-order `(F2,C)` edge-pair product
equivalence. -/
theorem retainedPassiveFormalRawF2CLinearEquiv_apply
    (A : Fin (M + 1) → Matrix ρ ρ K)
    (H : ∀ p : Fin (M + 1), Matrix ρ (κ' p.succ) K)
    (G : ∀ p : Fin (M + 1), Matrix (κ' p.succ) ρ K)
    (hA : ∀ p : Fin (M + 1), IsUnit (A p).det)
    (v :
      (∀ p : Fin (M + 1), Matrix ρ (κ' p.castSucc) K) ×
        (∀ p : Fin (M + 1), Matrix (κ' p.succ) (κ' p.castSucc) K)) :
    retainedPassiveFormalRawF2CLinearEquiv
        (ρ := ρ) (κ' := κ') (K := K) A H G hA v =
      (fun p : Fin (M + 1) =>
          -(A p + H p * G p) * v.1 p + H p * v.2 p,
        fun p : Fin (M + 1) =>
          -G p * v.1 p + v.2 p) := by
  apply Prod.ext
  · funext p
    simp [retainedPassiveFormalRawF2CLinearEquiv,
      edgeLocalFCPairPiLinearEquiv, edgeLocalFCPairLinearMap_apply]
  · funext p
    simp [retainedPassiveFormalRawF2CLinearEquiv,
      edgeLocalFCPairPiLinearEquiv, edgeLocalFCPairLinearMap_apply]

/-- Inverse formula for the raw-order `(F2,C)` edge-pair product
equivalence. -/
theorem retainedPassiveFormalRawF2CLinearEquiv_symm_apply
    (A : Fin (M + 1) → Matrix ρ ρ K)
    (H : ∀ p : Fin (M + 1), Matrix ρ (κ' p.succ) K)
    (G : ∀ p : Fin (M + 1), Matrix (κ' p.succ) ρ K)
    (hA : ∀ p : Fin (M + 1), IsUnit (A p).det)
    (v :
      (∀ p : Fin (M + 1), Matrix ρ (κ' p.castSucc) K) ×
        (∀ p : Fin (M + 1), Matrix (κ' p.succ) (κ' p.castSucc) K)) :
    (retainedPassiveFormalRawF2CLinearEquiv
        (ρ := ρ) (κ' := κ') (K := K) A H G hA).symm v =
      (fun p : Fin (M + 1) => (A p)⁻¹ * (H p * v.2 p - v.1 p),
        fun p : Fin (M + 1) =>
          v.2 p + G p * ((A p)⁻¹ * (H p * v.2 p - v.1 p))) := by
  apply Prod.ext
  · funext p
    simp [retainedPassiveFormalRawF2CLinearEquiv,
      edgeLocalFCPairPiLinearEquiv, edgeLocalFCPairLinearMapInverse_apply]
  · funext p
    simp [retainedPassiveFormalRawF2CLinearEquiv,
      edgeLocalFCPairPiLinearEquiv, edgeLocalFCPairLinearMapInverse_apply]

end EdgePairRawEquiv

section UnitHelpers

variable {ι K : Type*} [CommRing K] [Fintype ι] [DecidableEq ι]

/-- If a square matrix has determinant a unit, then its total nonsingular
inverse also has determinant a unit. -/
theorem matrix_det_inv_isUnit_of_det_isUnit (A : Matrix ι ι K)
    (hA : IsUnit A.det) : IsUnit (A⁻¹).det :=
  Matrix.isUnit_det_of_right_inverse (A := A⁻¹) (B := A)
    (Matrix.nonsing_inv_mul A hA)

/-- Negating a square matrix preserves determinant-unit-ness. -/
theorem matrix_det_neg_isUnit_of_det_isUnit (A : Matrix ι ι K)
    (hA : IsUnit A.det) : IsUnit (-A).det := by
  rw [Matrix.det_neg]
  exact (isUnit_neg_one.pow _).mul hA

end UnitHelpers

section TotalRawOrder

variable {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*} [CommRing K]
variable [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]

/-- Reorder the determinant-friendly formal block tangent into the retained
passive raw `TopologyTuple` product order:

`(A1passive, A3passive, Ctop, edge (F,C), F3)` becomes
`(A1passive, F2, A3passive, C, Ctop, F3)`.
-/
def retainedPassiveFormalBlockToRawTopologyTupleLinearEquiv :
    RetainedPassiveTotalFormalBlockTangent (ρ := ρ) (κ' := κ') (K := K) ≃ₗ[K]
      RetainedPassiveRawTopologyTuple ρ κ' K where
  toFun v :=
    (v.1,
      (fun p => (v.2.2.2.1 p).1,
        (v.2.1,
          (fun p => (v.2.2.2.1 p).2,
            (v.2.2.1, v.2.2.2.2)))))
  invFun z :=
    (z.1,
      (z.2.2.1,
        (z.2.2.2.2.1,
          (fun p => (z.2.1 p, z.2.2.2.1 p), z.2.2.2.2.2))))
  left_inv v := by
    rcases v with ⟨A1, A3, Ctop, edge, F3⟩
    rfl
  right_inv z := by
    rcases z with ⟨A1, F2, A3, C, Ctop, F3⟩
    rfl
  map_add' v w := by
    rfl
  map_smul' a v := by
    rfl

omit [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] in
@[simp]
theorem retainedPassiveFormalBlockToRawTopologyTupleLinearEquiv_apply
    (v : RetainedPassiveTotalFormalBlockTangent (ρ := ρ) (κ' := κ') (K := K)) :
    retainedPassiveFormalBlockToRawTopologyTupleLinearEquiv
        (ρ := ρ) (κ' := κ') (K := K) v =
      (v.1,
        (fun p => (v.2.2.2.1 p).1,
          (v.2.1,
            (fun p => (v.2.2.2.1 p).2,
              (v.2.2.1, v.2.2.2.2))))) :=
  rfl

omit [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] in
@[simp]
theorem retainedPassiveFormalBlockToRawTopologyTupleLinearEquiv_symm_apply
    (z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' K) :
    (retainedPassiveFormalBlockToRawTopologyTupleLinearEquiv
        (ρ := ρ) (κ' := κ') (K := K)).symm z =
      (z.1,
        (z.2.2.1,
          (z.2.2.2.2.1,
            (fun p => (z.2.1 p, z.2.2.2.1 p), z.2.2.2.2.2)))) :=
  rfl

/-- The formal block map transported into the retained-passive raw
`TopologyTuple` product order. -/
def retainedPassiveFormalRawOrderJacobian
    (Tail : Matrix ρ ρ K)
    (A : Fin (M + 1) → Matrix ρ ρ K)
    (H : ∀ p : Fin (M + 1), Matrix ρ (κ' p.succ) K)
    (G : ∀ p : Fin (M + 1), Matrix (κ' p.succ) ρ K)
    (LastTop : Matrix ρ ρ K) :
    RetainedPassiveRawTopologyTuple ρ κ' K →ₗ[K]
      RetainedPassiveRawTopologyTuple ρ κ' K :=
  let e :=
    retainedPassiveFormalBlockToRawTopologyTupleLinearEquiv
      (ρ := ρ) (κ' := κ') (K := K)
  e.toLinearMap.comp
    ((retainedPassiveTotalFormalBlockJacobian
        (ρ := ρ) (κ' := κ') (K := K) Tail A H G LastTop).comp
      e.symm.toLinearMap)

/-- Apply formula for the formal block map after transport to raw tuple
order. -/
theorem retainedPassiveFormalRawOrderJacobian_apply
    (Tail : Matrix ρ ρ K)
    (A : Fin (M + 1) → Matrix ρ ρ K)
    (H : ∀ p : Fin (M + 1), Matrix ρ (κ' p.succ) K)
    (G : ∀ p : Fin (M + 1), Matrix (κ' p.succ) ρ K)
    (LastTop : Matrix ρ ρ K)
    (z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' K) :
    retainedPassiveFormalRawOrderJacobian
        (ρ := ρ) (κ' := κ') (K := K) Tail A H G LastTop z =
      (z.1,
        (fun p : Fin (M + 1) =>
            (-(A p + H p * G p) * z.2.1 p + H p * z.2.2.2.1 p),
          (z.2.2.1,
            (fun p : Fin (M + 1) =>
                -G p * z.2.1 p + z.2.2.2.1 p,
              (Tail⁻¹ * z.2.2.2.2.1,
                z.2.2.2.2.2 * (-LastTop)))))) := by
  rcases z with ⟨A1raw, F2, A3raw, C, Ctop, F3⟩
  ext <;>
    simp [retainedPassiveFormalRawOrderJacobian,
      retainedPassiveTotalFormalBlockJacobian,
      edgeLocalFCPairPiLinearMap, edgeLocalFCPairLinearMap_apply]

/-- Exact determinant of the formal retained-passive block map after
transport to the raw `TopologyTuple` product order.

This is a conjugation statement for the formal block map above.  It still does
not identify this transported formal map with the analytic derivative of
`topologyTupleEdgeRawOrder`.
-/
theorem retainedPassiveFormalRawOrderJacobian_det_eq
    (Tail : Matrix ρ ρ K)
    (A : Fin (M + 1) → Matrix ρ ρ K)
    (H : ∀ p : Fin (M + 1), Matrix ρ (κ' p.succ) K)
    (G : ∀ p : Fin (M + 1), Matrix (κ' p.succ) ρ K)
    (LastTop : Matrix ρ ρ K) :
    LinearMap.det
      (retainedPassiveFormalRawOrderJacobian
        (ρ := ρ) (κ' := κ') (K := K) Tail A H G LastTop) =
      (Tail⁻¹).det ^ Fintype.card ρ *
        (∏ p : Fin (M + 1), (-A p).det ^ Fintype.card (κ' p.castSucc)) *
          (-LastTop).det ^ Fintype.card (κ' (Fin.last (M + 1))) := by
  let e :=
    retainedPassiveFormalBlockToRawTopologyTupleLinearEquiv
      (ρ := ρ) (κ' := κ') (K := K)
  let L :=
    retainedPassiveTotalFormalBlockJacobian
      (ρ := ρ) (κ' := κ') (K := K) Tail A H G LastTop
  calc
    LinearMap.det
        (retainedPassiveFormalRawOrderJacobian
          (ρ := ρ) (κ' := κ') (K := K) Tail A H G LastTop) =
      LinearMap.det ((e : RetainedPassiveTotalFormalBlockTangent
          (ρ := ρ) (κ' := κ') (K := K) →ₗ[K]
            RetainedPassiveRawTopologyTuple ρ κ' K).comp
        (L.comp (e.symm : RetainedPassiveRawTopologyTuple ρ κ' K →ₗ[K]
          RetainedPassiveTotalFormalBlockTangent
            (ρ := ρ) (κ' := κ') (K := K)))) := by
        rfl
    _ = LinearMap.det L := by
        rw [LinearMap.det_conj L e]
    _ =
      (Tail⁻¹).det ^ Fintype.card ρ *
        (∏ p : Fin (M + 1), (-A p).det ^ Fintype.card (κ' p.castSucc)) *
          (-LastTop).det ^ Fintype.card (κ' (Fin.last (M + 1))) := by
        rw [retainedPassiveTotalFormalBlockJacobian_det_eq]

section RealAbsDet

variable {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
variable [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]

/-- Absolute determinant of the formal retained-passive raw-order Jacobian.

This is the sign-free version of `retainedPassiveFormalRawOrderJacobian_det_eq`.
It remains a formal determinant calculation and does not identify the formal
map with the analytic Frechet derivative of `topologyTupleEdgeRawOrder`. -/
theorem retainedPassiveFormalRawOrderJacobian_abs_det_eq
    (Tail : Matrix ρ ρ ℝ)
    (A : Fin (M + 1) → Matrix ρ ρ ℝ)
    (H : ∀ p : Fin (M + 1), Matrix ρ (κ' p.succ) ℝ)
    (G : ∀ p : Fin (M + 1), Matrix (κ' p.succ) ρ ℝ)
    (LastTop : Matrix ρ ρ ℝ) :
    |LinearMap.det
      (retainedPassiveFormalRawOrderJacobian
        (ρ := ρ) (κ' := κ') (K := ℝ) Tail A H G LastTop)| =
      |(Tail⁻¹).det| ^ Fintype.card ρ *
        (∏ p : Fin (M + 1), |(A p).det| ^ Fintype.card (κ' p.castSucc)) *
          |LastTop.det| ^ Fintype.card (κ' (Fin.last (M + 1))) := by
  rw [retainedPassiveFormalRawOrderJacobian_det_eq]
  rw [abs_mul, abs_mul, Finset.abs_prod]
  simp_rw [abs_pow]
  congr 2
  · refine Finset.prod_congr rfl ?_
    intro p _hp
    have hdet_abs : |(-A p).det| = |(A p).det| := by
      simp [Matrix.det_neg, abs_mul]
    rw [hdet_abs]
  · have hdet_abs : |(-LastTop).det| = |LastTop.det| := by
      simp [Matrix.det_neg, abs_mul]
    rw [hdet_abs]

end RealAbsDet

/-- The chart-specialized formal raw-order determinant is a unit.

This uses only the formal determinant formula and the retained-passive
determinant-chart unit facts.  It does not compare this formal raw-order map
with the analytic Frechet derivative of `topologyTupleEdgeRawOrder`.
-/
theorem retainedPassiveFormalRawOrderJacobian_det_isUnit_of_mem_topologyTupleDetChartSet
    [∀ j, DecidableEq (κ' j)]
    (z : RetainedPassiveRawTopologyTuple (M := M) ρ κ' K)
    (hz : z ∈
      ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.topologyTupleDetChartSet
        (K := K) (ρ := ρ) (κ' := κ')) :
    let data :
        ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
          (K := K) (ρ := ρ) κ' :=
      ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.ofTopologyTuple
        (K := K) (ρ := ρ) (κ' := κ') z
    let coord :
        ChartLocalSuffixState.RetainedPassiveCoordinateData
          (K := K) (ρ := ρ) κ' :=
      data.toCoordinateData
    IsUnit
      (LinearMap.det
        (retainedPassiveFormalRawOrderJacobian
          (ρ := ρ) (κ' := κ') (K := K)
          (ChartLocalSuffixState.retainedPassiveA1TailAfterFirst
            (K := K) (ρ := ρ) data.A1seed)
          (fun p : Fin (M + 1) => coord.solvedA1 p)
          (fun p : Fin (M + 1) => coord.F2 p.succ)
          (fun p : Fin (M + 1) => coord.solvedA3 p)
          (coord.solvedA1 (Fin.last M)))) := by
  classical
  let data :
      ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
        (K := K) (ρ := ρ) κ' :=
    ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.ofTopologyTuple
      (K := K) (ρ := ρ) (κ' := κ') z
  let coord :
      ChartLocalSuffixState.RetainedPassiveCoordinateData
        (K := K) (ρ := ρ) κ' :=
    data.toCoordinateData
  have hdet : data.detChart := hz
  have hPassive :
      ∀ p : Fin (M + 1), p ≠ 0 → IsUnit (coord.A1seed p).det := by
    simpa [coord, data] using
      data.toCoordinateData_passiveA1_units hdet.2
  have hTail :
      IsUnit
        (ChartLocalSuffixState.retainedPassiveA1TailAfterFirst
          (K := K) (ρ := ρ) data.A1seed).det := by
    simpa [coord, data] using
      ChartLocalSuffixState.retainedPassiveA1TailAfterFirst_det_isUnit_of_passive
        (K := K) (ρ := ρ) coord.A1seed hPassive
  have hSolvedA1 : ∀ p : Fin (M + 1), IsUnit (coord.solvedA1 p).det := by
    let h := open ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData in
      solvedA1_det_isUnit_of_detChart (K := K) (ρ := ρ) data hdet
    simpa [coord, data] using
      h
  change
    IsUnit
      (LinearMap.det
        (retainedPassiveFormalRawOrderJacobian
          (ρ := ρ) (κ' := κ') (K := K)
          (ChartLocalSuffixState.retainedPassiveA1TailAfterFirst
            (K := K) (ρ := ρ) data.A1seed)
          (fun p : Fin (M + 1) => coord.solvedA1 p)
          (fun p : Fin (M + 1) => coord.F2 p.succ)
          (fun p : Fin (M + 1) => coord.solvedA3 p)
          (coord.solvedA1 (Fin.last M))))
  rw [retainedPassiveFormalRawOrderJacobian_det_eq]
  refine
    (((matrix_det_inv_isUnit_of_det_isUnit
      (ChartLocalSuffixState.retainedPassiveA1TailAfterFirst
        (K := K) (ρ := ρ) data.A1seed)
      hTail).pow _).mul ?_).mul ?_
  · rw [IsUnit.prod_univ_iff]
    intro p
    exact
      (matrix_det_neg_isUnit_of_det_isUnit (coord.solvedA1 p)
        (hSolvedA1 p)).pow _
  · exact
      (matrix_det_neg_isUnit_of_det_isUnit
        (coord.solvedA1 (Fin.last M))
        (hSolvedA1 (Fin.last M))).pow _

end TotalRawOrder

end Aoyagi
end DLN
end DLNFibre
