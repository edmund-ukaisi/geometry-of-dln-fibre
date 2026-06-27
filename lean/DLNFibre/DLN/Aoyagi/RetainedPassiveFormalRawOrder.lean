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

end TotalRawOrder

end Aoyagi
end DLN
end DLNFibre
