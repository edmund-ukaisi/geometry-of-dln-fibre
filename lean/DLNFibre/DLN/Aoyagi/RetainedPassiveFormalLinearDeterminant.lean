import DLNFibre.DLN.Aoyagi.MatrixLinearDeterminant
import DLNFibre.DLN.Aoyagi.ProductReduction

/-!
# Formal retained-passive block determinant

This file records the block-order finite linear determinant calculation behind
the retained-passive p. 13 coordinate change in Aoyagi's Lemma 2.  It is a
formal algebraic Jacobian for the determinant factors only.  It does not prove
that this block map is the analytic derivative of the raw `TopologyTuple`
coordinate map, does not account for product-coordinate permutation signs, and
does not perform measure transport, normal-crossing reduction, or RLCT
extraction.
-/

noncomputable section

open Matrix

namespace DLNFibre
namespace DLN
namespace Aoyagi

section EdgeProduct

variable {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*} [CommRing K]
variable [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]

/-- Dependent product of the edge-local `(F,C)` tangent spaces. -/
abbrev RetainedPassiveFormalEdgeTangent :=
  ∀ p : Fin (M + 1),
    EdgeLocalFCPairTangent
      (ρ := ρ) (μ := κ' p.succ) (κ := κ' p.castSucc) (K := K)

/-- The dependent product of edge-local `(F,C)` linear maps. -/
def edgeLocalFCPairPiLinearMap
    (A : Fin (M + 1) → Matrix ρ ρ K)
    (H : ∀ p : Fin (M + 1), Matrix ρ (κ' p.succ) K)
    (G : ∀ p : Fin (M + 1), Matrix (κ' p.succ) ρ K) :
    RetainedPassiveFormalEdgeTangent (ρ := ρ) (κ' := κ') (K := K) →ₗ[K]
      RetainedPassiveFormalEdgeTangent (ρ := ρ) (κ' := κ') (K := K) :=
  LinearMap.pi fun p =>
    (edgeLocalFCPairLinearMap
        (ρ := ρ) (μ := κ' p.succ) (κ := κ' p.castSucc) (K := K)
        (A p) (H p) (G p)).comp (LinearMap.proj p)

/-- Determinant of the dependent product of edge-local `(F,C)` maps. -/
theorem edgeLocalFCPairPiLinearMap_det_eq
    (A : Fin (M + 1) → Matrix ρ ρ K)
    (H : ∀ p : Fin (M + 1), Matrix ρ (κ' p.succ) K)
    (G : ∀ p : Fin (M + 1), Matrix (κ' p.succ) ρ K) :
    LinearMap.det
      (edgeLocalFCPairPiLinearMap
        (ρ := ρ) (κ' := κ') (K := K) A H G) =
      ∏ p : Fin (M + 1), (-A p).det ^ Fintype.card (κ' p.castSucc) := by
  classical
  haveI :
      ∀ p : Fin (M + 1),
        Module.Finite K
          (EdgeLocalFCPairTangent
            (ρ := ρ) (μ := κ' p.succ) (κ := κ' p.castSucc) (K := K)) :=
    fun _p => moduleFinite_prod
  rw [edgeLocalFCPairPiLinearMap]
  rw [linearMap_det_piMap_eq_prod]
  refine Finset.prod_congr rfl ?_
  intro p _hp
  rw [edgeLocalFCPairLinearMap_det_eq]

end EdgeProduct

section TotalBlock

variable {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*} [CommRing K]
variable [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]

/-- Block-order tangent space for the formal retained-passive determinant
calculation.

The order is determinant-friendly rather than the raw `TopologyTuple` product
order:

* passive `A1` blocks,
* passive `A3` blocks,
* the `Ctop` solve block,
* the dependent product of edge-local `(F,C)` blocks,
* the terminal `F3` solve block.
-/
abbrev RetainedPassiveTotalFormalBlockTangent :=
  (Fin M → Matrix ρ ρ K) ×
    ((∀ p : Fin M, Matrix (κ' p.castSucc.succ) ρ K) ×
      (Matrix ρ ρ K ×
        (RetainedPassiveFormalEdgeTangent (ρ := ρ) (κ' := κ') (K := K) ×
          Matrix (κ' (Fin.last (M + 1))) ρ K)))

/-- Formal block-order retained-passive Jacobian.

`Tail` is the solved first-edge top-left tail and `LastTop` is the terminal
top-left block acting on the final `F3` variable.  The edge-local blocks use
the already-landed `(F,C)` determinant calculation. -/
def retainedPassiveTotalFormalBlockJacobian
    (Tail : Matrix ρ ρ K)
    (A : Fin (M + 1) → Matrix ρ ρ K)
    (H : ∀ p : Fin (M + 1), Matrix ρ (κ' p.succ) K)
    (G : ∀ p : Fin (M + 1), Matrix (κ' p.succ) ρ K)
    (LastTop : Matrix ρ ρ K) :
    RetainedPassiveTotalFormalBlockTangent (ρ := ρ) (κ' := κ') (K := K) →ₗ[K]
      RetainedPassiveTotalFormalBlockTangent (ρ := ρ) (κ' := κ') (K := K) :=
  (LinearMap.id :
      (Fin M → Matrix ρ ρ K) →ₗ[K] (Fin M → Matrix ρ ρ K)).prodMap
    ((LinearMap.id :
        (∀ p : Fin M, Matrix (κ' p.castSucc.succ) ρ K) →ₗ[K]
          (∀ p : Fin M, Matrix (κ' p.castSucc.succ) ρ K)).prodMap
      ((mulLeftLinearMap ρ K Tail⁻¹ :
          Matrix ρ ρ K →ₗ[K] Matrix ρ ρ K).prodMap
        ((edgeLocalFCPairPiLinearMap
            (ρ := ρ) (κ' := κ') (K := K) A H G).prodMap
          (mulRightLinearMap (κ' (Fin.last (M + 1))) K (-LastTop)))))

/-- Exact determinant of the formal retained-passive block-order Jacobian.

This is a signed determinant in the explicit block order above.  Passing to the
actual raw `TopologyTuple` product order may introduce a permutation sign; the
absolute determinant formula is insensitive to that later bookkeeping. -/
theorem retainedPassiveTotalFormalBlockJacobian_det_eq
    (Tail : Matrix ρ ρ K)
    (A : Fin (M + 1) → Matrix ρ ρ K)
    (H : ∀ p : Fin (M + 1), Matrix ρ (κ' p.succ) K)
    (G : ∀ p : Fin (M + 1), Matrix (κ' p.succ) ρ K)
    (LastTop : Matrix ρ ρ K) :
    LinearMap.det
      (retainedPassiveTotalFormalBlockJacobian
        (ρ := ρ) (κ' := κ') (K := K) Tail A H G LastTop) =
      (Tail⁻¹).det ^ Fintype.card ρ *
        (∏ p : Fin (M + 1), (-A p).det ^ Fintype.card (κ' p.castSucc)) *
          (-LastTop).det ^ Fintype.card (κ' (Fin.last (M + 1))) := by
  classical
  haveI : Module.Finite K (Fin M → Matrix ρ ρ K) :=
    moduleFinite_pi
  haveI :
      Module.Finite K (∀ p : Fin M, Matrix (κ' p.castSucc.succ) ρ K) :=
    moduleFinite_pi
  haveI :
      ∀ p : Fin (M + 1),
        Module.Finite K
          (EdgeLocalFCPairTangent
            (ρ := ρ) (μ := κ' p.succ) (κ := κ' p.castSucc) (K := K)) :=
    fun _p => moduleFinite_prod
  haveI :
      Module.Finite K
        (RetainedPassiveFormalEdgeTangent (ρ := ρ) (κ' := κ') (K := K)) :=
    moduleFinite_pi
  haveI :
      Module.Finite K
        (RetainedPassiveFormalEdgeTangent (ρ := ρ) (κ' := κ') (K := K) ×
          Matrix (κ' (Fin.last (M + 1))) ρ K) :=
    moduleFinite_prod
  haveI :
      Module.Finite K
        (Matrix ρ ρ K ×
          (RetainedPassiveFormalEdgeTangent (ρ := ρ) (κ' := κ') (K := K) ×
            Matrix (κ' (Fin.last (M + 1))) ρ K)) :=
    moduleFinite_prod
  haveI :
      Module.Finite K
        ((∀ p : Fin M, Matrix (κ' p.castSucc.succ) ρ K) ×
          (Matrix ρ ρ K ×
            (RetainedPassiveFormalEdgeTangent (ρ := ρ) (κ' := κ') (K := K) ×
              Matrix (κ' (Fin.last (M + 1))) ρ K))) :=
    moduleFinite_prod
  unfold retainedPassiveTotalFormalBlockJacobian
  rw [linearMap_det_prodMap_eq_mul]
  rw [linearMap_det_prodMap_eq_mul]
  rw [linearMap_det_prodMap_eq_mul]
  rw [linearMap_det_prodMap_eq_mul]
  rw [LinearMap.det_id, LinearMap.det_id]
  rw [linearMap_det_mulLeftLinearMap]
  rw [edgeLocalFCPairPiLinearMap_det_eq]
  rw [linearMap_det_mulRightLinearMap]
  ac_rfl

/-- The terminal one-edge residual-factor product is the last solved top
block, not the first-edge tail. -/
theorem retainedPassiveLastTopResidualFactorProduct_eq
    (A : Fin (M + 1) → Matrix ρ ρ K) :
    ChartLocalSuffixState.residualFactorProduct
        (K := K) (κ := fun _ : Fin (M + 2) => ρ)
        A (Fin.last (M + 1)) (Fin.last M).castSucc
          (Fin.last M).castSucc.le_last =
      A (Fin.last M) := by
  simpa using
    (ChartLocalSuffixState.residualFactorProduct_one_edge_eq_factor
      (K := K) (κ := fun _ : Fin (M + 2) => ρ)
      A (Fin.last M) (Fin.last M).castSucc.le_last)

end TotalBlock

end Aoyagi
end DLN
end DLNFibre
