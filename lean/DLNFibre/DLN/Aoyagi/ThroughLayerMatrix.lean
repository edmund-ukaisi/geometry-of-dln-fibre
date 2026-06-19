import DLNFibre.DLN.Aoyagi.ThroughLayerBasis
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Matrix block form from transported through-bases

This file records the elementary basis bookkeeping that turns a transported
subspace basis into a matrix block with identity top-left block and zero
lower-left block.  It does not state analytic or RLCT consequences.
-/

noncomputable section

open Matrix

namespace DLNFibre
namespace DLN
namespace Aoyagi

section SumQuotBlock

variable {K E F : Type*} [Field K]
variable [AddCommGroup E] [Module K E]
variable [AddCommGroup F] [Module K F]
variable {U : Submodule K E} {U' : Submodule K F}
variable {ι κ κ' : Type*} [Fintype ι] [Fintype κ] [Finite κ']
variable [DecidableEq ι] [DecidableEq κ]

/-- Transported subspace bases give a matrix block with identity top-left and zero lower-left. -/
theorem exists_toMatrix_sumQuot_eq_fromBlocks_one_zero
    (f : E →ₗ[K] F) (e : U ≃ₗ[K] U') (he : ∀ x : U, (e x : F) = f x)
    (bU : Module.Basis ι K U) (bQE : Module.Basis κ K (E ⧸ U))
    (bQF : Module.Basis κ' K (F ⧸ U')) :
    ∃ B : Matrix ι κ K, ∃ D : Matrix κ' κ K,
      LinearMap.toMatrix (Module.Basis.sumQuot bU bQE) (Module.Basis.sumQuot (bU.map e) bQF) f =
        fromBlocks (1 : Matrix ι ι K) B 0 D := by
  let bE : Module.Basis (ι ⊕ κ) K E := Module.Basis.sumQuot bU bQE
  let bF : Module.Basis (ι ⊕ κ') K F := Module.Basis.sumQuot (bU.map e) bQF
  let B : Matrix ι κ K := fun i j ↦ LinearMap.toMatrix bE bF f (Sum.inl i) (Sum.inr j)
  let D : Matrix κ' κ K := fun i j ↦ LinearMap.toMatrix bE bF f (Sum.inr i) (Sum.inr j)
  refine ⟨B, D, ?_⟩
  ext (i | i) (j | j)
  · have hmap : f (bU j : E) = ((bU.map e) j : F) := by
      rw [← he (bU j)]
      simp
    calc
      LinearMap.toMatrix bE bF f (Sum.inl i) (Sum.inl j)
          = bF.repr (f (bU j : E)) (Sum.inl i) := by
            rw [LinearMap.toMatrix_apply]
            simp [bE]
      _ = bF.repr ((bU.map e) j : F) (Sum.inl i) := by rw [hmap]
      _ = (Finsupp.single (Sum.inl j) (1 : K)) (Sum.inl i) := by
            change ((Module.Basis.sumQuot (bU.map e) bQF).repr ((bU.map e) j : F))
              (Sum.inl i) = _
            rw [Module.Basis.sumQuot_repr_left]
      _ = (1 : Matrix ι ι K) i j := by
            by_cases h : i = j <;> simp [Matrix.one_apply, h]
  · rfl
  · have hmem : f (bU j : E) ∈ U' := by
      rw [← he (bU j)]
      exact (e (bU j)).property
    have hq : Submodule.Quotient.mk (f (bU j : E)) = (0 : F ⧸ U') :=
      (Submodule.Quotient.mk_eq_zero (p := U')).2 hmem
    calc
      LinearMap.toMatrix bE bF f (Sum.inr i) (Sum.inl j)
          = bQF.repr (Submodule.Quotient.mk (f (bU j : E))) i := by
            rw [LinearMap.toMatrix_apply]
            simp [bE, bF]
      _ = 0 := by rw [hq]; simp
  · rfl

end SumQuotBlock

section ThroughSubspaceBlock

variable {K : Type*} [Field K] {N : ℕ}
  (V : Fin (N + 1) → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
  (A : ∀ i : Fin N, V i.castSucc →ₗ[K] V i.succ)
variable {ι κ κ' : Type*} [Fintype ι] [Fintype κ] [Finite κ']
variable [DecidableEq ι] [DecidableEq κ]

/-- A through-layer edge has matrix block form `[I B; 0 D]` in transported `sumQuot` bases. -/
theorem exists_toMatrix_throughSubspaceEdge_eq_fromBlocks_one_zero
    (U₀ : Submodule K (V 0)) (p : Fin N)
    (hU₀ : Disjoint U₀
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))))
    (bU : Module.Basis ι K (throughSubspace V A U₀ p.castSucc))
    (bQE : Module.Basis κ K (V p.castSucc ⧸ throughSubspace V A U₀ p.castSucc))
    (bQF : Module.Basis κ' K (V p.succ ⧸ throughSubspace V A U₀ p.succ)) :
    ∃ B : Matrix ι κ K, ∃ D : Matrix κ' κ K,
      LinearMap.toMatrix (Module.Basis.sumQuot bU bQE)
          (Module.Basis.sumQuot (bU.map (throughSubspaceEdgeEquiv V A U₀ p hU₀)) bQF)
          (A p) =
        fromBlocks (1 : Matrix ι ι K) B 0 D :=
  exists_toMatrix_sumQuot_eq_fromBlocks_one_zero (A p) (throughSubspaceEdgeEquiv V A U₀ p hU₀)
    (throughSubspaceEdgeEquiv_apply V A U₀ p hU₀) bU bQE bQF

end ThroughSubspaceBlock

end Aoyagi
end DLN
end DLNFibre
