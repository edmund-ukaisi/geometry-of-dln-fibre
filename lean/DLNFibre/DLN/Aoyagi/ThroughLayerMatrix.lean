import DLNFibre.DLN.Aoyagi.ProductReduction
import DLNFibre.DLN.Aoyagi.ThroughLayerBasis
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Projection

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

section DirectSumBlock

variable {K E F : Type*} [Field K]
variable [AddCommGroup E] [Module K E]
variable [AddCommGroup F] [Module K F]
variable {U W : Submodule K E} {U' W' : Submodule K F}
variable {ι κ κ' : Type*}

/-- A basis of an ambient space from bases of complementary subspaces. -/
def basisOfIsCompl (h : IsCompl U W)
    (bU : Module.Basis ι K U) (bW : Module.Basis κ K W) :
    Module.Basis (ι ⊕ κ) K E :=
  (bU.prod bW).map (Submodule.prodEquivOfIsCompl U W h)

@[simp]
theorem basisOfIsCompl_apply_inl (h : IsCompl U W)
    (bU : Module.Basis ι K U) (bW : Module.Basis κ K W) (i : ι) :
    basisOfIsCompl h bU bW (Sum.inl i) = (bU i : E) := by
  simp [basisOfIsCompl]

@[simp]
theorem basisOfIsCompl_apply_inr (h : IsCompl U W)
    (bU : Module.Basis ι K U) (bW : Module.Basis κ K W) (i : κ) :
    basisOfIsCompl h bU bW (Sum.inr i) = (bW i : E) := by
  simp [basisOfIsCompl]

variable [Fintype ι] [Fintype κ] [Finite κ']
variable [DecidableEq ι] [DecidableEq κ]

/-- Transported subspace bases and arbitrary complement bases give block form `[I B; 0 D]`. -/
theorem exists_toMatrix_basisOfIsCompl_eq_fromBlocks_one_zero
    (h : IsCompl U W) (h' : IsCompl U' W')
    (f : E →ₗ[K] F) (e : U ≃ₗ[K] U') (he : ∀ x : U, (e x : F) = f x)
    (bU : Module.Basis ι K U) (bW : Module.Basis κ K W)
    (bW' : Module.Basis κ' K W') :
    ∃ B : Matrix ι κ K, ∃ D : Matrix κ' κ K,
      LinearMap.toMatrix (basisOfIsCompl h bU bW)
          (basisOfIsCompl h' (bU.map e) bW') f =
        fromBlocks (1 : Matrix ι ι K) B 0 D := by
  let bE : Module.Basis (ι ⊕ κ) K E := basisOfIsCompl h bU bW
  let bF : Module.Basis (ι ⊕ κ') K F := basisOfIsCompl h' (bU.map e) bW'
  let B : Matrix ι κ K := fun i j ↦ LinearMap.toMatrix bE bF f (Sum.inl i) (Sum.inr j)
  let D : Matrix κ' κ K := fun i j ↦ LinearMap.toMatrix bE bF f (Sum.inr i) (Sum.inr j)
  refine ⟨B, D, ?_⟩
  ext (i | i) (j | j)
  · have hmap : f (bU j : E) = ((bU.map e) j : F) := by
      rw [← he (bU j)]
      simp
    have hbF : bF (Sum.inl j) = ((bU.map e) j : F) := by
      simp [bF]
    calc
      LinearMap.toMatrix bE bF f (Sum.inl i) (Sum.inl j)
          = bF.repr (f (bU j : E)) (Sum.inl i) := by
            rw [LinearMap.toMatrix_apply]
            simp [bE]
      _ = bF.repr ((bU.map e) j : F) (Sum.inl i) := by rw [hmap]
      _ = bF.repr (bF (Sum.inl j)) (Sum.inl i) := by rw [hbF]
      _ = (Finsupp.single (Sum.inl j) (1 : K)) (Sum.inl i) := by
            rw [Module.Basis.repr_self]
      _ = (1 : Matrix ι ι K) i j := by
            by_cases hji : i = j <;> simp [Matrix.one_apply, hji]
  · rfl
  · have hmap : f (bU j : E) = ((bU.map e) j : F) := by
      rw [← he (bU j)]
      simp
    have hbF : bF (Sum.inl j) = ((bU.map e) j : F) := by
      simp [bF]
    calc
      LinearMap.toMatrix bE bF f (Sum.inr i) (Sum.inl j)
          = bF.repr (f (bU j : E)) (Sum.inr i) := by
            rw [LinearMap.toMatrix_apply]
            simp [bE]
      _ = bF.repr ((bU.map e) j : F) (Sum.inr i) := by rw [hmap]
      _ = bF.repr (bF (Sum.inl j)) (Sum.inr i) := by rw [hbF]
      _ = (Finsupp.single (Sum.inl j) (1 : K)) (Sum.inr i) := by
            rw [Module.Basis.repr_self]
      _ = 0 := by simp
  · rfl

/-- If the complement maps to zero, transported direct-sum bases give block form `[I 0; 0 0]`. -/
theorem toMatrix_basisOfIsCompl_eq_fromBlocks_one_zero_zero_of_map_complement_eq_zero
    (h : IsCompl U W) (h' : IsCompl U' W')
    (f : E →ₗ[K] F) (e : U ≃ₗ[K] U') (he : ∀ x : U, (e x : F) = f x)
    (hWzero : ∀ x : W, f x = 0)
    (bU : Module.Basis ι K U) (bW : Module.Basis κ K W)
    (bW' : Module.Basis κ' K W') :
      LinearMap.toMatrix (basisOfIsCompl h bU bW)
          (basisOfIsCompl h' (bU.map e) bW') f =
        fromBlocks (1 : Matrix ι ι K) 0 0 0 := by
  let bE : Module.Basis (ι ⊕ κ) K E := basisOfIsCompl h bU bW
  let bF : Module.Basis (ι ⊕ κ') K F := basisOfIsCompl h' (bU.map e) bW'
  ext (i | i) (j | j)
  · have hmap : f (bU j : E) = ((bU.map e) j : F) := by
      rw [← he (bU j)]
      simp
    have hbF : bF (Sum.inl j) = ((bU.map e) j : F) := by
      simp [bF]
    calc
      LinearMap.toMatrix bE bF f (Sum.inl i) (Sum.inl j)
          = bF.repr (f (bU j : E)) (Sum.inl i) := by
            rw [LinearMap.toMatrix_apply]
            simp [bE]
      _ = bF.repr ((bU.map e) j : F) (Sum.inl i) := by rw [hmap]
      _ = bF.repr (bF (Sum.inl j)) (Sum.inl i) := by rw [hbF]
      _ = (Finsupp.single (Sum.inl j) (1 : K)) (Sum.inl i) := by
            rw [Module.Basis.repr_self]
      _ = (1 : Matrix ι ι K) i j := by
            by_cases hji : i = j <;> simp [Matrix.one_apply, hji]
  · have hzero : f (bW j : E) = 0 := hWzero (bW j)
    calc
      LinearMap.toMatrix bE bF f (Sum.inl i) (Sum.inr j)
          = bF.repr (f (bW j : E)) (Sum.inl i) := by
            rw [LinearMap.toMatrix_apply]
            simp [bE]
      _ = 0 := by rw [hzero]; simp
  · have hmap : f (bU j : E) = ((bU.map e) j : F) := by
      rw [← he (bU j)]
      simp
    have hbF : bF (Sum.inl j) = ((bU.map e) j : F) := by
      simp [bF]
    calc
      LinearMap.toMatrix bE bF f (Sum.inr i) (Sum.inl j)
          = bF.repr (f (bU j : E)) (Sum.inr i) := by
            rw [LinearMap.toMatrix_apply]
            simp [bE]
      _ = bF.repr ((bU.map e) j : F) (Sum.inr i) := by rw [hmap]
      _ = bF.repr (bF (Sum.inl j)) (Sum.inr i) := by rw [hbF]
      _ = (Finsupp.single (Sum.inl j) (1 : K)) (Sum.inr i) := by
            rw [Module.Basis.repr_self]
      _ = 0 := by simp
  · have hzero : f (bW j : E) = 0 := hWzero (bW j)
    calc
      LinearMap.toMatrix bE bF f (Sum.inr i) (Sum.inr j)
          = bF.repr (f (bW j : E)) (Sum.inr i) := by
            rw [LinearMap.toMatrix_apply]
            simp [bE]
      _ = 0 := by rw [hzero]; simp

end DirectSumBlock

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

/-- A through-layer edge has matrix block form `[I B; 0 D]` in transported direct-sum bases. -/
theorem exists_toMatrix_throughSubspaceEdge_basisOfIsCompl_eq_fromBlocks_one_zero
    (U₀ : Submodule K (V 0)) (p : Fin N)
    (hU₀ : Disjoint U₀
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))))
    {W : Submodule K (V p.castSucc)} {W' : Submodule K (V p.succ)}
    (hW : IsCompl (throughSubspace V A U₀ p.castSucc) W)
    (hW' : IsCompl (throughSubspace V A U₀ p.succ) W')
    (bU : Module.Basis ι K (throughSubspace V A U₀ p.castSucc))
    (bW : Module.Basis κ K W) (bW' : Module.Basis κ' K W') :
    ∃ B : Matrix ι κ K, ∃ D : Matrix κ' κ K,
      LinearMap.toMatrix (basisOfIsCompl hW bU bW)
          (basisOfIsCompl hW' (bU.map (throughSubspaceEdgeEquiv V A U₀ p hU₀)) bW')
          (A p) =
        fromBlocks (1 : Matrix ι ι K) B 0 D :=
  exists_toMatrix_basisOfIsCompl_eq_fromBlocks_one_zero hW hW' (A p)
    (throughSubspaceEdgeEquiv V A U₀ p hU₀)
    (throughSubspaceEdgeEquiv_apply V A U₀ p hU₀) bU bW bW'

/-- Disjointness from the total kernel implies disjointness from every prefix kernel. -/
theorem disjoint_ker_chainMap_prefix_of_disjoint_ker_total
    (U₀ : Submodule K (V 0)) (j : Fin (N + 1))
    (hU₀ : Disjoint U₀
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N))))) :
    Disjoint U₀ (LinearMap.ker (chainMap V A 0 j (Fin.zero_le j))) := by
  have hfactor : chainMap V A 0 (Fin.last N) ((Fin.zero_le j).trans j.le_last)
      = (chainMap V A j (Fin.last N) j.le_last).comp
        (chainMap V A 0 j (Fin.zero_le j)) :=
    chainMap_zero_last_eq_suffix_comp_prefix V A j
  have hcomp : Disjoint U₀
      (LinearMap.ker ((chainMap V A j (Fin.last N) j.le_last).comp
        (chainMap V A 0 j (Fin.zero_le j)))) := by
    simpa [← hfactor] using hU₀
  exact disjoint_ker_of_disjoint_ker_comp (chainMap V A 0 j (Fin.zero_le j))
    (chainMap V A j (Fin.last N) j.le_last) U₀ hcomp

/-- Prefix transport from the initial through-subspace to a later through-subspace. -/
def throughSubspacePrefixEquiv (U₀ : Submodule K (V 0)) (j : Fin (N + 1))
    (hU₀ : Disjoint U₀
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N))))) :
    U₀ ≃ₗ[K] throughSubspace V A U₀ j :=
  linearEquivMapOfDisjointKer (chainMap V A 0 j (Fin.zero_le j)) U₀
    (disjoint_ker_chainMap_prefix_of_disjoint_ker_total V A U₀ j hU₀)

/-- Prefix transport applies as the prefix chain map. -/
@[simp]
theorem throughSubspacePrefixEquiv_apply (U₀ : Submodule K (V 0)) (j : Fin (N + 1))
    (hU₀ : Disjoint U₀
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))))
    (x : U₀) :
    (throughSubspacePrefixEquiv V A U₀ j hU₀ x : V j) =
      chainMap V A 0 j (Fin.zero_le j) x :=
  linearEquivMapOfDisjointKer_apply (chainMap V A 0 j (Fin.zero_le j)) U₀
    (disjoint_ker_chainMap_prefix_of_disjoint_ker_total V A U₀ j hU₀) x

/-- Adjacent prefix-transported vectors are related by the edge map. -/
theorem throughSubspacePrefixEquiv_succ_apply (U₀ : Submodule K (V 0)) (p : Fin N)
    (hU₀ : Disjoint U₀
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))))
    (x : U₀) :
    (throughSubspacePrefixEquiv V A U₀ p.succ hU₀ x : V p.succ) =
      A p (throughSubspacePrefixEquiv V A U₀ p.castSucc hU₀ x) := by
  rw [throughSubspacePrefixEquiv_apply, throughSubspacePrefixEquiv_apply,
    chainMap_succ V A 0 p (Fin.zero_le p.castSucc)]
  rfl

/-- A through-layer edge has block form `[I B; 0 D]` using prefix-transported bases. -/
theorem exists_toMatrix_throughSubspaceEdge_prefix_basisOfIsCompl_eq_fromBlocks_one_zero
    (U₀ : Submodule K (V 0)) (p : Fin N)
    (hU₀ : Disjoint U₀
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))))
    {W : Submodule K (V p.castSucc)} {W' : Submodule K (V p.succ)}
    (hW : IsCompl (throughSubspace V A U₀ p.castSucc) W)
    (hW' : IsCompl (throughSubspace V A U₀ p.succ) W')
    (bU₀ : Module.Basis ι K U₀)
    (bW : Module.Basis κ K W) (bW' : Module.Basis κ' K W') :
    ∃ B : Matrix ι κ K, ∃ D : Matrix κ' κ K,
      LinearMap.toMatrix
          (basisOfIsCompl hW
            (bU₀.map (throughSubspacePrefixEquiv V A U₀ p.castSucc hU₀)) bW)
          (basisOfIsCompl hW'
            (bU₀.map (throughSubspacePrefixEquiv V A U₀ p.succ hU₀)) bW')
          (A p) =
        fromBlocks (1 : Matrix ι ι K) B 0 D := by
  let eSrc := throughSubspacePrefixEquiv V A U₀ p.castSucc hU₀
  let eTgt := throughSubspacePrefixEquiv V A U₀ p.succ hU₀
  let eEdge : throughSubspace V A U₀ p.castSucc ≃ₗ[K] throughSubspace V A U₀ p.succ :=
    eSrc.symm.trans eTgt
  have he : ∀ x : throughSubspace V A U₀ p.castSucc, (eEdge x : V p.succ) = A p x := by
    intro x
    change (eTgt (eSrc.symm x) : V p.succ) = A p x
    rw [throughSubspacePrefixEquiv_succ_apply V A U₀ p hU₀ (eSrc.symm x)]
    simp [eSrc]
  have hbasis : (bU₀.map eSrc).map eEdge = bU₀.map eTgt := by
    ext i
    simp [eSrc, eTgt, eEdge]
  simpa [eSrc, eTgt, eEdge, hbasis] using
    (exists_toMatrix_basisOfIsCompl_eq_fromBlocks_one_zero hW hW' (A p) eEdge he
      (bU₀.map eSrc) bW bW')

/-- Complement and basis choices for every layer around a fixed through-subspace chain. -/
structure ThroughSubspaceChartData (U₀ : Submodule K (V 0))
    (ι : Type*) (κ : Fin (N + 1) → Type*) where
  W : ∀ j : Fin (N + 1), Submodule K (V j)
  hW : ∀ j : Fin (N + 1), IsCompl (throughSubspace V A U₀ j) (W j)
  bU₀ : Module.Basis ι K U₀
  bW : ∀ j : Fin (N + 1), Module.Basis (κ j) K (W j)

/-- The adapted ambient basis at one vertex from supplied through-subspace chart data. -/
def throughSubspaceAdaptedBasis
    {κ : Fin (N + 1) → Type*}
    (U₀ : Submodule K (V 0))
    (hU₀ : Disjoint U₀
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))))
    (data : ThroughSubspaceChartData V A U₀ ι κ) (j : Fin (N + 1)) :
    Module.Basis (ι ⊕ κ j) K (V j) :=
  basisOfIsCompl (data.hW j)
    (data.bU₀.map (throughSubspacePrefixEquiv V A U₀ j hU₀))
    (data.bW j)

/-- The matrix of a chain segment in supplied adapted bases. -/
def throughSubspaceAdaptedChainMapMatrix
    {κ : Fin (N + 1) → Type*} [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (U₀ : Submodule K (V 0))
    (hU₀ : Disjoint U₀
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))))
    (data : ThroughSubspaceChartData V A U₀ ι κ)
    (i j : Fin (N + 1)) (hij : i ≤ j) :
    Matrix (ι ⊕ κ j) (ι ⊕ κ i) K :=
  LinearMap.toMatrix
    (throughSubspaceAdaptedBasis V A U₀ hU₀ data i)
    (throughSubspaceAdaptedBasis V A U₀ hU₀ data j)
    (chainMap V A i j hij)

/-- The matrix of one edge in supplied adapted bases. -/
def throughSubspaceAdaptedEdgeMatrix
    {κ : Fin (N + 1) → Type*} [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (U₀ : Submodule K (V 0))
    (hU₀ : Disjoint U₀
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))))
    (data : ThroughSubspaceChartData V A U₀ ι κ) (p : Fin N) :
    Matrix (ι ⊕ κ p.succ) (ι ⊕ κ p.castSucc) K :=
  LinearMap.toMatrix
    (throughSubspaceAdaptedBasis V A U₀ hU₀ data p.castSucc)
    (throughSubspaceAdaptedBasis V A U₀ hU₀ data p.succ)
    (A p)

set_option linter.unusedDecidableInType false in
/-- Extending a chain segment by one edge multiplies edge matrix by prefix matrix. -/
theorem throughSubspaceAdaptedChainMapMatrix_succ
    {κ : Fin (N + 1) → Type*} [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (U₀ : Submodule K (V 0))
    (hU₀ : Disjoint U₀
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))))
    (data : ThroughSubspaceChartData V A U₀ ι κ)
    (i : Fin (N + 1)) (p : Fin N) (hip : i ≤ p.castSucc) :
    throughSubspaceAdaptedChainMapMatrix V A U₀ hU₀ data i p.succ
        (hip.trans (Fin.castSucc_le_succ p)) =
      throughSubspaceAdaptedEdgeMatrix V A U₀ hU₀ data p *
        throughSubspaceAdaptedChainMapMatrix V A U₀ hU₀ data i p.castSucc hip := by
  classical
  rw [throughSubspaceAdaptedChainMapMatrix, throughSubspaceAdaptedEdgeMatrix,
    chainMap_succ V A i p hip]
  exact LinearMap.toMatrix_comp
    (throughSubspaceAdaptedBasis V A U₀ hU₀ data i)
    (throughSubspaceAdaptedBasis V A U₀ hU₀ data p.castSucc)
    (throughSubspaceAdaptedBasis V A U₀ hU₀ data p.succ)
    (A p) (chainMap V A i p.castSucc hip)

set_option linter.unusedDecidableInType false in
/-- Splitting a chain segment after one edge multiplies suffix matrix by edge matrix. -/
theorem throughSubspaceAdaptedChainMapMatrix_succ_right
    {κ : Fin (N + 1) → Type*} [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (U₀ : Submodule K (V 0))
    (hU₀ : Disjoint U₀
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))))
    (data : ThroughSubspaceChartData V A U₀ ι κ)
    (p : Fin N) (j : Fin (N + 1)) (hpj : p.succ ≤ j) :
    throughSubspaceAdaptedChainMapMatrix V A U₀ hU₀ data p.castSucc j
        ((Fin.castSucc_le_succ p).trans hpj) =
      throughSubspaceAdaptedChainMapMatrix V A U₀ hU₀ data p.succ j hpj *
        throughSubspaceAdaptedEdgeMatrix V A U₀ hU₀ data p := by
  classical
  rw [throughSubspaceAdaptedChainMapMatrix, throughSubspaceAdaptedEdgeMatrix,
    chainMap_trans V A p.castSucc (Fin.castSucc_le_succ p) hpj,
    chainMap_edge V A p (Fin.castSucc_le_succ p)]
  exact LinearMap.toMatrix_comp
    (throughSubspaceAdaptedBasis V A U₀ hU₀ data p.castSucc)
    (throughSubspaceAdaptedBasis V A U₀ hU₀ data p.succ)
    (throughSubspaceAdaptedBasis V A U₀ hU₀ data j)
    (chainMap V A p.succ j hpj) (A p)

/-- The left-multiply step for the dependent product of adapted edge matrices. -/
private def throughSubspaceAdaptedEdgeProductStep
    {κ : Fin (N + 1) → Type*} [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (U₀ : Submodule K (V 0))
    (hU₀ : Disjoint U₀
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))))
    (data : ThroughSubspaceChartData V A U₀ ι κ) (i : Fin (N + 1)) :
    ⦃m : ℕ⦄ → (i ≤ m) →
      ((hm : m < N + 1) → Matrix (ι ⊕ κ ⟨m, hm⟩) (ι ⊕ κ i) K) →
        ((hm : m + 1 < N + 1) → Matrix (ι ⊕ κ ⟨m + 1, hm⟩) (ι ⊕ κ i) K) :=
  fun {m} _ rec hm ↦
    let p : Fin N := ⟨m, Nat.lt_of_succ_lt_succ hm⟩
    show Matrix (ι ⊕ κ p.succ) (ι ⊕ κ i) K from
      throughSubspaceAdaptedEdgeMatrix V A U₀ hU₀ data p *
        (show Matrix (ι ⊕ κ p.castSucc) (ι ⊕ κ i) K from rec p.castSucc.isLt)

/-- The dependent product of adapted edge matrices from `i` to `j`. -/
def throughSubspaceAdaptedEdgeProductMatrix
    {κ : Fin (N + 1) → Type*} [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (U₀ : Submodule K (V 0))
    (hU₀ : Disjoint U₀
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))))
    (data : ThroughSubspaceChartData V A U₀ ι κ)
    (i j : Fin (N + 1)) (hij : i ≤ j) :
    Matrix (ι ⊕ κ j) (ι ⊕ κ i) K :=
  Nat.leRec (motive := fun m _ ↦
      (hm : m < N + 1) → Matrix (ι ⊕ κ ⟨m, hm⟩) (ι ⊕ κ i) K)
    (fun _ ↦ 1) (throughSubspaceAdaptedEdgeProductStep V A U₀ hU₀ data i) hij j.isLt

/-- The empty adapted edge product is the identity matrix. -/
theorem throughSubspaceAdaptedEdgeProductMatrix_self
    {κ : Fin (N + 1) → Type*} [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (U₀ : Submodule K (V 0))
    (hU₀ : Disjoint U₀
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))))
    (data : ThroughSubspaceChartData V A U₀ ι κ) (i : Fin (N + 1)) :
    throughSubspaceAdaptedEdgeProductMatrix V A U₀ hU₀ data i i le_rfl = 1 := by
  unfold throughSubspaceAdaptedEdgeProductMatrix
  exact congrFun (Nat.leRec_self (motive := fun m _ ↦ (hm : m < N + 1) →
    Matrix (ι ⊕ κ ⟨m, hm⟩) (ι ⊕ κ i) K) (fun _ ↦ 1)
    (throughSubspaceAdaptedEdgeProductStep V A U₀ hU₀ data i)) i.isLt

/-- Extending the adapted edge product prepends the next adapted edge matrix. -/
theorem throughSubspaceAdaptedEdgeProductMatrix_succ
    {κ : Fin (N + 1) → Type*} [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (U₀ : Submodule K (V 0))
    (hU₀ : Disjoint U₀
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))))
    (data : ThroughSubspaceChartData V A U₀ ι κ)
    (i : Fin (N + 1)) (p : Fin N) (hip : i ≤ p.castSucc) :
    throughSubspaceAdaptedEdgeProductMatrix V A U₀ hU₀ data i p.succ
        (hip.trans (Fin.castSucc_le_succ p)) =
      throughSubspaceAdaptedEdgeMatrix V A U₀ hU₀ data p *
        throughSubspaceAdaptedEdgeProductMatrix V A U₀ hU₀ data i p.castSucc hip := by
  unfold throughSubspaceAdaptedEdgeProductMatrix
  exact congrFun (Nat.leRec_succ (h1 := Fin.val_fin_le.mpr hip)
    (h2 := Fin.val_fin_le.mpr (hip.trans (Fin.castSucc_le_succ p)))
    (refl := fun _ ↦ 1)
    (le_succ_of_le := throughSubspaceAdaptedEdgeProductStep V A U₀ hU₀ data i)) p.succ.isLt

set_option linter.unusedDecidableInType false in
/-- The adapted edge product is the matrix of the corresponding chain map. -/
theorem throughSubspaceAdaptedChainMapMatrix_eq_edgeProductMatrix
    {κ : Fin (N + 1) → Type*} [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (U₀ : Submodule K (V 0))
    (hU₀ : Disjoint U₀
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))))
    (data : ThroughSubspaceChartData V A U₀ ι κ)
    (i j : Fin (N + 1)) (hij : i ≤ j) :
    throughSubspaceAdaptedChainMapMatrix V A U₀ hU₀ data i j hij =
      throughSubspaceAdaptedEdgeProductMatrix V A U₀ hU₀ data i j hij := by
  induction j using Fin.induction with
  | zero =>
      have hi : i = 0 := Fin.le_zero_iff.mp hij
      subst i
      rw [throughSubspaceAdaptedChainMapMatrix, chainMap_self, LinearMap.toMatrix_id,
        throughSubspaceAdaptedEdgeProductMatrix_self]
  | succ p ih =>
      rcases eq_or_lt_of_le hij with hEq | hlt
      · subst i
        rw [throughSubspaceAdaptedChainMapMatrix, chainMap_self, LinearMap.toMatrix_id,
          throughSubspaceAdaptedEdgeProductMatrix_self]
      · have hip : i ≤ p.castSucc := by
          rw [Fin.le_castSucc_iff]
          exact hlt
        rw [throughSubspaceAdaptedChainMapMatrix_succ V A U₀ hU₀ data i p hip,
          throughSubspaceAdaptedEdgeProductMatrix_succ V A U₀ hU₀ data i p hip, ih hip]

set_option linter.unusedDecidableInType false in
/-- The prefix adapted chain-map matrix is the corresponding adapted edge product. -/
theorem throughSubspaceAdaptedChainMapMatrix_zero_eq_edgeProductMatrix
    {κ : Fin (N + 1) → Type*} [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (U₀ : Submodule K (V 0))
    (hU₀ : Disjoint U₀
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))))
    (data : ThroughSubspaceChartData V A U₀ ι κ) (j : Fin (N + 1)) :
    throughSubspaceAdaptedChainMapMatrix V A U₀ hU₀ data 0 j (Fin.zero_le j) =
      throughSubspaceAdaptedEdgeProductMatrix V A U₀ hU₀ data 0 j (Fin.zero_le j) :=
  throughSubspaceAdaptedChainMapMatrix_eq_edgeProductMatrix V A U₀ hU₀ data 0 j (Fin.zero_le j)

set_option linter.unusedDecidableInType false in
/-- The total chain-map matrix is the adapted product of all edge matrices. -/
theorem toMatrix_chainMap_zero_last_eq_adaptedEdgeProductMatrix
    {κ : Fin (N + 1) → Type*} [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (U₀ : Submodule K (V 0))
    (hU₀ : Disjoint U₀
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))))
    (data : ThroughSubspaceChartData V A U₀ ι κ) :
    LinearMap.toMatrix
        (throughSubspaceAdaptedBasis V A U₀ hU₀ data 0)
        (throughSubspaceAdaptedBasis V A U₀ hU₀ data (Fin.last N))
        (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N))) =
      throughSubspaceAdaptedEdgeProductMatrix V A U₀ hU₀ data
        0 (Fin.last N) (Fin.zero_le (Fin.last N)) := by
  simpa [throughSubspaceAdaptedChainMapMatrix] using
    (throughSubspaceAdaptedChainMapMatrix_zero_eq_edgeProductMatrix
      V A U₀ hU₀ data (Fin.last N))

/-- A supplied-data edge block form stated using the named adapted basis family. -/
theorem exists_toMatrix_throughSubspaceEdge_adaptedBasis_eq_fromBlocks_one_zero
    {κ : Fin (N + 1) → Type*} [∀ j, Fintype (κ j)]
    [∀ j, DecidableEq (κ j)]
    (U₀ : Submodule K (V 0))
    (hU₀ : Disjoint U₀
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))))
    (data : ThroughSubspaceChartData V A U₀ ι κ) (p : Fin N) :
    ∃ B : Matrix ι (κ p.castSucc) K, ∃ D : Matrix (κ p.succ) (κ p.castSucc) K,
      LinearMap.toMatrix
          (throughSubspaceAdaptedBasis V A U₀ hU₀ data p.castSucc)
          (throughSubspaceAdaptedBasis V A U₀ hU₀ data p.succ)
          (A p) =
        fromBlocks (1 : Matrix ι ι K) B 0 D := by
  simpa [throughSubspaceAdaptedBasis] using
    exists_toMatrix_throughSubspaceEdge_prefix_basisOfIsCompl_eq_fromBlocks_one_zero
      V A U₀ p hU₀ (data.hW p.castSucc) (data.hW p.succ) data.bU₀
      (data.bW p.castSucc) (data.bW p.succ)

/-- A bundled chart-data version of the prefix-compatible edge block form. -/
theorem exists_toMatrix_throughSubspaceEdge_chartData_eq_fromBlocks_one_zero
    {κ : Fin (N + 1) → Type*} [∀ j, Fintype (κ j)]
    [∀ j, DecidableEq (κ j)]
    (U₀ : Submodule K (V 0))
    (hU₀ : Disjoint U₀
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))))
    (data : ThroughSubspaceChartData V A U₀ ι κ) (p : Fin N) :
    ∃ B : Matrix ι (κ p.castSucc) K, ∃ D : Matrix (κ p.succ) (κ p.castSucc) K,
      LinearMap.toMatrix
          (basisOfIsCompl (data.hW p.castSucc)
            (data.bU₀.map (throughSubspacePrefixEquiv V A U₀ p.castSucc hU₀))
            (data.bW p.castSucc))
          (basisOfIsCompl (data.hW p.succ)
            (data.bU₀.map (throughSubspacePrefixEquiv V A U₀ p.succ hU₀))
            (data.bW p.succ))
          (A p) =
        fromBlocks (1 : Matrix ι ι K) B 0 D :=
  exists_toMatrix_throughSubspaceEdge_prefix_basisOfIsCompl_eq_fromBlocks_one_zero V A U₀ p hU₀
    (data.hW p.castSucc) (data.hW p.succ) data.bU₀ (data.bW p.castSucc) (data.bW p.succ)

/-- A supplied-data endpoint theorem using the same adapted basis family as the edge blocks. -/
theorem toMatrix_chainMap_zero_last_chartData_eq_fromBlocks_one_zero_zero_of_maps_complement_to_zero
    {κ : Fin (N + 1) → Type*} [Fintype (κ 0)] [Finite (κ (Fin.last N))]
    [DecidableEq (κ 0)]
    (U₀ : Submodule K (V 0))
    (hU₀ : Disjoint U₀
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))))
    (data : ThroughSubspaceChartData V A U₀ ι κ)
    (hWzero : ∀ x : data.W 0,
      chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)) x = 0) :
      LinearMap.toMatrix
          (throughSubspaceAdaptedBasis V A U₀ hU₀ data 0)
          (throughSubspaceAdaptedBasis V A U₀ hU₀ data (Fin.last N))
          (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N))) =
        fromBlocks (1 : Matrix ι ι K) 0 0 0 := by
  let e₀ := throughSubspacePrefixEquiv V A U₀ 0 hU₀
  let eLast := throughSubspacePrefixEquiv V A U₀ (Fin.last N) hU₀
  let eTotal : throughSubspace V A U₀ 0 ≃ₗ[K] throughSubspace V A U₀ (Fin.last N) :=
    e₀.symm.trans eLast
  have heTotal : ∀ x : throughSubspace V A U₀ 0,
      (eTotal x : V (Fin.last N)) =
        chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)) x := by
    intro x
    change (eLast (e₀.symm x) : V (Fin.last N)) =
      chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)) x
    rw [throughSubspacePrefixEquiv_apply V A U₀ (Fin.last N) hU₀ (e₀.symm x)]
    have hx₀ : ((e₀.symm x : U₀) : V 0) = (x : V 0) := by
      have happly : (e₀ (e₀.symm x) : V 0) = (x : V 0) :=
        congrArg (fun y : throughSubspace V A U₀ 0 ↦ (y : V 0))
          (e₀.apply_symm_apply x)
      have hleft : (e₀ (e₀.symm x) : V 0) = ((e₀.symm x : U₀) : V 0) := by
        simpa [e₀] using
          throughSubspacePrefixEquiv_apply V A U₀ 0 hU₀ (e₀.symm x)
      exact hleft.symm.trans happly
    rw [hx₀]
  have hbasis : (data.bU₀.map e₀).map eTotal = data.bU₀.map eLast := by
    ext i
    simp [e₀, eLast, eTotal]
  simpa [throughSubspaceAdaptedBasis, e₀, eLast, eTotal, hbasis] using
    (toMatrix_basisOfIsCompl_eq_fromBlocks_one_zero_zero_of_map_complement_eq_zero
      (data.hW 0) (data.hW (Fin.last N))
      (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N))) eTotal heTotal
      hWzero (data.bU₀.map e₀) (data.bW 0) (data.bW (Fin.last N)))

/-- Bundled chart data stays in the identity-corner chart after a unitriangular multiplier. -/
theorem exists_unitriangular_toMatrix_throughSubspaceEdge_chartData_eq_fromBlocks_one_zero
    {κ : Fin (N + 1) → Type*} [∀ j, Fintype (κ j)]
    [∀ j, DecidableEq (κ j)]
    (U₀ : Submodule K (V 0))
    (hU₀ : Disjoint U₀
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))))
    (data : ThroughSubspaceChartData V A U₀ ι κ) (p : Fin N)
    (F : Matrix ι (κ p.succ) K) :
    ∃ B' : Matrix ι (κ p.castSucc) K, ∃ D' : Matrix (κ p.succ) (κ p.castSucc) K,
      fromBlocks (1 : Matrix ι ι K) (-F) 0 1 *
          LinearMap.toMatrix
            (basisOfIsCompl (data.hW p.castSucc)
              (data.bU₀.map (throughSubspacePrefixEquiv V A U₀ p.castSucc hU₀))
              (data.bW p.castSucc))
            (basisOfIsCompl (data.hW p.succ)
              (data.bU₀.map (throughSubspacePrefixEquiv V A U₀ p.succ hU₀))
              (data.bW p.succ))
            (A p) =
        fromBlocks (1 : Matrix ι ι K) B' 0 D' :=
  exists_fromBlocks_one_zero_of_upperUnitriangular_mul_indexed F _
    (exists_toMatrix_throughSubspaceEdge_chartData_eq_fromBlocks_one_zero V A U₀ hU₀ data p)

/-- The total chain map has block form `[I 0; 0 0]` when the source complement is its kernel. -/
theorem toMatrix_chainMap_zero_last_ker_basisOfIsCompl_eq_fromBlocks_one_zero_zero
    (U₀ : Submodule K (V 0))
    (hU₀ : IsCompl U₀
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))))
    {Wlast : Submodule K (V (Fin.last N))}
    (hWlast : IsCompl (throughSubspace V A U₀ (Fin.last N)) Wlast)
    (bU₀ : Module.Basis ι K U₀)
    (bKer : Module.Basis κ K
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))))
    (bWlast : Module.Basis κ' K Wlast) :
      LinearMap.toMatrix (basisOfIsCompl hU₀ bU₀ bKer)
          (basisOfIsCompl hWlast
            (bU₀.map (linearEquivMapOfDisjointKer
              (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N))) U₀ hU₀.disjoint))
            bWlast)
          (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N))) =
        fromBlocks (1 : Matrix ι ι K) 0 0 0 := by
  refine toMatrix_basisOfIsCompl_eq_fromBlocks_one_zero_zero_of_map_complement_eq_zero
    hU₀ hWlast
    (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))
    (linearEquivMapOfDisjointKer
      (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N))) U₀ hU₀.disjoint)
    ?_ ?_ bU₀ bKer bWlast
  · intro x
    exact linearEquivMapOfDisjointKer_apply
      (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N))) U₀ hU₀.disjoint x
  · intro x
    exact LinearMap.mem_ker.mp x.property

end ThroughSubspaceBlock

section FiniteChartData

universe u v

variable {K : Type u} [Field K] {N : ℕ}
  (V : Fin (N + 1) → Type v) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
  (A : ∀ i : Fin N, V i.castSucc →ₗ[K] V i.succ)

/-- A chosen complement to a through-subspace at one layer. -/
def throughSubspaceComplement (U₀ : Submodule K (V 0)) (j : Fin (N + 1)) :
    Submodule K (V j) :=
  Classical.choose (Submodule.exists_isCompl (throughSubspace V A U₀ j))

/-- The chosen through-subspace complement is complementary to the through-subspace. -/
theorem throughSubspace_isCompl_complement (U₀ : Submodule K (V 0)) (j : Fin (N + 1)) :
    IsCompl (throughSubspace V A U₀ j) (throughSubspaceComplement V A U₀ j) :=
  Classical.choose_spec (Submodule.exists_isCompl (throughSubspace V A U₀ j))

/-- The finite index family for the chosen complements. -/
abbrev throughSubspaceComplementIndex
    (A : ∀ i : Fin N, V i.castSucc →ₗ[K] V i.succ)
    (U₀ : Submodule K (V 0)) : Fin (N + 1) → Type :=
  fun j ↦ Fin (Module.finrank K (throughSubspaceComplement V A U₀ j))

/-- The chosen finite-dimensional chart data for a through-subspace chain. -/
def throughSubspaceChartDataOfFiniteDimensional
    [∀ j, FiniteDimensional K (V j)] (U₀ : Submodule K (V 0)) :
    ThroughSubspaceChartData V A U₀
      (Fin (Module.finrank K U₀)) (throughSubspaceComplementIndex V A U₀) :=
  { W := throughSubspaceComplement V A U₀
    hW := throughSubspace_isCompl_complement V A U₀
    bU₀ := Module.finBasis K U₀
    bW := fun j ↦ Module.finBasis K (throughSubspaceComplement V A U₀ j) }

/-- Complements chosen as the total kernel at the source and arbitrary complements elsewhere. -/
def throughSubspaceEndpointComplement (U₀ : Submodule K (V 0)) (j : Fin (N + 1)) :
    Submodule K (V j) :=
  if h : j = 0 then
    by
      subst j
      exact LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))
  else
    throughSubspaceComplement V A U₀ j

/-- The endpoint-compatible complement family complements the through-subspaces. -/
theorem throughSubspace_isCompl_endpointComplement
    (U₀ : Submodule K (V 0))
    (hU₀ : IsCompl U₀
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))))
    (j : Fin (N + 1)) :
    IsCompl (throughSubspace V A U₀ j) (throughSubspaceEndpointComplement V A U₀ j) := by
  by_cases h : j = 0
  · subst j
    simpa [throughSubspaceEndpointComplement, throughSubspace_zero] using hU₀
  · simp [throughSubspaceEndpointComplement, h, throughSubspace_isCompl_complement V A U₀ j]

/-- The finite index family for endpoint-compatible complements. -/
abbrev throughSubspaceEndpointComplementIndex
    (A : ∀ i : Fin N, V i.castSucc →ₗ[K] V i.succ)
    (U₀ : Submodule K (V 0)) : Fin (N + 1) → Type :=
  fun j ↦ Fin (Module.finrank K (throughSubspaceEndpointComplement V A U₀ j))

/-- Finite-dimensional endpoint-compatible chart data. -/
def throughSubspaceEndpointChartDataOfFiniteDimensional
    [∀ j, FiniteDimensional K (V j)]
    (U₀ : Submodule K (V 0))
    (hU₀ : IsCompl U₀
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N))))) :
    ThroughSubspaceChartData V A U₀
      (Fin (Module.finrank K U₀)) (throughSubspaceEndpointComplementIndex V A U₀) :=
  { W := throughSubspaceEndpointComplement V A U₀
    hW := throughSubspace_isCompl_endpointComplement V A U₀ hU₀
    bU₀ := Module.finBasis K U₀
    bW := fun j ↦ Module.finBasis K (throughSubspaceEndpointComplement V A U₀ j) }

/-- The source complement in endpoint-compatible chart data maps to zero under the total product. -/
theorem maps_endpointComplement_zero
    (U₀ : Submodule K (V 0)) :
    ∀ x : throughSubspaceEndpointComplement V A U₀ 0,
      chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)) x = 0 := by
  intro x
  exact LinearMap.mem_ker.mp x.property

/-- Finite-dimensional layers supply finite-indexed through-subspace chart data. -/
theorem nonempty_throughSubspaceChartDataOfFiniteDimensional
    [∀ j, FiniteDimensional K (V j)] (U₀ : Submodule K (V 0)) :
    Nonempty (ThroughSubspaceChartData V A U₀
      (Fin (Module.finrank K U₀)) (throughSubspaceComplementIndex V A U₀)) :=
  ⟨throughSubspaceChartDataOfFiniteDimensional V A U₀⟩

/-- Finite-dimensional layers supply endpoint-compatible chart data. -/
theorem nonempty_throughSubspaceEndpointChartDataOfFiniteDimensional
    [∀ j, FiniteDimensional K (V j)]
    (U₀ : Submodule K (V 0))
    (hU₀ : IsCompl U₀
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N))))) :
    Nonempty (ThroughSubspaceChartData V A U₀
      (Fin (Module.finrank K U₀)) (throughSubspaceEndpointComplementIndex V A U₀)) :=
  ⟨throughSubspaceEndpointChartDataOfFiniteDimensional V A U₀ hU₀⟩

/-- Finite-dimensional layers supply a kernel complement with endpoint-compatible chart data. -/
theorem exists_isCompl_ker_throughSubspaceEndpointChartDataOfFiniteDimensional
    [∀ j, FiniteDimensional K (V j)] :
    ∃ U₀ : Submodule K (V 0),
      IsCompl U₀
          (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))) ∧
        Module.finrank K U₀ =
          Module.finrank K
            (LinearMap.range
              (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))) ∧
          Nonempty (ThroughSubspaceChartData V A U₀
            (Fin (Module.finrank K U₀)) (throughSubspaceEndpointComplementIndex V A U₀)) := by
  let P : V 0 →ₗ[K] V (Fin.last N) :=
    chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N))
  rcases exists_isCompl_ker_and_finrank_eq_range (P := P) with ⟨U₀, hU₀, hfinU₀⟩
  exact ⟨U₀, by simpa [P] using hU₀, by simpa [P] using hfinU₀,
    nonempty_throughSubspaceEndpointChartDataOfFiniteDimensional V A U₀
      (by simpa [P] using hU₀)⟩

/-- Endpoint-compatible finite chart data gives the total-product block form. -/
theorem toMatrix_chainMap_zero_last_endpointChartData_eq_fromBlocks_one_zero_zero
    [∀ j, FiniteDimensional K (V j)]
    (U₀ : Submodule K (V 0))
    (hU₀ : IsCompl U₀
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N))))) :
      LinearMap.toMatrix
          (throughSubspaceAdaptedBasis V A U₀ hU₀.disjoint
            (throughSubspaceEndpointChartDataOfFiniteDimensional V A U₀ hU₀) 0)
          (throughSubspaceAdaptedBasis V A U₀ hU₀.disjoint
            (throughSubspaceEndpointChartDataOfFiniteDimensional V A U₀ hU₀) (Fin.last N))
          (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N))) =
        fromBlocks (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
          (0 : Matrix (Fin (Module.finrank K U₀))
            (throughSubspaceEndpointComplementIndex V A U₀ 0) K)
          (0 : Matrix (throughSubspaceEndpointComplementIndex V A U₀ (Fin.last N))
            (Fin (Module.finrank K U₀)) K)
          (0 : Matrix (throughSubspaceEndpointComplementIndex V A U₀ (Fin.last N))
            (throughSubspaceEndpointComplementIndex V A U₀ 0) K) :=
  toMatrix_chainMap_zero_last_chartData_eq_fromBlocks_one_zero_zero_of_maps_complement_to_zero
    V A U₀ hU₀.disjoint (throughSubspaceEndpointChartDataOfFiniteDimensional V A U₀ hU₀)
    (maps_endpointComplement_zero V A U₀)

/-- Endpoint-compatible data gives one edge block and the total-product block in shared bases. -/
theorem endpointChartData_edge_and_totalProduct_blocks
    [∀ j, FiniteDimensional K (V j)]
    (U₀ : Submodule K (V 0))
    (hU₀ : IsCompl U₀
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))))
    (p : Fin N) :
    let data := throughSubspaceEndpointChartDataOfFiniteDimensional V A U₀ hU₀
    (∃ B : Matrix (Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex V A U₀ p.castSucc) K,
      ∃ D : Matrix
          (throughSubspaceEndpointComplementIndex V A U₀ p.succ)
          (throughSubspaceEndpointComplementIndex V A U₀ p.castSucc) K,
        LinearMap.toMatrix
            (throughSubspaceAdaptedBasis V A U₀ hU₀.disjoint data p.castSucc)
            (throughSubspaceAdaptedBasis V A U₀ hU₀.disjoint data p.succ)
            (A p) =
          fromBlocks (1 : Matrix (Fin (Module.finrank K U₀))
            (Fin (Module.finrank K U₀)) K) B 0 D) ∧
      LinearMap.toMatrix
          (throughSubspaceAdaptedBasis V A U₀ hU₀.disjoint data 0)
          (throughSubspaceAdaptedBasis V A U₀ hU₀.disjoint data (Fin.last N))
          (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N))) =
        fromBlocks (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
          (0 : Matrix (Fin (Module.finrank K U₀))
            (throughSubspaceEndpointComplementIndex V A U₀ 0) K)
          (0 : Matrix (throughSubspaceEndpointComplementIndex V A U₀ (Fin.last N))
            (Fin (Module.finrank K U₀)) K)
          (0 : Matrix (throughSubspaceEndpointComplementIndex V A U₀ (Fin.last N))
            (throughSubspaceEndpointComplementIndex V A U₀ 0) K) := by
  dsimp
  constructor
  · exact exists_toMatrix_throughSubspaceEdge_adaptedBasis_eq_fromBlocks_one_zero
      V A U₀ hU₀.disjoint (throughSubspaceEndpointChartDataOfFiniteDimensional V A U₀ hU₀) p
  · exact toMatrix_chainMap_zero_last_endpointChartData_eq_fromBlocks_one_zero_zero
      V A U₀ hU₀

/-- A finite-dimensional through-layer edge has concrete adapted-basis block form `[I B; 0 D]`. -/
theorem exists_toMatrix_throughSubspaceEdge_finiteDimensional_eq_fromBlocks_one_zero
    [∀ j, FiniteDimensional K (V j)]
    (U₀ : Submodule K (V 0))
    (hU₀ : Disjoint U₀
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))))
    (p : Fin N) :
    ∃ B : Matrix (Fin (Module.finrank K U₀))
        (throughSubspaceComplementIndex V A U₀ p.castSucc) K,
      ∃ D : Matrix (throughSubspaceComplementIndex V A U₀ p.succ)
          (throughSubspaceComplementIndex V A U₀ p.castSucc) K,
        LinearMap.toMatrix
            (basisOfIsCompl
              (throughSubspace_isCompl_complement V A U₀ p.castSucc)
              ((Module.finBasis K U₀).map
                (throughSubspacePrefixEquiv V A U₀ p.castSucc hU₀))
              (Module.finBasis K (throughSubspaceComplement V A U₀ p.castSucc)))
            (basisOfIsCompl
              (throughSubspace_isCompl_complement V A U₀ p.succ)
              ((Module.finBasis K U₀).map
                (throughSubspacePrefixEquiv V A U₀ p.succ hU₀))
              (Module.finBasis K (throughSubspaceComplement V A U₀ p.succ)))
            (A p) =
          fromBlocks (1 : Matrix (Fin (Module.finrank K U₀))
            (Fin (Module.finrank K U₀)) K) B 0 D := by
  simpa [throughSubspaceChartDataOfFiniteDimensional] using
    (exists_toMatrix_throughSubspaceEdge_chartData_eq_fromBlocks_one_zero V A U₀ hU₀
      (throughSubspaceChartDataOfFiniteDimensional V A U₀) p)

/-- Concrete finite-dimensional adapted-basis edge form survives a unitriangular multiplier. -/
theorem exists_unitriangular_toMatrix_throughSubspaceEdge_finiteDimensional_eq_fromBlocks_one_zero
    [∀ j, FiniteDimensional K (V j)]
    (U₀ : Submodule K (V 0))
    (hU₀ : Disjoint U₀
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))))
    (p : Fin N)
    (F : Matrix (Fin (Module.finrank K U₀))
        (throughSubspaceComplementIndex V A U₀ p.succ) K) :
    ∃ B' : Matrix (Fin (Module.finrank K U₀))
        (throughSubspaceComplementIndex V A U₀ p.castSucc) K,
      ∃ D' : Matrix (throughSubspaceComplementIndex V A U₀ p.succ)
          (throughSubspaceComplementIndex V A U₀ p.castSucc) K,
        fromBlocks (1 : Matrix (Fin (Module.finrank K U₀))
            (Fin (Module.finrank K U₀)) K) (-F) 0 1 *
          LinearMap.toMatrix
            (basisOfIsCompl
              (throughSubspace_isCompl_complement V A U₀ p.castSucc)
              ((Module.finBasis K U₀).map
                (throughSubspacePrefixEquiv V A U₀ p.castSucc hU₀))
              (Module.finBasis K (throughSubspaceComplement V A U₀ p.castSucc)))
            (basisOfIsCompl
              (throughSubspace_isCompl_complement V A U₀ p.succ)
              ((Module.finBasis K U₀).map
                (throughSubspacePrefixEquiv V A U₀ p.succ hU₀))
              (Module.finBasis K (throughSubspaceComplement V A U₀ p.succ)))
            (A p) =
          fromBlocks (1 : Matrix (Fin (Module.finrank K U₀))
            (Fin (Module.finrank K U₀)) K) B' 0 D' := by
  simpa [throughSubspaceChartDataOfFiniteDimensional] using
    (exists_unitriangular_toMatrix_throughSubspaceEdge_chartData_eq_fromBlocks_one_zero V A U₀
      hU₀ (throughSubspaceChartDataOfFiniteDimensional V A U₀) p F)

/-- The finite-dimensional total chain map has concrete adapted-basis form `[I 0; 0 0]`. -/
theorem toMatrix_chainMap_zero_last_ker_finiteDimensional_eq_fromBlocks_one_zero_zero
    [∀ j, FiniteDimensional K (V j)]
    (U₀ : Submodule K (V 0))
    (hU₀ : IsCompl U₀
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N))))) :
      LinearMap.toMatrix
          (basisOfIsCompl hU₀ (Module.finBasis K U₀)
            (Module.finBasis K
              (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N))))))
          (basisOfIsCompl
            (throughSubspace_isCompl_complement V A U₀ (Fin.last N))
            ((Module.finBasis K U₀).map (linearEquivMapOfDisjointKer
              (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N))) U₀ hU₀.disjoint))
            (Module.finBasis K (throughSubspaceComplement V A U₀ (Fin.last N))))
          (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N))) =
        fromBlocks (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
          (0 : Matrix (Fin (Module.finrank K U₀))
            (Fin (Module.finrank K
              (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))))) K)
          (0 : Matrix (throughSubspaceComplementIndex V A U₀ (Fin.last N))
            (Fin (Module.finrank K U₀)) K)
          (0 : Matrix (throughSubspaceComplementIndex V A U₀ (Fin.last N))
            (Fin (Module.finrank K
              (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))))) K) := by
  exact toMatrix_chainMap_zero_last_ker_basisOfIsCompl_eq_fromBlocks_one_zero_zero
    V A U₀ hU₀
    (throughSubspace_isCompl_complement V A U₀ (Fin.last N))
    (Module.finBasis K U₀)
    (Module.finBasis K
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))))
    (Module.finBasis K (throughSubspaceComplement V A U₀ (Fin.last N)))

/-- Finite-dimensional layers supply a kernel complement with finite-indexed chart data. -/
theorem exists_isCompl_ker_throughSubspaceChartDataOfFiniteDimensional
    [∀ j, FiniteDimensional K (V j)] :
    ∃ U₀ : Submodule K (V 0),
      IsCompl U₀
          (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))) ∧
        Module.finrank K U₀ =
          Module.finrank K
            (LinearMap.range
              (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))) ∧
          Nonempty (ThroughSubspaceChartData V A U₀
            (Fin (Module.finrank K U₀)) (throughSubspaceComplementIndex V A U₀)) := by
  let P : V 0 →ₗ[K] V (Fin.last N) :=
    chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N))
  rcases exists_isCompl_ker_and_finrank_eq_range (P := P) with ⟨U₀, hU₀, hfinU₀⟩
  exact ⟨U₀, by simpa [P] using hU₀, by simpa [P] using hfinU₀,
    nonempty_throughSubspaceChartDataOfFiniteDimensional V A U₀⟩

end FiniteChartData

section PaperOrderFiniteChartData

universe u v

variable {K : Type u} [Field K] {N : ℕ}
  (W : Fin (N + 1) → Type v) [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
  (B : ∀ i : Fin N, W i.succ →ₗ[K] W i.castSucc)

/-- A paper-order total-kernel hypothesis as a reversed source-to-target hypothesis. -/
theorem disjoint_ker_reverse_total_of_disjoint_ker_paperChainMap
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : Disjoint U₀
      (LinearMap.ker
        (paperChainMap W B (Fin.last N).rev (0 : Fin (N + 1)).rev
          (Fin.rev_le_rev.mpr (Fin.zero_le (Fin.last N)))))) :
    Disjoint U₀
      (LinearMap.ker
        (chainMap (reverseVertex W) (reverseEdge W B) 0 (Fin.last N)
          (Fin.zero_le (Fin.last N)))) := by
  simpa [chainMap_reverse_eq_paper] using hU₀

/-- A paper-order total-kernel complement as a reversed source-to-target complement. -/
theorem isCompl_ker_reverse_total_of_isCompl_ker_paperChainMap
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀
      (LinearMap.ker
        (paperChainMap W B (Fin.last N).rev (0 : Fin (N + 1)).rev
          (Fin.rev_le_rev.mpr (Fin.zero_le (Fin.last N)))))) :
    IsCompl U₀
      (LinearMap.ker
        (chainMap (reverseVertex W) (reverseEdge W B) 0 (Fin.last N)
          (Fin.zero_le (Fin.last N)))) := by
  simpa [chainMap_reverse_eq_paper] using hU₀

/-- Finite-dimensional paper-order layers supply endpoint-compatible chart data. -/
theorem exists_isCompl_ker_paperEndpointChartDataOfFiniteDimensional
    [∀ j, FiniteDimensional K (W j)] :
    ∃ U₀ : Submodule K (reverseVertex W 0),
      IsCompl U₀
          (LinearMap.ker
            (paperChainMap W B (Fin.last N).rev (0 : Fin (N + 1)).rev
              (Fin.rev_le_rev.mpr (Fin.zero_le (Fin.last N))))) ∧
        Module.finrank K U₀ =
          Module.finrank K
            (LinearMap.range
              (paperChainMap W B (Fin.last N).rev (0 : Fin (N + 1)).rev
                (Fin.rev_le_rev.mpr (Fin.zero_le (Fin.last N))))) ∧
          Nonempty (ThroughSubspaceChartData (reverseVertex W) (reverseEdge W B) U₀
            (Fin (Module.finrank K U₀))
            (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀)) := by
  rcases exists_isCompl_ker_throughSubspaceEndpointChartDataOfFiniteDimensional
      (reverseVertex W) (reverseEdge W B) with
    ⟨U₀, hU₀, hfinU₀, hdata⟩
  refine ⟨U₀, ?_, ?_, hdata⟩
  · simpa [chainMap_reverse_eq_paper] using hU₀
  · have htotal :
        chainMap (reverseVertex W) (reverseEdge W B) 0 (Fin.last N)
            (Fin.zero_le (Fin.last N)) =
          paperChainMap W B (Fin.last N).rev (0 : Fin (N + 1)).rev
            (Fin.rev_le_rev.mpr (Fin.zero_le (Fin.last N))) :=
      chainMap_reverse_eq_paper W B 0 (Fin.last N) (Fin.zero_le (Fin.last N))
    rw [htotal] at hfinU₀
    exact hfinU₀

/-- Endpoint-compatible paper data gives one reversed edge block and the total paper block. -/
theorem paperEndpointChartData_edge_and_totalProduct_blocks
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀
      (LinearMap.ker
        (paperChainMap W B (Fin.last N).rev (0 : Fin (N + 1)).rev
          (Fin.rev_le_rev.mpr (Fin.zero_le (Fin.last N))))))
    (p : Fin N) :
    let hU₀rev := isCompl_ker_reverse_total_of_isCompl_ker_paperChainMap W B U₀ hU₀
    let data := throughSubspaceEndpointChartDataOfFiniteDimensional
      (reverseVertex W) (reverseEdge W B) U₀ hU₀rev
    (∃ Bmat : Matrix (Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀
          p.castSucc) K,
      ∃ Dmat : Matrix
          (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
          (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀
            p.castSucc) K,
        LinearMap.toMatrix
            (throughSubspaceAdaptedBasis (reverseVertex W) (reverseEdge W B) U₀
              hU₀rev.disjoint data p.castSucc)
            (throughSubspaceAdaptedBasis (reverseVertex W) (reverseEdge W B) U₀
              hU₀rev.disjoint data p.succ)
            (reverseEdge W B p) =
          fromBlocks (1 : Matrix (Fin (Module.finrank K U₀))
            (Fin (Module.finrank K U₀)) K) Bmat 0 Dmat) ∧
      LinearMap.toMatrix
          (throughSubspaceAdaptedBasis (reverseVertex W) (reverseEdge W B) U₀
            hU₀rev.disjoint data 0)
          (throughSubspaceAdaptedBasis (reverseVertex W) (reverseEdge W B) U₀
            hU₀rev.disjoint data (Fin.last N))
          (paperChainMap W B (Fin.last N).rev (0 : Fin (N + 1)).rev
            (Fin.rev_le_rev.mpr (Fin.zero_le (Fin.last N)))) =
        fromBlocks (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
          (0 : Matrix (Fin (Module.finrank K U₀))
            (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0)
            K)
          (0 : Matrix
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (Fin (Module.finrank K U₀)) K)
          (0 : Matrix
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0)
            K) := by
  dsimp
  simpa [chainMap_reverse_eq_paper] using
    (endpointChartData_edge_and_totalProduct_blocks
      (reverseVertex W) (reverseEdge W B) U₀
      (isCompl_ker_reverse_total_of_isCompl_ker_paperChainMap W B U₀ hU₀) p)

/-- The adapted matrix of one paper-order edge in the reversed finite chart data. -/
def paperAdaptedReverseEdgeMatrix
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : Disjoint U₀
      (LinearMap.ker
        (paperChainMap W B (Fin.last N).rev (0 : Fin (N + 1)).rev
          (Fin.rev_le_rev.mpr (Fin.zero_le (Fin.last N))))))
    (p : Fin N) :
    Matrix
      (Fin (Module.finrank K U₀) ⊕
        throughSubspaceComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
      (Fin (Module.finrank K U₀) ⊕
        throughSubspaceComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K :=
  LinearMap.toMatrix
    (basisOfIsCompl
      (throughSubspace_isCompl_complement
        (reverseVertex W) (reverseEdge W B) U₀ p.castSucc)
      ((Module.finBasis K U₀).map
        (throughSubspacePrefixEquiv (reverseVertex W) (reverseEdge W B) U₀
          p.castSucc
          (disjoint_ker_reverse_total_of_disjoint_ker_paperChainMap W B U₀ hU₀)))
      (Module.finBasis K
        (throughSubspaceComplement
          (reverseVertex W) (reverseEdge W B) U₀ p.castSucc)))
    (basisOfIsCompl
      (throughSubspace_isCompl_complement
        (reverseVertex W) (reverseEdge W B) U₀ p.succ)
      ((Module.finBasis K U₀).map
        (throughSubspacePrefixEquiv (reverseVertex W) (reverseEdge W B) U₀
          p.succ
          (disjoint_ker_reverse_total_of_disjoint_ker_paperChainMap W B U₀ hU₀)))
      (Module.finBasis K
        (throughSubspaceComplement
          (reverseVertex W) (reverseEdge W B) U₀ p.succ)))
    (reverseEdge W B p)

/-- The upper-unitriangular multiplier used on an adapted paper-order edge matrix. -/
def paperUnitriangularLeft
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0)) (p : Fin N)
    (F : Matrix (Fin (Module.finrank K U₀))
        (throughSubspaceComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ) K) :
    Matrix
      (Fin (Module.finrank K U₀) ⊕
        throughSubspaceComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
      (Fin (Module.finrank K U₀) ⊕
        throughSubspaceComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ) K :=
  fromBlocks (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
    (-F) 0 1

/-- A paper-order edge has concrete adapted-basis block form `[I B; 0 D]`. -/
theorem exists_toMatrix_reverseEdge_finiteDimensional_eq_fromBlocks_one_zero
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : Disjoint U₀
      (LinearMap.ker
        (paperChainMap W B (Fin.last N).rev (0 : Fin (N + 1)).rev
          (Fin.rev_le_rev.mpr (Fin.zero_le (Fin.last N))))))
    (p : Fin N) :
    ∃ Bmat : Matrix (Fin (Module.finrank K U₀))
        (throughSubspaceComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K,
      ∃ Dmat : Matrix
          (throughSubspaceComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
          (throughSubspaceComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K,
        LinearMap.toMatrix
            (basisOfIsCompl
              (throughSubspace_isCompl_complement
                (reverseVertex W) (reverseEdge W B) U₀ p.castSucc)
              ((Module.finBasis K U₀).map
                (throughSubspacePrefixEquiv (reverseVertex W) (reverseEdge W B) U₀
                  p.castSucc
                  (disjoint_ker_reverse_total_of_disjoint_ker_paperChainMap W B U₀ hU₀)))
              (Module.finBasis K
                (throughSubspaceComplement
                  (reverseVertex W) (reverseEdge W B) U₀ p.castSucc)))
            (basisOfIsCompl
              (throughSubspace_isCompl_complement
                (reverseVertex W) (reverseEdge W B) U₀ p.succ)
              ((Module.finBasis K U₀).map
                (throughSubspacePrefixEquiv (reverseVertex W) (reverseEdge W B) U₀
                  p.succ
                  (disjoint_ker_reverse_total_of_disjoint_ker_paperChainMap W B U₀ hU₀)))
              (Module.finBasis K
                (throughSubspaceComplement
                  (reverseVertex W) (reverseEdge W B) U₀ p.succ)))
            (reverseEdge W B p) =
          fromBlocks (1 : Matrix (Fin (Module.finrank K U₀))
            (Fin (Module.finrank K U₀)) K) Bmat 0 Dmat := by
  exact exists_toMatrix_throughSubspaceEdge_finiteDimensional_eq_fromBlocks_one_zero
    (reverseVertex W) (reverseEdge W B) U₀
    (disjoint_ker_reverse_total_of_disjoint_ker_paperChainMap W B U₀ hU₀) p

/-- The adapted paper-order edge matrix has identity top-left corner form. -/
theorem identityCornerForm_paperAdaptedReverseEdgeMatrix
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : Disjoint U₀
      (LinearMap.ker
        (paperChainMap W B (Fin.last N).rev (0 : Fin (N + 1)).rev
          (Fin.rev_le_rev.mpr (Fin.zero_le (Fin.last N))))))
    (p : Fin N) :
    identityCornerForm (paperAdaptedReverseEdgeMatrix W B U₀ hU₀ p) :=
  exists_toMatrix_reverseEdge_finiteDimensional_eq_fromBlocks_one_zero W B U₀ hU₀ p

/-- The adapted paper-order edge matrix has selected top-left corner equal to `1`. -/
theorem topLeftCorner_paperAdaptedReverseEdgeMatrix_eq_one
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : Disjoint U₀
      (LinearMap.ker
        (paperChainMap W B (Fin.last N).rev (0 : Fin (N + 1)).rev
          (Fin.rev_le_rev.mpr (Fin.zero_le (Fin.last N))))))
    (p : Fin N) :
    topLeftCorner (paperAdaptedReverseEdgeMatrix W B U₀ hU₀ p) =
      (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K) :=
  topLeftCorner_eq_one_of_identityCornerForm
    (identityCornerForm_paperAdaptedReverseEdgeMatrix W B U₀ hU₀ p)

/-- The adapted paper-order edge matrix lies in the selected determinant chart. -/
theorem identityCornerDetChart_paperAdaptedReverseEdgeMatrix
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : Disjoint U₀
      (LinearMap.ker
        (paperChainMap W B (Fin.last N).rev (0 : Fin (N + 1)).rev
          (Fin.rev_le_rev.mpr (Fin.zero_le (Fin.last N))))))
    (p : Fin N) :
    identityCornerDetChart (paperAdaptedReverseEdgeMatrix W B U₀ hU₀ p) :=
  identityCornerDetChart_of_identityCornerForm
    (identityCornerForm_paperAdaptedReverseEdgeMatrix W B U₀ hU₀ p)

/-- A block-diagonal prefix extends across one adapted paper-order edge by right elimination. -/
theorem productReduction_paperAdaptedReverseEdgeMatrix_rightElim
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : Disjoint U₀
      (LinearMap.ker
        (paperChainMap W B (Fin.last N).rev (0 : Fin (N + 1)).rev
          (Fin.rev_le_rev.mpr (Fin.zero_le (Fin.last N))))))
    (p : Fin N) {π : Type*}
    (C1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
    (Dprev : Matrix π
      (throughSubspaceComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ) K) :
    ∃ Bmat : Matrix (Fin (Module.finrank K U₀))
        (throughSubspaceComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K,
      ∃ Dmat : Matrix
          (throughSubspaceComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
          (throughSubspaceComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K,
        fromBlocks C1 0 0 Dprev *
            paperAdaptedReverseEdgeMatrix W B U₀ hU₀ p *
            fromBlocks
              (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
              (-Bmat) 0
              (1 : Matrix
                (throughSubspaceComplementIndex (reverseVertex W) (reverseEdge W B) U₀
                  p.castSucc)
                (throughSubspaceComplementIndex (reverseVertex W) (reverseEdge W B) U₀
                  p.castSucc) K) =
          fromBlocks C1 0 0 (Dprev * Dmat) :=
  productReduction_blockDiagonal_mul_identityCornerForm_rightElim C1 Dprev
    (identityCornerForm_paperAdaptedReverseEdgeMatrix W B U₀ hU₀ p)

/-- A paper-order edge remains in identity-corner block form after a unitriangular multiplier. -/
theorem exists_unitriangular_toMatrix_reverseEdge_finiteDimensional_eq_fromBlocks_one_zero
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : Disjoint U₀
      (LinearMap.ker
        (paperChainMap W B (Fin.last N).rev (0 : Fin (N + 1)).rev
          (Fin.rev_le_rev.mpr (Fin.zero_le (Fin.last N))))))
    (p : Fin N)
    (F : Matrix (Fin (Module.finrank K U₀))
        (throughSubspaceComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ) K) :
    ∃ B' : Matrix (Fin (Module.finrank K U₀))
        (throughSubspaceComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K,
      ∃ D' : Matrix
          (throughSubspaceComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
          (throughSubspaceComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K,
        fromBlocks (1 : Matrix (Fin (Module.finrank K U₀))
            (Fin (Module.finrank K U₀)) K) (-F) 0 1 *
          LinearMap.toMatrix
            (basisOfIsCompl
              (throughSubspace_isCompl_complement
                (reverseVertex W) (reverseEdge W B) U₀ p.castSucc)
              ((Module.finBasis K U₀).map
                (throughSubspacePrefixEquiv (reverseVertex W) (reverseEdge W B) U₀
                  p.castSucc
                  (disjoint_ker_reverse_total_of_disjoint_ker_paperChainMap W B U₀ hU₀)))
              (Module.finBasis K
                (throughSubspaceComplement
                  (reverseVertex W) (reverseEdge W B) U₀ p.castSucc)))
            (basisOfIsCompl
              (throughSubspace_isCompl_complement
                (reverseVertex W) (reverseEdge W B) U₀ p.succ)
              ((Module.finBasis K U₀).map
                (throughSubspacePrefixEquiv (reverseVertex W) (reverseEdge W B) U₀
                  p.succ
                  (disjoint_ker_reverse_total_of_disjoint_ker_paperChainMap W B U₀ hU₀)))
              (Module.finBasis K
                (throughSubspaceComplement
                  (reverseVertex W) (reverseEdge W B) U₀ p.succ)))
            (reverseEdge W B p) =
          fromBlocks (1 : Matrix (Fin (Module.finrank K U₀))
            (Fin (Module.finrank K U₀)) K) B' 0 D' := by
  exact exists_unitriangular_toMatrix_throughSubspaceEdge_finiteDimensional_eq_fromBlocks_one_zero
    (reverseVertex W) (reverseEdge W B) U₀
    (disjoint_ker_reverse_total_of_disjoint_ker_paperChainMap W B U₀ hU₀) p F

/-- The unitriangularly transformed paper-order edge remains in identity-corner form. -/
theorem identityCornerForm_unitriangular_paperAdaptedReverseEdgeMatrix
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : Disjoint U₀
      (LinearMap.ker
        (paperChainMap W B (Fin.last N).rev (0 : Fin (N + 1)).rev
          (Fin.rev_le_rev.mpr (Fin.zero_le (Fin.last N))))))
    (p : Fin N)
    (F : Matrix (Fin (Module.finrank K U₀))
        (throughSubspaceComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ) K) :
    identityCornerForm
      (paperUnitriangularLeft W B U₀ p F * paperAdaptedReverseEdgeMatrix W B U₀ hU₀ p) :=
  exists_unitriangular_toMatrix_reverseEdge_finiteDimensional_eq_fromBlocks_one_zero
    W B U₀ hU₀ p F

/-- The unitriangularly transformed paper-order edge lies in the selected determinant chart. -/
theorem identityCornerDetChart_unitriangular_paperAdaptedReverseEdgeMatrix
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : Disjoint U₀
      (LinearMap.ker
        (paperChainMap W B (Fin.last N).rev (0 : Fin (N + 1)).rev
          (Fin.rev_le_rev.mpr (Fin.zero_le (Fin.last N))))))
    (p : Fin N)
    (F : Matrix (Fin (Module.finrank K U₀))
        (throughSubspaceComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ) K) :
    identityCornerDetChart
      (paperUnitriangularLeft W B U₀ p F * paperAdaptedReverseEdgeMatrix W B U₀ hU₀ p) :=
  identityCornerDetChart_of_identityCornerForm
    (identityCornerForm_unitriangular_paperAdaptedReverseEdgeMatrix W B U₀ hU₀ p F)

/-- The paper-order total product has endpoint adapted-basis form `[I 0; 0 0]`. -/
theorem toMatrix_paperChainMap_ker_finiteDimensional_eq_fromBlocks_one_zero_zero
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀
      (LinearMap.ker
        (paperChainMap W B (Fin.last N).rev (0 : Fin (N + 1)).rev
          (Fin.rev_le_rev.mpr (Fin.zero_le (Fin.last N)))))) :
      LinearMap.toMatrix
          (basisOfIsCompl
            (isCompl_ker_reverse_total_of_isCompl_ker_paperChainMap W B U₀ hU₀)
            (Module.finBasis K U₀)
            (Module.finBasis K
              (LinearMap.ker
                (chainMap (reverseVertex W) (reverseEdge W B) 0 (Fin.last N)
                  (Fin.zero_le (Fin.last N))))))
          (basisOfIsCompl
            (throughSubspace_isCompl_complement
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            ((Module.finBasis K U₀).map (linearEquivMapOfDisjointKer
              (chainMap (reverseVertex W) (reverseEdge W B) 0 (Fin.last N)
                (Fin.zero_le (Fin.last N))) U₀
              (isCompl_ker_reverse_total_of_isCompl_ker_paperChainMap W B U₀ hU₀).disjoint))
            (Module.finBasis K
              (throughSubspaceComplement
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))))
          (paperChainMap W B (Fin.last N).rev (0 : Fin (N + 1)).rev
            (Fin.rev_le_rev.mpr (Fin.zero_le (Fin.last N)))) =
        fromBlocks (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
          (0 : Matrix (Fin (Module.finrank K U₀))
            (Fin (Module.finrank K
              (LinearMap.ker
                (chainMap (reverseVertex W) (reverseEdge W B) 0 (Fin.last N)
                  (Fin.zero_le (Fin.last N)))))) K)
          (0 : Matrix
            (throughSubspaceComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (Fin (Module.finrank K U₀)) K)
          (0 : Matrix
            (throughSubspaceComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (Fin (Module.finrank K
              (LinearMap.ker
                (chainMap (reverseVertex W) (reverseEdge W B) 0 (Fin.last N)
                  (Fin.zero_le (Fin.last N)))))) K) := by
  simpa [chainMap_reverse_eq_paper] using
    (toMatrix_chainMap_zero_last_ker_finiteDimensional_eq_fromBlocks_one_zero_zero
      (reverseVertex W) (reverseEdge W B) U₀
      (isCompl_ker_reverse_total_of_isCompl_ker_paperChainMap W B U₀ hU₀))

end PaperOrderFiniteChartData

end Aoyagi
end DLN
end DLNFibre
