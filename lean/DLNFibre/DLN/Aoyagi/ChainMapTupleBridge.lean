import DLNFibre.Core.Submult
import DLNFibre.DLN.Aoyagi.ThroughLayerBasis
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Bridge from Aoyagi chain maps to the core multiplication tuple

This file records the finite matrix-product identity needed before comparing
Aoyagi endpoint coordinate losses with `lossDLN`: the core `mult` of the tuple
of edge matrices in fixed bases is the matrix of the corresponding `chainMap`.
It is only finite linear algebra; it does not state analytic, statistical, or
RLCT consequences.
-/

noncomputable section

namespace DLNFibre
namespace DLN
namespace Aoyagi

open DLNFibre.Core

section ChainMapTupleBridge

variable {K : Type*} [Field K] {N : ℕ}
variable {V : Fin (N + 1) → Type*}
variable [∀ j, AddCommGroup (V j)] [∀ j, Module K (V j)]
variable {d : Fin (N + 1) → ℕ}

/-- The core matrix tuple obtained by expressing each chain edge in fixed bases. -/
def chainMapMatrixTuple
    (b : ∀ j, Module.Basis (Fin (d j)) K (V j))
    (A : ∀ p : Fin N, V p.castSucc →ₗ[K] V p.succ) : Tuple (k := K) d :=
  fun p ↦ LinearMap.toMatrix (b p.castSucc) (b p.succ) (A p)

/-- Interval products of edge matrices are matrices of interval chain maps. -/
theorem submult_chainMapMatrixTuple
    (b : ∀ j, Module.Basis (Fin (d j)) K (V j))
    (A : ∀ p : Fin N, V p.castSucc →ₗ[K] V p.succ)
    (i j : Fin (N + 1)) (hij : i ≤ j) :
    submult d (chainMapMatrixTuple b A) i j hij =
      LinearMap.toMatrix (b i) (b j) (chainMap V A i j hij) := by
  induction j using Fin.induction with
  | zero =>
      obtain rfl : i = 0 := Fin.le_zero_iff.mp hij
      rw [submult_self, chainMap_self, LinearMap.toMatrix_id]
  | succ p ih =>
      rcases eq_or_lt_of_le hij with rfl | hlt
      · rw [submult_self, chainMap_self, LinearMap.toMatrix_id]
      · have hip : i ≤ p.castSucc := by
          rw [Fin.le_castSucc_iff]
          exact hlt
        rw [submult_succ d (chainMapMatrixTuple b A) i p hip, ih hip,
          chainMap_succ V A i p hip]
        symm
        exact LinearMap.toMatrix_comp
          (b i) (b p.castSucc) (b p.succ) (A p)
          (chainMap V A i p.castSucc hip)

/-- Prefix products of edge matrices are matrices of prefix chain maps. -/
theorem multPrefix_chainMapMatrixTuple
    (b : ∀ j, Module.Basis (Fin (d j)) K (V j))
    (A : ∀ p : Fin N, V p.castSucc →ₗ[K] V p.succ)
    (j : Fin (N + 1)) :
    multPrefix d (chainMapMatrixTuple b A) j =
      LinearMap.toMatrix (b 0) (b j) (chainMap V A 0 j (Fin.zero_le j)) := by
  induction j using Fin.induction with
  | zero =>
      rw [multPrefix_zero, chainMap_self, LinearMap.toMatrix_id]
  | succ p ih =>
      rw [multPrefix_succ, ih, chainMap_succ V A 0 p (Fin.zero_le p.castSucc)]
      symm
      exact LinearMap.toMatrix_comp
        (b 0) (b p.castSucc) (b p.succ) (A p)
        (chainMap V A 0 p.castSucc (Fin.zero_le p.castSucc))

/-- The core `mult` of edge matrices is the matrix of the total chain map. -/
theorem mult_chainMapMatrixTuple
    (b : ∀ j, Module.Basis (Fin (d j)) K (V j))
    (A : ∀ p : Fin N, V p.castSucc →ₗ[K] V p.succ) :
    mult d (chainMapMatrixTuple b A) =
      LinearMap.toMatrix (b 0) (b (Fin.last N))
        (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N))) := by
  simpa [mult] using
    (multPrefix_chainMapMatrixTuple (d := d) (V := V) b A (Fin.last N))

/-- Inline form: a tuple given directly by edge matrices has product equal to
the matrix of the total chain map. -/
theorem mult_toMatrix_chainMap
    (b : ∀ j, Module.Basis (Fin (d j)) K (V j))
    (A : ∀ p : Fin N, V p.castSucc →ₗ[K] V p.succ) :
    mult d (fun p ↦ LinearMap.toMatrix (b p.castSucc) (b p.succ) (A p)) =
      LinearMap.toMatrix (b 0) (b (Fin.last N))
        (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N))) := by
  simpa [chainMapMatrixTuple] using
    (mult_chainMapMatrixTuple (d := d) (V := V) b A)

/-- Reverse-vertex form of `mult_toMatrix_chainMap`, for Aoyagi paper-order
chains after reversing vertices. -/
theorem mult_toMatrix_chainMap_reverseVertex
    {W : Fin (N + 1) → Type*}
    [∀ j, AddCommGroup (W j)] [∀ j, Module K (W j)]
    (b : ∀ j, Module.Basis (Fin (d j)) K (reverseVertex W j))
    (E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ) :
    mult d (fun p ↦ LinearMap.toMatrix (b p.castSucc) (b p.succ) (E p)) =
      LinearMap.toMatrix (b 0) (b (Fin.last N))
        (chainMap (reverseVertex W) E 0 (Fin.last N)
          (Fin.zero_le (Fin.last N))) := by
  exact mult_toMatrix_chainMap (d := d) (V := reverseVertex W) b E

end ChainMapTupleBridge

end Aoyagi
end DLN
end DLNFibre
