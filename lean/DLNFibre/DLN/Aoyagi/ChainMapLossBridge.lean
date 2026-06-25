import DLNFibre.DLN.Aoyagi.ChainMapTupleBridge
import DLNFibre.DLN.RlctPayoff

/-!
# Loss wrappers for chain-map coordinate tuples

This file rewrites `lossDLN` on a tuple obtained from edge matrices in fixed
bases as the Frobenius trace of the corresponding chain-map matrix difference.
It is a definitional finite-linear-algebra bridge; it does not compare this
loss with adapted endpoint coordinates, statistical losses, or RLCT data.
-/

noncomputable section

namespace DLNFibre
namespace DLN
namespace Aoyagi

open Matrix DLNFibre.Core

section ChainMapLossBridge

variable {N : ℕ}
variable {V : Fin (N + 1) → Type*}
variable [∀ j, AddCommGroup (V j)] [∀ j, Module ℝ (V j)]
variable {d : Fin (N + 1) → ℕ}

/-- Frobenius trace loss of a chain-map matrix against a target matrix in the
same endpoint bases. -/
def chainMapMatrixFrobeniusLossAgainst
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (V j))
    (T : V 0 →ₗ[ℝ] V (Fin.last N))
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ) : ℝ :=
  let M := LinearMap.toMatrix (b 0) (b (Fin.last N)) T - B
  (Mᵀ * M).trace

/-- Frobenius trace loss between two chain maps in the same endpoint bases. -/
def chainMapMatrixFrobeniusLoss
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (V j))
    (T T₀ : V 0 →ₗ[ℝ] V (Fin.last N)) : ℝ :=
  chainMapMatrixFrobeniusLossAgainst b T
    (LinearMap.toMatrix (b 0) (b (Fin.last N)) T₀)

/-- `lossDLN` of a chain-coordinate tuple unfolds to the Frobenius trace of
the corresponding chain-map matrix minus the chosen target matrix. -/
theorem lossDLN_chainMapMatrixTuple_eq_trace
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (V j))
    (A : ∀ p : Fin N, V p.castSucc →ₗ[ℝ] V p.succ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ) :
    lossDLN d B (chainMapMatrixTuple b A) =
      chainMapMatrixFrobeniusLossAgainst b
        (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N))) B := by
  rw [lossDLN, chainMapMatrixFrobeniusLossAgainst,
    mult_chainMapMatrixTuple (d := d) (V := V) b A]

/-- If the target matrix is itself the matrix of a fixed target chain, then
`lossDLN` is the Frobenius trace of the difference of total chain-map
matrices. -/
theorem lossDLN_chainMapMatrixTuple_eq_chainMapFrobenius
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (V j))
    (A A₀ : ∀ p : Fin N, V p.castSucc →ₗ[ℝ] V p.succ) :
    lossDLN d
        (LinearMap.toMatrix (b 0) (b (Fin.last N))
          (chainMap V A₀ 0 (Fin.last N) (Fin.zero_le (Fin.last N))))
        (chainMapMatrixTuple b A) =
      chainMapMatrixFrobeniusLoss b
        (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))
        (chainMap V A₀ 0 (Fin.last N) (Fin.zero_le (Fin.last N))) := by
  rw [lossDLN_chainMapMatrixTuple_eq_trace, chainMapMatrixFrobeniusLoss]

/-- Reverse-vertex Aoyagi specialization: with target the base paper-order
chain, `lossDLN` of a reversed edge-coordinate tuple is the Frobenius trace of
the difference of reversed endpoint chain-map matrices. -/
theorem lossDLN_reverseVertex_chainMapMatrixTuple_eq_baseFrobenius
    {W : Fin (N + 1) → Type*}
    [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)]
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (reverseVertex W j))
    (E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)
    (Bpaper : ∀ p : Fin N, W p.succ →ₗ[ℝ] W p.castSucc) :
    lossDLN d
        (LinearMap.toMatrix (b 0) (b (Fin.last N))
          (chainMap (reverseVertex W) (reverseEdge W Bpaper) 0
            (Fin.last N) (Fin.zero_le (Fin.last N))))
        (chainMapMatrixTuple b E) =
      chainMapMatrixFrobeniusLoss b
        (chainMap (reverseVertex W) E 0
          (Fin.last N) (Fin.zero_le (Fin.last N)))
        (chainMap (reverseVertex W) (reverseEdge W Bpaper) 0
          (Fin.last N) (Fin.zero_le (Fin.last N))) := by
  exact
    lossDLN_chainMapMatrixTuple_eq_chainMapFrobenius
      (d := d) (V := reverseVertex W) b E (reverseEdge W Bpaper)

end ChainMapLossBridge

end Aoyagi
end DLN
end DLNFibre
