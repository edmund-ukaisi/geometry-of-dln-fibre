import DLNFibre.Core.CascadeRank
import DLNFibre.Core.Submult

/-!
# `DLNFibre.Core.CascadeRealizable` — the diagonal cascade realizes its rank pattern

Rung 2+ of the cascade-realizability ladder (pp2 g228 / pp-r1realize #107, double-confirmed): the explicit
diagonal cascade `cascadeTuple d t := fun s ↦ partialId (d_{s+1}) (d_s) (t_s)` (Core's left-multiply
orientation) has every interval sub-product a single partial-identity, its rank the running window-min of
the block ranks — `count-the-1s`, no `Matrix.rank_mul_le`, no surjectivity.

`submult (cascadeTuple) i j = partialId (d_j) (d_i) (⨅_{i ≤ s < j} t_s)` (`submult_cascade`), so the rank
pattern `rankFn (cascadeTuple) i j = min over the window of the block ranks` (`rank_submult_cascade`),
capped by the endpoint widths. This is the matrix-level cascade computation; the §4 achiever witness
`T* ∈ RealizableRank` instantiates it with the achiever's running ranks (downstream, with the `embedRank`
2-index matching).
-/

open Matrix
namespace DLNFibre.Core

variable {k : Type*} [Field k] {N : ℕ}

/-- **The diagonal cascade** (Core left-multiply orientation): `A_s = partialId (d_{s+1}) (d_s) (t_s)`, the
rectangular partial-identity block with `t_s` surviving 1s. A genuine `Tuple d` (the block dimensions match
the `Tuple` factor shape `Matrix (Fin (d s.succ)) (Fin (d s.castSucc))`). -/
def cascadeTuple (d : Fin (N + 1) → ℕ) (t : Fin N → ℕ) : Tuple (k := k) d :=
  fun s => partialId k (d s.succ) (d s.castSucc) (t s)

/-- **Single-step (the cascade's one-block sub-product).** `submult (cascadeTuple) s.castSucc s.succ` is the
block `A_s = partialId (d_{s+1}) (d_s) (t_s)` itself. The base case of the cascade product iteration
(`submult i (i+1) = A_i`), via `submult_succ` + `submult_self`. -/
theorem submult_cascade_single (d : Fin (N + 1) → ℕ) (t : Fin N → ℕ) (s : Fin N) :
    submult d (cascadeTuple (k := k) d t) s.castSucc s.succ (Fin.castSucc_le_succ s)
      = partialId k (d s.succ) (d s.castSucc) (t s) := by
  rw [submult_succ d (cascadeTuple d t) s.castSucc s le_rfl, submult_self, Matrix.mul_one]
  rfl

end DLNFibre.Core
