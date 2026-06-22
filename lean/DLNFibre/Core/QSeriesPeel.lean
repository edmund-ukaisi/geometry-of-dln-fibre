import DLNFibre.Core.QSeriesDurfee

/-!
# `DLNFibre.Core.QSeriesPeel` — the local transfer identity (M3 engine)

The engine of the PEEL induction (thread 03 §4, transfer pinned in thread 04): the last-column transfer
is `N` nested applications of the `N = 1` Durfee identity (`durfee`, M2), glued by an arithmetic
exponent split. Stated as a recursion over the last-column data `b : List ℕ` and the residual `d`:

`transferRHS [] d = P d`,
`transferRHS (b₀ :: bs) d = ∑_{x₀=0}^{min b₀ d} X^{(b₀-x₀)(d-x₀)} P(b₀-x₀) P x₀ · transferRHS bs (d-x₀)`.

The identity `transferRHS b d = P d · ∏ P bᵢ` is proved by induction on `b`, applying `durfee` once per
block. (The transfer-pin certificate's inner range `0..b₀` is sharpened to `0..min b₀ d` — the residual
constraint `x₀ ≤ d` — which is exactly the range of `durfee d b₀`.)
-/

namespace DLNFibre.Core

open PowerSeries Finset

/-- The last-column transfer recursion over the block data `b : List ℕ` and residual `d`. -/
noncomputable def transferRHS : List ℕ → ℕ → ℤ⟦X⟧
  | [], d => P d
  | (b0 :: bs), d =>
      ∑ x0 ∈ Finset.range (min b0 d + 1),
        X ^ ((b0 - x0) * (d - x0)) * P (b0 - x0) * P x0 * transferRHS bs (d - x0)

/-- **The local transfer identity** (M3 engine): `transferRHS b d = P d · ∏ᵢ P bᵢ` — `N` nested
applications of the `N = 1` Durfee identity (`durfee`). -/
theorem transferRHS_eq (b : List ℕ) (d : ℕ) :
    transferRHS b d = P d * (b.map P).prod := by
  induction b generalizing d with
  | nil => simp [transferRHS]
  | cons b0 bs ih =>
    rw [transferRHS, List.map_cons, List.prod_cons]
    -- factor the (bs.map P).prod tail out of the sum via the IH
    have step : ∑ x0 ∈ Finset.range (min b0 d + 1),
          X ^ ((b0 - x0) * (d - x0)) * P (b0 - x0) * P x0 * transferRHS bs (d - x0)
        = (∑ x0 ∈ Finset.range (min b0 d + 1),
            X ^ ((b0 - x0) * (d - x0)) * P (b0 - x0) * P x0 * P (d - x0)) * (bs.map P).prod := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun x0 _ ↦ ?_
      rw [ih]; ring
    rw [step]
    -- the inner sum IS durfee d b0 (after `min` and factor commutation)
    have hdurfee : ∑ x0 ∈ Finset.range (min b0 d + 1),
          X ^ ((b0 - x0) * (d - x0)) * P (b0 - x0) * P x0 * P (d - x0) = P d * P b0 := by
      rw [durfee d b0, durfeeSum, Nat.min_comm b0 d]
      refine Finset.sum_congr rfl fun r _ ↦ ?_
      rw [durfeeTerm, Nat.mul_comm (b0 - r) (d - r)]; ring
    rw [hdurfee]; ring

end DLNFibre.Core
