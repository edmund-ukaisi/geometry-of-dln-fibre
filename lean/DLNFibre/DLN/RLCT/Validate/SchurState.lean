import DLNFibre.DLN.RLCT.Validate.GeneralR1Recursion

/-!
# `DLNFibre.DLN.RLCT.Validate.SchurState` — the C1 reduced-width datum (fm3)

The concrete `ChainDimSplit` a C1 (blow-up ⊕ det-1 Schur-peel) node produces: the reduced widths
`schurState M = (M₀−1, M₁−1, M₂, …)` (the two pivot vertices each drop one width; the det-1 triangular
peel clears the pivot row+col, `ΣM−2`). Locked design (fm3 g194/g196, pp2 g183/g207): the recursion's
per-node reduction is `split.red = schurState M`, the GENUINE reduced chain — `ChainDimSplit` is crux2's
certified carrier, populated here.

`schurState` lives on the SAME `Fin (L+1)` the recursion carries (`L` fixed — the width-only reduction);
it requires `1 ≤ M s` at the two pivot vertices (`s.val ≤ 1`), supplied by the per-node `hMid (∀ s, 0 <
M s)` invariant. `ΣM`-termination is `ChainDimSplit.redM_widthSum_lt` (banked in `RouteMRecursion`), free
from the `hdrops` field this constructs.
-/

open scoped BigOperators
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The C1 reduced-width split** `schurState M = (M₀−1, M₁−1, M₂, …)`. The det-1 Schur-peel clears the
two pivot vertices' rows/cols, dropping one width at each (`drop = 1` at `s.val ≤ 1`, `0` else;
`ΣM − 2`). A `ChainDimSplit M` on the same `Fin (L+1)` (width-only reduction, `L` fixed). Requires
`1 ≤ M s` at the pivot vertices (`s.val ≤ 1`) — supplied by the per-node `hMid`. -/
def schurState (M : Fin (L + 1) → ℕ) (hlo : ∀ s : Fin (L + 1), s.val ≤ 1 → 1 ≤ M s) :
    ChainDimSplit M where
  drop := fun s => if s.val ≤ 1 then 1 else 0
  red := fun s => if s.val ≤ 1 then M s - 1 else M s
  hsum := by
    intro s
    by_cases hs : s.val ≤ 1
    · simp only [hs, if_true]; have := hlo s hs; omega
    · simp only [hs, if_false]; omega
  hdrops := by
    apply Finset.sum_pos'
    · exact fun _ _ => Nat.zero_le _
    · exact ⟨0, Finset.mem_univ 0, by simp⟩

/-- The reduced widths of `schurState` are `M s − 1` at the two pivot vertices (`s.val ≤ 1`), `M s`
elsewhere — i.e. `(M₀−1, M₁−1, M₂, …)`. -/
@[simp] theorem schurState_red (M : Fin (L + 1) → ℕ) (hlo : ∀ s : Fin (L + 1), s.val ≤ 1 → 1 ≤ M s)
    (s : Fin (L + 1)) :
    (schurState M hlo).red s = if s.val ≤ 1 then M s - 1 else M s := rfl

/-- The dropped widths of `schurState` are `1` at the two pivot vertices, `0` elsewhere. -/
@[simp] theorem schurState_drop (M : Fin (L + 1) → ℕ) (hlo : ∀ s : Fin (L + 1), s.val ≤ 1 → 1 ≤ M s)
    (s : Fin (L + 1)) :
    (schurState M hlo).drop s = if s.val ≤ 1 then 1 else 0 := rfl

end DLNFibre.DLN.RLCT
