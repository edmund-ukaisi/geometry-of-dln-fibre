import DLNFibre.DLN.RLCT.Validate.RouteMNReg

/-!
# `DLNFibre.DLN.RLCT.Validate.BindingArith` — the recursion-arithmetic hypotheses of
`binding_recursion_of_step` (G-a feed, #143)

fm3's PROVEN `binding_recursion_of_step` (`BindingRecursion.lean`, `routem-ga`) takes the combinatorial
arithmetic of the binding telescope as parameters (fm3 owns the geometric `hstep`/`hbase` producer; these
are the COMBINATORIAL side). This file is the concrete instantiation
`redOf := schurStateRed`, `nRegOf := bindNReg`, `lamOf := lambdaCore`,
`degenChild := isLeafNode ∘ schurStateRed`, discharging the arithmetic hypotheses.

**The ℚ relief (controller, "sig-match is trivial wrapping").** In ℚ the ℕ-truncation dissolves:
`bindNReg M := 2·(lambdaCore M − lambdaCore (schurStateRed M))` makes `harith_step` an UNCONDITIONAL `ring`
identity. The monotonicity `lambdaCore (schurStateRed M) ≤ lambdaCore M` survives only in `hnReg`
(`0 ≤ bindNReg M`) — the one genuine obligation (the achiever-transfer under the `schurState`
width-reduction), carried as the named hypothesis `hMono` until certified. `bindNReg` equals the value-side
`(minAdm M − minAdm (schurStateRed M) : ℚ)` (`2·lambdaCore = (Adm).inf'`, the ℤ minimal codim).
-/

open scoped BigOperators ENNReal
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- The per-node regular count as a ℚ-difference of `lambdaCore`s: `2·(λ M − λ (schurStateRed M))`. Equals
`(minAdm M − minAdm (schurStateRed M) : ℚ)`. The ℚ form makes the telescope step unconditional. -/
def bindNReg (M : Fin (L + 1) → ℕ) : ℚ :=
  2 * (lambdaCore M - lambdaCore (schurStateRed M))

/-- **`harith_step` — the telescope step (UNCONDITIONAL in ℚ).** `lambdaCore M = bindNReg M / 2 +
lambdaCore (schurStateRed M)`. Pure ring identity. No monotonicity needed (the ℚ relief). -/
theorem bind_harith_step (M : Fin (L + 1) → ℕ) :
    lambdaCore M = bindNReg M / 2 + lambdaCore (schurStateRed M) := by
  unfold bindNReg; ring

/-- A leaf node has `lambdaCore = 0`: `isLeafNode` gives `inf' Mval ≤ 0` (via `Int.toNat_eq_zero`), and
`inf' ≥ 0` (admissible `Mval ≥ 0`), so `inf' = 0` and `lambdaCore = ½·0 = 0`. -/
theorem lambdaCore_eq_zero_of_isLeafNode (M : Fin (L + 1) → ℕ) (hleaf : isLeafNode M) :
    lambdaCore M = 0 := by
  obtain ⟨T, hT, hTval⟩ := (isLeafNode_iff_exists_zero M).mp hleaf
  have hge : 0 ≤ (Adm M).inf' (Adm_nonempty M) (Mval M) :=
    Finset.le_inf' _ _ (fun T' hT' => Mval_nonneg_adm M T' hT')
  have hle : (Adm M).inf' (Adm_nonempty M) (Mval M) ≤ 0 := hTval ▸ Finset.inf'_le _ hT
  have h0 : (Adm M).inf' (Adm_nonempty M) (Mval M) = 0 := le_antisymm hle hge
  unfold lambdaCore; rw [h0]; ring

/-- **`harith_base` — the degenerate-child base.** When the child `schurStateRed M` is a leaf,
`lambdaCore (schurStateRed M) = 0`, so `lambdaCore M = bindNReg M / 2`. The `#70`-base level (one above the
degenerate leaf): the recursion stops, the node's value is its own `nReg/2`. -/
theorem bind_harith_base (M : Fin (L + 1) → ℕ) (hleaf : isLeafNode (schurStateRed M)) :
    lambdaCore M = bindNReg M / 2 := by
  rw [bind_harith_step M, lambdaCore_eq_zero_of_isLeafNode _ hleaf, add_zero]

/-- **`hdrop` — well-foundedness.** `Σ (schurStateRed M) < Σ M` at a non-leaf node. The `schurState`
precondition `hlo` (the pivot widths `≥ 1`) is `schurState_hlo_of_not_isLeafNode`; the drop is the banked
`ChainDimSplit.redM_widthSum_lt` (via `chainWidthSum_schurStateRed_lt`). -/
theorem bind_hdrop {L' : ℕ} (M : Fin (L' + 1 + 1) → ℕ) (hnonleaf : ¬ isLeafNode M) :
    ∑ i, schurStateRed M i < ∑ i, M i :=
  chainWidthSum_schurStateRed_lt M (schurState_hlo_of_not_isLeafNode M hnonleaf)

/-- **`hlam` — `lambdaCore ≥ 0`.** `lambdaCore M = ½·inf' Mval ≥ 0` (admissible `Mval ≥ 0` ⟹ `inf' ≥ 0`). -/
theorem bind_hlam (M : Fin (L + 1) → ℕ) : 0 ≤ lambdaCore M := by
  unfold lambdaCore
  have hge : 0 ≤ (Adm M).inf' (Adm_nonempty M) (Mval M) :=
    Finset.le_inf' _ _ (fun T hT => Mval_nonneg_adm M T hT)
  positivity

/-- **`hnReg` — `bindNReg ≥ 0`** (the one genuine obligation). `bindNReg M = 2·(λ M − λ (schurStateRed M))
≥ 0 ⟺ λ (schurStateRed M) ≤ λ M` — the monotonicity of `lambdaCore` under the `schurState` width-reduction
(`hMono`, the achiever-transfer: the reduced node's minimal codim does not exceed `M`'s). Carried as the
named hypothesis until certified (the genuine recursion-arithmetic obligation; the anchors confirm it). -/
theorem bind_hnReg (M : Fin (L + 1) → ℕ)
    (hMono : lambdaCore (schurStateRed M) ≤ lambdaCore M) :
    0 ≤ bindNReg M := by
  unfold bindNReg; linarith

end DLNFibre.DLN.RLCT
