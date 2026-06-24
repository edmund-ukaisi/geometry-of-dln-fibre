import DLNFibre.DLN.RLCT.Validate.Case222RouteStep
import DLNFibre.DLN.RLCT.Validate.Case323RouteStep

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMNReg` — the per-node regular-block count `nReg` (G-a feed, #143)

The per-node `nReg` the G-a producer (`RouteMNodeDescent.ofNodePresentation`, fm3 #144) consumes: the count
of regular smooth-square (Morse) generators in the node's post-blow-up Schur presentation `flatCore w =
(∑_{i:p} ∑_{j:n} Erow_{ij}²) + (∑ (bcol·Erow + SΓ)²)` — the `Erow`/pivot-row block, count `|p|·|n|`
(`schur_node_loss_presentation`). The per-node RLCT splits `nReg/2 + rlctAtOn (dlnLoss S.red 0) 0`
(`schur_straighten_squeeze_of_data`), so `nReg` is the node's Morse contribution to the descent.

## Definition + the value-side cross-check (controller, 2026-06-23)

The STRUCTURAL count is `|p|·|n|` (the `Erow` block dims). The controller pinned the value-side identity it
MUST equal (fm3 verified numerically on 6 nodes): `nReg = minAdm M − minAdm (schurState-reduced M)` — the
drop in the minimal admissible codim across one `schurState` width-reduction step. We DEFINE `nRegOf` by this
value-side difference (total, no `hlo`) and CROSS-CHECK it lands on the anchors (`2` for `(2,2,2)`, `3` for
`(3,2,3)`); the structural `|p|·|n|` reading is the semantic meaning the descent's `flatCore` carries. The
two reconcile (monomial↔Morse bookkeeping); a disagreement would be a genuine seam bug to surface.

`schurStateRed M s = if s ≤ 1 then M s - 1 else M s` (the `schurState`-reduced widths, `SchurState`'s `red`,
written total here so `nRegOf` needs no non-leaf precondition).
-/

open scoped BigOperators
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- The `schurState`-reduced widths, total (drops the two pivot vertices `0,1` by `1`). Equals
`(schurState M hlo).red` at a non-leaf node; total so `nRegOf` is unconditional. -/
def schurStateRed (M : Fin (L + 1) → ℕ) : Fin (L + 1) → ℕ :=
  fun s => if s.val ≤ 1 then M s - 1 else M s

/-- `schurStateRed` agrees with `(schurState M hlo).red` at a non-leaf node. -/
theorem schurStateRed_eq_red (M : Fin (L + 1) → ℕ)
    (hlo : ∀ s : Fin (L + 1), s.val ≤ 1 → 1 ≤ M s) :
    schurStateRed M = (schurState M hlo).red := rfl

/-- **The per-node regular-block count `nReg`**: the drop in the minimal admissible codim across one
`schurState` step, `nReg = minAdm M − minAdm (schurStateRed M)` (controller-pinned value-side identity;
fm3-verified). The structural meaning is the `|p|·|n|` `Erow` generator count of
`schur_node_loss_presentation` — this difference is the value-side cross-check it must equal. Total. -/
def nRegOf (M : Fin (L + 1) → ℕ) : ℕ :=
  ((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat
    - ((Adm (schurStateRed M)).inf' (Adm_nonempty (schurStateRed M)) (Mval (schurStateRed M))).toNat

/-! ## The anchor cross-check (controller's guard against a wrong count)

`(2,2,2) ↦ 2`, `(3,2,3) ↦ 3` — the controller's required values (fm3-verified). Proved via the committed
single-`inf'` `minAdm` lemmas (`minAdm_M222 = 3`, `minAdm_M323 = 5`) + the reduced-width `minAdm` (each a
single `inf'` `decide`, matching the committed-anchor feasibility), NOT one double-`inf'` `decide`. If these
failed, the structural `|p|·|n|` and the value-side `minAdm`-difference would disagree (the seam bug to
surface). They agree. -/

/-- `schurStateRed (2,2,2) = (1,1,2)` (the `schurState`-reduced `(2,2,2)` node). -/
theorem schurStateRed_M222 : schurStateRed M222route = ![1, 1, 2] := by
  funext s; fin_cases s <;> rfl

/-- `schurStateRed (3,2,3) = (2,1,3)`. -/
theorem schurStateRed_M323 : schurStateRed M323route = ![2, 1, 3] := by
  funext s; fin_cases s <;> rfl

/-- `minAdm (1,1,2) = 1` (the `(2,2,2)`-reduced node's minimal codim; single `inf'`, `decide`). -/
theorem minAdm_M112 :
    ((Adm (![1, 1, 2] : Fin 3 → ℕ)).inf' (Adm_nonempty (![1, 1, 2] : Fin 3 → ℕ))
      (Mval (![1, 1, 2] : Fin 3 → ℕ))).toNat = 1 := by decide

/-- `minAdm (2,1,3) = 2` (the `(3,2,3)`-reduced node's minimal codim; single `inf'`, `decide`). -/
theorem minAdm_M213 :
    ((Adm (![2, 1, 3] : Fin 3 → ℕ)).inf' (Adm_nonempty (![2, 1, 3] : Fin 3 → ℕ))
      (Mval (![2, 1, 3] : Fin 3 → ℕ))).toNat = 2 := by decide

/-- `nRegOf (2,2,2) = 2`: `minAdm (2,2,2) − minAdm (1,1,2) = 3 − 1`. The `(2,2,2)` node's `Erow` block is
`2×1` (`nReg = 2`), matching `schur_straighten_squeeze_of_data`'s `2/2` Morse share at this node. -/
theorem nRegOf_M222 : nRegOf M222route = 2 := by
  have h2 : ((Adm (schurStateRed M222route)).inf' (Adm_nonempty (schurStateRed M222route))
      (Mval (schurStateRed M222route))).toNat = 1 := by rw [schurStateRed_M222]; exact minAdm_M112
  unfold nRegOf
  rw [minAdm_M222, h2]

/-- `nRegOf (3,2,3) = 3`: `minAdm (3,2,3) − minAdm (2,1,3) = 5 − 2`. The asymmetric anchor's value-side
count, matching the controller's cross-check. -/
theorem nRegOf_M323 : nRegOf M323route = 3 := by
  have h2 : ((Adm (schurStateRed M323route)).inf' (Adm_nonempty (schurStateRed M323route))
      (Mval (schurStateRed M323route))).toNat = 2 := by rw [schurStateRed_M323]; exact minAdm_M213
  unfold nRegOf
  rw [minAdm_M323, h2]

/-! ## The recursion arithmetic — the facts `binding_from_O1_and_leaf` assumes (controller, 2026-06-23)

fm3's `binding_from_O1_and_leaf` skeleton consumes combinatorial facts about `minAdm`/`nRegOf` along the
`schurState` descent (the binding-path telescope). Stated here in their natural form; the exact-signature
match to fm3's `harith_step`/`harith_base`/`hdrop` is a trivial final rearrangement (ring/omega — controller's
call, not a substantive blocker). `minAdm M = ((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat` (inline). -/

/-- **Well-foundedness — `ΣM` strictly drops along `schurState`.** `Σ (schurStateRed M) < Σ M` at a non-leaf
node (where `schurStateRed = (schurState M hlo).red`). The strong-induction / `WellFounded.fix` measure of the
descent. Reuses the banked `ChainDimSplit.redM_widthSum_lt` (the `ΣM`-drop). -/
theorem chainWidthSum_schurStateRed_lt (M : Fin (L + 1) → ℕ)
    (hlo : ∀ s : Fin (L + 1), s.val ≤ 1 → 1 ≤ M s) :
    chainWidthSum (schurStateRed M) < chainWidthSum M := by
  rw [schurStateRed_eq_red M hlo]
  exact (schurState M hlo).redM_widthSum_lt

/-- **The per-step telescope identity** `minAdm (schurStateRed M) + nRegOf M = minAdm M` — the local step the
binding-path telescope `Σ nReg_k = minAdm M` iterates (terminal degenerate child has `minAdm = 0`). Holds when
the reduced node's minimal codim does not exceed `M`'s (`hmono`), so the `nRegOf` ℕ-subtraction is exact. The
`hmono` hypothesis is the monotonicity `minAdm (schurStateRed M) ≤ minAdm M` (its own lemma below). -/
theorem minAdm_schurStateRed_add_nRegOf (M : Fin (L + 1) → ℕ)
    (hmono : ((Adm (schurStateRed M)).inf' (Adm_nonempty (schurStateRed M)) (Mval (schurStateRed M))).toNat
        ≤ ((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat) :
    ((Adm (schurStateRed M)).inf' (Adm_nonempty (schurStateRed M)) (Mval (schurStateRed M))).toNat + nRegOf M
      = ((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat := by
  -- `nRegOf M = minAdm M − minAdm(red)`; with `hmono : minAdm(red) ≤ minAdm M`, the ℕ-subtraction is exact.
  rw [nRegOf]
  -- goal: minAdm(red) + (minAdm M − minAdm(red)) = minAdm M
  exact Nat.add_sub_cancel' hmono

end DLNFibre.DLN.RLCT
