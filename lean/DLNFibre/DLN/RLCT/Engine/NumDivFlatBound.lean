import DLNFibre.DLN.RLCT.Engine.EngineConstruction

/-!
# `DLNFibre.DLN.RLCT.Engine.NumDivFlatBound` — the `numDiv ≤ flatDim` reachability invariant (sub-gap-1)

The count of `t̃=0` analytic divisors at any leaf of the built tree is at most the ambient flat
dimension `flatDim M`, so an INJECTIVE `divCoord : Fin numDiv → Fin (flatDim M)` exists (pigeonhole).
This is the spine-safe, type-INDEPENDENT half of sub-gap-1 (RULINGS-t04 §1): the bound the ChartBridge
`Function.Injective divCoord` clause needs, whether ChartBridge reads the ledger leaf's `divCoord`
(frozen type) or an atlas piece's `divCoord` sharing that leaf's ledger content (the corrected
flat-atlas type — see `threads/11-construction/decision-package-chartbridge-type.md`).

**Battery-verified** (`threads/11-construction/battery/numdiv-le-flatdim.py`): the bound holds across
the mechanism-aware kill-set + a 1360-instance width sweep, and is TIGHT at all-`1` widths
(`numDiv = L = flatDim`). Tightness is why a loose bound cannot suffice; the proof is an exact
divisor-accounting argument.

**Accounting (the invariant, plan for `leaves_numDiv_le_flatDim`).** Each `stepAppendAdvance`
(case-1(2)/case-2) does `numDiv += 1, cleared += 1`; `stepCase11` and `stepRollover` leave `numDiv`
fixed (`stepRollover` resets `cleared := 0`, `layer += 1`). So over the reachable cone

    numDiv ≤ (∑_{i : Fin L, i < layer} widthMinUpto M (i+1)) + cleared

is preserved: `stepAppendAdvance` adds one to both sides; `stepCase11` touches neither; `stepRollover`
needs the COMPANION bound `cleared ≤ widthMinUpto M (layer+1)` (= `MSp1`, the per-layer pivot count),
so the budget does not shrink when the layer's term rolls in. At a leaf (`layer = L`, `cleared = 0`)
this reads `numDiv ≤ ∑_{i : Fin L} widthMinUpto M (i+1)`, and `sum_widthMinUpto_le_flatDim` closes it
against `flatDim M = ∑ M(i.castSucc)·M(i.succ)`.

The companion `cleared ≤ widthMinUpto M (layer+1)` holds because `stepAppendAdvance` fires only when
`cleared < widthMinUpto M (layer+1)` (the `classify` non-rollover branch), so `cleared + 1 ≤ MSp1`.
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open scoped BigOperators

variable {L : ℕ}

/-- `widthMinUpto M n ≤ M i` for any head index `i ≤ n` (the running-min through layer `n` is `≤`
every width it mins over). -/
theorem widthMinUpto_le {M : Fin (L + 1) → ℕ} {n : ℕ} (i : Fin (L + 1))
    (hi : (i : ℕ) ≤ n) : widthMinUpto M n ≤ M i :=
  Finset.inf'_le M (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)

/-- **The arithmetic core**: the per-layer pivot counts sum to at most the flat dimension —
`∑_{i : Fin L} widthMinUpto M (i+1) ≤ flatDim M`. Each `widthMinUpto M (i+1) ≤ min(M i.castSucc,
M i.succ) ≤ M i.castSucc · M i.succ`, the `i`-th `flatDim` term. This is the leaf-level closer of the
`numDiv ≤ flatDim` accounting; it is fully self-contained (no reachability). -/
theorem sum_widthMinUpto_le_flatDim (M : Fin (L + 1) → ℕ) :
    ∑ i : Fin L, widthMinUpto M ((i : ℕ) + 1) ≤ flatDim M := by
  rw [flatDim_eq]
  refine Finset.sum_le_sum (fun i _ => ?_)
  -- `w ≤ a` and `w ≤ b`, so `w ≤ a * b` (case on `b = 0`)
  have ha : widthMinUpto M ((i : ℕ) + 1) ≤ M i.castSucc :=
    widthMinUpto_le i.castSucc (by simp)
  have hb : widthMinUpto M ((i : ℕ) + 1) ≤ M i.succ :=
    widthMinUpto_le i.succ (by simp)
  rcases Nat.eq_zero_or_pos (M i.succ) with h0 | hpos
  · rw [h0, Nat.mul_zero]; omega
  · exact le_trans ha (Nat.le_mul_of_pos_right _ hpos)

/-- **The `numDiv ≤ flatDim` reachability invariant** (sub-gap-1 core): every leaf of the built tree
carries at most `flatDim M` analytic (`t̃=0`) divisors, so its `divCoord : Fin numDiv → Fin (flatDim
M)` admits an injective assignment. Consumed by the ChartBridge injectivity clause (frozen leaf
`divCoord`, or the corrected atlas-piece `divCoord` sharing this leaf's ledger content).

PLAN (see the module docstring): the divisor-accounting invariant `numDiv ≤ (∑_{i<layer} widthMinUpto
M (i+1)) + cleared` threaded through `conOracle`'s step-children (reusing the
`MvalBoundaryInv_conOracle_stepChildren` pattern), with the companion `cleared ≤ widthMinUpto M
(layer+1)`, folded at leaves (`layer = L`, `cleared = 0`) through `sum_widthMinUpto_le_flatDim`. -/
theorem leaves_numDiv_le_flatDim (M : Fin (L + 1) → ℕ) (l : LeafData M)
    (hl : l ∈ ResolutionTree.leaves (buildTree M (conOracle M) (conRoot : ConState L))) :
    l.numDiv ≤ flatDim M := by
  sorry

end DLNFibre.DLN.RLCT.Engine
