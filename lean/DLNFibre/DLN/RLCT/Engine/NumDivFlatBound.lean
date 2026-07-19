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

**Accounting.** Each `stepAppendAdvance` (case-1(2)/case-2) does `numDiv += 1, cleared += 1`;
`stepCase11` and `stepRollover` leave `numDiv` fixed (`stepRollover` resets `cleared := 0`,
`layer += 1`). The threaded invariant `NumDivInv` bundles the budget bound `numDiv ≤ budgetSum layer +
cleared` (`budgetSum layer = ∑_{i<layer} widthMinUpto M (i+1)`, the per-layer pivot counts), the
companion `cleared ≤ widthMinUpto M (layer+1)` (= `MSp1`), `layer ≤ L`, and `layer = L → cleared = 0`.
From it, `numDiv ≤ flatDim` at EVERY reachable state: at `layer < L`, `numDiv ≤ budgetSum layer +
cleared ≤ budgetSum (layer+1) ≤ budgetSum L ≤ flatDim`; at `layer = L`, `cleared = 0` so `numDiv ≤
budgetSum L ≤ flatDim`. So the leaf `numDiv = (t0Indices s).length ≤ s.numDiv ≤ flatDim` needs no
chooser-totality (it survives even the off-cone terminal fallback).
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open scoped BigOperators

variable {L : ℕ}

/-! ## The arithmetic core (self-contained; no reachability) -/

/-- `widthMinUpto M n ≤ M i` for any head index `i ≤ n` (the running-min through layer `n` is `≤`
every width it mins over). -/
theorem widthMinUpto_le {M : Fin (L + 1) → ℕ} {n : ℕ} (i : Fin (L + 1))
    (hi : (i : ℕ) ≤ n) : widthMinUpto M n ≤ M i :=
  Finset.inf'_le M (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)

/-- **The arithmetic core**: the per-layer pivot counts sum to at most the flat dimension —
`∑_{i : Fin L} widthMinUpto M (i+1) ≤ flatDim M`. Each `widthMinUpto M (i+1) ≤ min(M i.castSucc,
M i.succ) ≤ M i.castSucc · M i.succ`, the `i`-th `flatDim` term. -/
theorem sum_widthMinUpto_le_flatDim (M : Fin (L + 1) → ℕ) :
    ∑ i : Fin L, widthMinUpto M ((i : ℕ) + 1) ≤ flatDim M := by
  rw [flatDim_eq]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have ha : widthMinUpto M ((i : ℕ) + 1) ≤ M i.castSucc :=
    widthMinUpto_le i.castSucc (by simp)
  have hb : widthMinUpto M ((i : ℕ) + 1) ≤ M i.succ :=
    widthMinUpto_le i.succ (by simp)
  rcases Nat.eq_zero_or_pos (M i.succ) with h0 | hpos
  · rw [h0, Nat.mul_zero]; omega
  · exact le_trans ha (Nat.le_mul_of_pos_right _ hpos)

/-- The per-layer pivot-count budget through `layer`: `∑_{i < layer} widthMinUpto M (i+1)`. -/
def budgetSum (M : Fin (L + 1) → ℕ) (layer : ℕ) : ℕ :=
  ∑ i ∈ Finset.range layer, widthMinUpto M (i + 1)

theorem budgetSum_succ (M : Fin (L + 1) → ℕ) (layer : ℕ) :
    budgetSum M (layer + 1) = budgetSum M layer + widthMinUpto M (layer + 1) :=
  Finset.sum_range_succ _ _

theorem budgetSum_mono (M : Fin (L + 1) → ℕ) {a b : ℕ} (h : a ≤ b) :
    budgetSum M a ≤ budgetSum M b := by
  unfold budgetSum
  refine Finset.sum_le_sum_of_subset (fun x hx => ?_)
  exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) h)

/-- `budgetSum M L ≤ flatDim M` — the full budget is at most the flat dimension (the leaf closer). -/
theorem budgetSum_le_flatDim (M : Fin (L + 1) → ℕ) : budgetSum M L ≤ flatDim M := by
  rw [budgetSum, ← Fin.sum_univ_eq_sum_range (fun i => widthMinUpto M (i + 1)) L]
  exact sum_widthMinUpto_le_flatDim M

/-! ## The threaded invariant -/

/-- **The `numDiv`-accounting invariant** threaded down the construction: the budget bound, the
per-layer companion `cleared ≤ MSp1`, `layer ≤ L`, and the terminal `layer = L → cleared = 0`. -/
def NumDivInv (M : Fin (L + 1) → ℕ) (s : ConState L) : Prop :=
  s.numDiv ≤ budgetSum M s.layer + s.cleared ∧
    s.cleared ≤ widthMinUpto M (s.layer + 1) ∧
      s.layer ≤ L ∧ (s.layer = L → s.cleared = 0)

/-- `NumDivInv` at the root (`numDiv = cleared = layer = 0`). -/
theorem NumDivInv_conRoot {M : Fin (L + 1) → ℕ} : NumDivInv M (conRoot : ConState L) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (0 : ℕ) ≤ budgetSum M 0 + 0; exact Nat.zero_le _
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · intro _; rfl

/-- **The state-level bound**: `NumDivInv` forces `numDiv ≤ flatDim` at every reachable state (leaf or
not). At `layer < L` via the companion + budget monotonicity; at `layer = L` via `cleared = 0`. -/
theorem numDiv_le_flatDim_of_inv {M : Fin (L + 1) → ℕ} {s : ConState L} (h : NumDivInv M s) :
    s.numDiv ≤ flatDim M := by
  obtain ⟨hb, hc, hl, ht⟩ := h
  rcases Nat.lt_or_ge s.layer L with hlt | hge
  · calc s.numDiv ≤ budgetSum M s.layer + s.cleared := hb
      _ ≤ budgetSum M s.layer + widthMinUpto M (s.layer + 1) := by omega
      _ = budgetSum M (s.layer + 1) := (budgetSum_succ M s.layer).symm
      _ ≤ budgetSum M L := budgetSum_mono M (by omega)
      _ ≤ flatDim M := budgetSum_le_flatDim M
  · have hlE : s.layer = L := le_antisymm hl hge
    have hc0 : s.cleared = 0 := ht hlE
    calc s.numDiv ≤ budgetSum M s.layer + s.cleared := hb
      _ = budgetSum M L := by rw [hlE, hc0, Nat.add_zero]
      _ ≤ flatDim M := budgetSum_le_flatDim M

/-! ## State-level per-transition maintenance (given the dispatch guards) -/

/-- Case-1(1) merge leaves `layer`/`cleared`/`numDiv` unchanged — `NumDivInv` transfers by defeq. -/
theorem NumDivInv_stepCase11 {M : Fin (L + 1) → ℕ} (s : ConState L) (i : Fin s.numDiv)
    (h : NumDivInv M s) : NumDivInv M (s.stepCase11 i) := h

/-- Case-1(2)/case-2 append (`numDiv += 1, cleared += 1`, `layer` fixed) preserves `NumDivInv`, given
the append guards `cleared < MSp1` and `layer < L` (the `conOracle` non-terminal, non-rollover
branch). -/
theorem NumDivInv_stepAppendAdvance {M : Fin (L + 1) → ℕ} (s : ConState L) (e : ℕ) (t₀ : Fin L → ℕ)
    (hlive : s.layer < L) (hlt : s.cleared < widthMinUpto M (s.layer + 1)) (h : NumDivInv M s) :
    NumDivInv M (s.stepAppendAdvance e t₀) := by
  obtain ⟨hb, hc, hl, ht⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · show s.numDiv + 1 ≤ budgetSum M s.layer + (s.cleared + 1); omega
  · show s.cleared + 1 ≤ widthMinUpto M (s.layer + 1); omega
  · show s.layer ≤ L; exact hl
  · intro he; exact absurd (show s.layer = L from he) (Nat.ne_of_lt hlive)

/-- Rollover (`layer += 1, cleared := 0`, `numDiv` fixed) preserves `NumDivInv`, using the companion
`cleared ≤ MSp1` from the input invariant and `layer < L` (the `conOracle` rollover branch). -/
theorem NumDivInv_stepRollover {M : Fin (L + 1) → ℕ} (s : ConState L) (hlive : s.layer < L)
    (h : NumDivInv M s) : NumDivInv M s.stepRollover := by
  obtain ⟨hb, hc, hl, ht⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · show s.numDiv ≤ budgetSum M (s.layer + 1) + 0
    rw [budgetSum_succ]; omega
  · show (0 : ℕ) ≤ widthMinUpto M (s.layer + 1 + 1); exact Nat.zero_le _
  · show s.layer + 1 ≤ L; omega
  · intro _; rfl

/-! ## The `conOracle`-navigation maintenance (the isolated crux) + the fold -/

/-- **`NumDivInv` maintenance through `conOracle`'s step-children** — the crux. Navigating
`conOracle`'s dispatch (`EngineConstruction`): a `rolloverDecision` child is `stepRollover s`
(guard `layer < L`); a `case1Decision` child is `stepCase11 s f` or `stepAppendAdvance s _ _` (the
1(1)/1(2) edges, guards `layer < L`, `cleared < MSp1`); a `case2Decision` child is
`stepAppendAdvance s _ _` (same guards). Apply the matching state-level maintenance lemma. Mirrors
`MvalBoundaryInv_conOracle_stepChildren`.

PLAN: `cases`/`split` on the `conOracle` `dif`/`match` structure to obtain each `StepChild`'s
`.child` state + its guards (`h1 : ¬ L ≤ layer` ⟹ `layer < L`; the rollover `h2` gives
`MSp1 ≤ cleared`; the append branch gives `cleared < MSp1` via `not_le.mp h2`), then dispatch to
`NumDivInv_stepRollover` / `NumDivInv_stepCase11` / `NumDivInv_stepAppendAdvance`. -/
theorem NumDivInv_conOracle_stepChildren {M : Fin (L + 1) → ℕ} (s : ConState L)
    (inv : NumDivInv M s) (c : StepChild M s) (hc : c ∈ (conOracle M s).stepChildren) :
    NumDivInv M c.child := by
  sorry

/-- The leaf constructor's analytic count is at most the state's ledger count (`t0Indices` filters
`finRange numDiv`). -/
theorem leafOfState_numDiv_le (M : Fin (L + 1) → ℕ) (s : ConState L) :
    (leafOfState M s).numDiv ≤ s.numDiv := by
  unfold leafOfState
  split
  · simp only [t0Indices]
    exact le_trans (List.length_filter_le _ _) (by simp)
  · exact Nat.zero_le _

/-- **The `numDiv ≤ flatDim` reachability invariant over the built tree** (sub-gap-1 core): every leaf
carries at most `flatDim M` analytic (`t̃=0`) divisors, so its `divCoord : Fin numDiv → Fin (flatDim
M)` admits an injective assignment. Consumed by the ChartBridge injectivity clause. -/
theorem leaves_numDiv_le_flatDim_of_inv {M : Fin (L + 1) → ℕ} (s : ConState L) (inv : NumDivInv M s) :
    ∀ l ∈ ResolutionTree.leaves (buildTree M (conOracle M) s), l.numDiv ≤ flatDim M := by
  induction s using (conRel_wf M).induction with
  | _ s ih =>
    intro l hl
    cases hoc : conOracle M s with
    | terminal l' hleaf =>
      rw [buildTree_terminal M (conOracle M) s l' hleaf hoc] at hl
      simp only [ResolutionTree.leaves, List.mem_singleton] at hl
      subst hl
      rw [conOracle_terminal_leaf s hoc]
      exact le_trans (leafOfState_numDiv_le M s) (numDiv_le_flatDim_of_inv inv)
    | step node children hnode hlayer hstep =>
      rw [buildTree_step M (conOracle M) s node children hoc] at hl
      rw [ResolutionTree.leaves, edgesLeaves_eq, List.mem_flatMap] at hl
      obtain ⟨e, he, hle⟩ := hl
      rw [List.mem_map] at he
      obtain ⟨c, hc, rfl⟩ := he
      have hcstep : c ∈ (conOracle M s).stepChildren := by rw [hoc]; exact hc
      exact ih c.child c.hdesc (NumDivInv_conOracle_stepChildren s inv c hcstep) l hle

/-- **Sub-gap-1 headline**: every leaf of the built tree from the root carries at most `flatDim M`
analytic divisors. -/
theorem leaves_numDiv_le_flatDim (M : Fin (L + 1) → ℕ)
    (l : LeafData M)
    (hl : l ∈ ResolutionTree.leaves (buildTree M (conOracle M) (conRoot : ConState L))) :
    l.numDiv ≤ flatDim M :=
  leaves_numDiv_le_flatDim_of_inv conRoot NumDivInv_conRoot l hl

end DLNFibre.DLN.RLCT.Engine
