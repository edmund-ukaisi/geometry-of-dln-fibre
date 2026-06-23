import DLNFibre.DLN.RLCT.Validate.RouteMRecursion
import DLNFibre.DLN.RLCT.Validate.SchurState
import DLNFibre.DLN.RLCT.Validate.ResolutionAtlas

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMClassify` — the `routeStep` leaf classifier (fm3, sub-1)

The terminal-node test for the general `routeStep` dispatcher (`RouteMRecursion.routeStep`), built as a
standalone, decidable building block. A node `M` is a **leaf** exactly when its minimal admissible codim
`minAdm M = ((Adm M).inf' Mval).toNat` is `0`: no positive-codim pivot stratum remains, so the residual
core is a unit and the chain has bottomed out. This is the dispatcher's piece (1) — the residual rank-defect
classifier — stated honestly: it is NOT "no `schurState` applies" (the `(2,2,0)`-style nodes still admit a
`schurState` split yet have `minAdm = 0`, so they ARE leaves), and it is non-vacuous (`(2,2,2)` has
`minAdm = 3 > 0`, so it is NOT a leaf — avoiding the docstring's trap (i), leaf-everywhere).

The leaf datum is `leafMonoData 0` (the empty `d = 0` base, threshold `⊤`): a unit leaf carries no monomial,
so it never binds the cover `⨅`; the value comes from the pivot divisors appended ABOVE it on the path
(`MonoData.appendDivisor`). `leafThreshold_eq_top` records this. This file does NOT touch the `routeStep`
`sorry` — it banks the leaf arm for sub-3's assembly.
-/

open scoped BigOperators ENNReal
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The leaf test**: `M` is a leaf iff its minimal admissible codim is `0` (no positive-codim pivot
stratum remains — the residual core is a unit). The honest terminal classifier (dispatcher piece (1)):
when `minAdm M = 0`, every admissible `T` gives `Mval M T = 0`, so there is no genuine blow-up to perform
and the recursion stops. Decidable (`Adm`/`Mval` concrete). -/
def isLeafNode (M : Fin (L + 1) → ℕ) : Prop :=
  ((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat = 0

instance (M : Fin (L + 1) → ℕ) : Decidable (isLeafNode M) := by
  unfold isLeafNode; infer_instance

/-! ## The leaf-fidelity characterization (the base-case gate)

The leaf test `isLeafNode M` (a decidable proxy) is the recursion's BASE CASE — load-bearing, so it
must EXACTLY capture the geometric leaf. The geometric leaf is "no positive-codim pivot stratum remains":
there is an admissible rank-pattern `T ∈ Adm M₀` of codim `Mval M T = 0` (the trivial / no-blow-up
stratum is the minimiser). `isLeafNode_iff_exists_zero` pins the exact `⟺`, and the proof rests on
`Mval ≥ 0` on `Adm` (`Mval_nonneg_adm`): the minimal codim is `0` iff some admissible stratum attains
codim `0`. NON-VACUOUS: `Mval M (fun _ => 0)` is NOT always `0` (`= 4` on `(2,2,2)`), so the RHS
genuinely fails on branch nodes and holds on terminal ones — the test is neither always-leaf nor
never-leaf. -/

/-- **The leaf-fidelity characterization (EXACT).** `M` is a leaf (`minAdm M = 0`) **iff** there is an
admissible rank-pattern `T ∈ Adm M` of codim `Mval M T = 0` — the geometric leaf "no positive-codim pivot
stratum remains". The exact base-case pin: `Mval ≥ 0` on `Adm` (`Mval_nonneg_adm`) makes the minimal codim
`0` exactly when some admissible stratum attains `0`. (The `⟹` rides `Finset.exists_mem_eq_inf'` — the inf
is achieved; the `⟸` rides `Finset.inf'_le` + nonnegativity.) -/
theorem isLeafNode_iff_exists_zero (M : Fin (L + 1) → ℕ) :
    isLeafNode M ↔ ∃ T ∈ Adm M, Mval M T = 0 := by
  unfold isLeafNode
  -- `Mval ≥ 0` on `Adm`, so `inf' Mval ≥ 0`; hence `(inf' Mval).toNat = 0 ↔ inf' Mval = 0`.
  have hge : 0 ≤ (Adm M).inf' (Adm_nonempty M) (Mval M) :=
    Finset.le_inf' _ _ (fun T hT => Mval_nonneg_adm M T hT)
  rw [Int.toNat_eq_zero]
  constructor
  · intro hle
    -- `inf' ≤ 0` and `inf' ≥ 0` give `inf' = 0`, achieved at some `T ∈ Adm M`.
    have heq : (Adm M).inf' (Adm_nonempty M) (Mval M) = 0 := le_antisymm hle hge
    obtain ⟨T, hT, hTval⟩ := Finset.exists_mem_eq_inf' (Adm_nonempty M) (Mval M)
    exact ⟨T, hT, by rw [← hTval, heq]⟩
  · rintro ⟨T, hT, hTval⟩
    -- a zero-codim admissible stratum drives the inf to `≤ 0`.
    calc (Adm M).inf' (Adm_nonempty M) (Mval M) ≤ Mval M T := Finset.inf'_le _ hT
      _ = 0 := hTval

/-- **The leaf arm of the dispatcher.** At a leaf node the chart carries the empty `d = 0` monomial datum
`leafMonoData 0` (threshold `⊤`): no monomial of its own, the value rides the divisors appended above. The
`RouteStep.leaf` constructor, root-anchored trivially (a leaf carries no codim/witness — those live on the
branch cells above). -/
def leafStep (M₀ M : Fin (L + 1) → ℕ) : RouteStep M₀ M :=
  .leaf (leafMonoData 0)

/-- **The leaf datum's threshold is `⊤`.** The leaf imposes no monomial threshold, so it never binds the
cover `⨅` — the per-leaf value comes entirely from the pivot divisors accumulated above it. (Restates
`leafMonoData_threshold` at the leaf-arm datum, the contract sub-3 relies on.) -/
theorem leafStep_threshold :
    monomialThreshold (leafMonoData 0).d (leafMonoData 0).k (leafMonoData 0).h = ⊤ :=
  leafMonoData_threshold 0

/-! ### The degenerate-boundary base case (pp2 #109 g233: `minAdm = 0 ⟺ ∃ s, M_s = 0`)

pp2's decorrelated cert (g232, 1360 M, zero mismatches) sharpens the geometric leaf to the **degenerate
boundary** `∃ s, M_s = 0` (a width-0 layer bottlenecks the chain through rank 0). `Mval_zeroT_eq` computes
the all-zeros stratum's codim `Mval M 0 = M_0 · M_1` (the two pivot widths), which gives the recursion's
ACTUAL base case directly: a collapsed pivot vertex (`M_0 = 0` or `M_1 = 0`) is a leaf. The full
`∃ s, M_s = 0` ⟺ (including interior `M_{≥2} = 0`) is pp2's sharper form (the interior witness saturates to
the wall); pp2 refuted the `M_0 = 0 ∨ M_1 = 0` form as the FULL characterization — it is sufficient (proven
here) but misses interior-zero leaves like `(2,2,0)` (caught instead by `isLeafNode_iff_exists_zero`). -/

/-- **The all-zeros stratum codim is the pivot-width product** `Mval M (fun _ => 0) = M_0 · M_1` (for
chains of length `≥ 2`). The `tPrev`-vanishing computation: with `T ≡ 0`, `tPrev_j = 0` for `j ≥ 1` and
`tPrev_0 = M_0`, so only the `j = 0` summand `(M_0)(M_1)` survives. The recursion's base-case codim — `0`
exactly when a pivot vertex has collapsed. -/
theorem Mval_zeroT_eq {L' : ℕ} (M : Fin (L' + 1 + 1) → ℕ) :
    Mval M (fun _ => 0) = (M 0 : ℤ) * (M 1 : ℤ) := by
  unfold Mval
  have hsummand : ∀ j : Fin (L' + 1),
      (tPrev M (fun _ => 0) j - ((fun _ => 0 : Fin (L' + 1) → ℕ) j : ℤ))
      * ((M j.succ : ℤ) - ((fun _ => 0 : Fin (L' + 1) → ℕ) j : ℤ))
      = if j = 0 then (M 0 : ℤ) * (M 1 : ℤ) else 0 := by
    intro j
    simp only [tPrev]
    by_cases hj : j.val = 0
    · have hj0 : j = 0 := Fin.ext hj
      subst hj0
      have hsucc : (0 : Fin (L' + 1)).succ = (1 : Fin (L' + 1 + 1)) := by
        apply Fin.ext; simp [Fin.succ, Nat.mod_eq_of_lt]
      simp only [Fin.val_zero, Nat.cast_zero, sub_zero, hsucc, if_true]
    · have hjne : j ≠ 0 := fun h => hj (by rw [h]; rfl)
      rw [if_neg hj, if_neg hjne]; simp
  rw [Finset.sum_congr rfl (fun j _ => hsummand j),
    Finset.sum_ite_eq' Finset.univ (0 : Fin (L' + 1)) (fun _ => (M 0 : ℤ) * (M 1 : ℤ))]
  simp

/-- **A collapsed pivot vertex makes the node a leaf** (the recursion's base case). If `M_0 = 0` or
`M_1 = 0` (a chain of length `≥ 2`), the all-zeros stratum has codim `Mval M 0 = M_0 · M_1 = 0`, so `M` is
a leaf. This is what the `schurState` descent reaches (it decrements `M_0, M_1` each step until one hits
`0`); a SUFFICIENT leaf condition, not the full characterization (interior `M_{≥2} = 0` leaves are caught
by `isLeafNode_iff_exists_zero`). -/
theorem isLeafNode_of_pivot_width_zero {L' : ℕ} (M : Fin (L' + 1 + 1) → ℕ)
    (h : M 0 = 0 ∨ M 1 = 0) : isLeafNode M := by
  refine (isLeafNode_iff_exists_zero M).mpr ⟨(fun _ => 0), zero_mem_Adm M, ?_⟩
  rw [Mval_zeroT_eq]
  rcases h with h0 | h1
  · rw [h0]; simp
  · rw [h1]; simp

/-- **Branch direction (the "too-weak" guard).** If every admissible stratum has positive codim
(`0 < Mval M T` for all `T ∈ Adm M`), then `M` is NOT a leaf — the recursion does not stop early. The
contrapositive of `isLeafNode_iff_exists_zero`: a positive-codim-everywhere node is a genuine branch.
This is the load-bearing fidelity direction (declaring a leaf with a positive-codim stratum remaining
would stop the recursion early and undershoot the value). -/
theorem not_isLeafNode_of_all_pos (M : Fin (L + 1) → ℕ)
    (hpos : ∀ T ∈ Adm M, 0 < Mval M T) : ¬ isLeafNode M := by
  rw [isLeafNode_iff_exists_zero]
  rintro ⟨T, hT, hTval⟩
  exact absurd hTval (by have := hpos T hT; omega)

/-- **Leaf direction (the "too-strong" guard).** If some admissible stratum has codim `0`, then `M` IS a
leaf — the recursion does not over-run past the terminal node. Restates the `⟸` of
`isLeafNode_iff_exists_zero` in usable form. -/
theorem isLeafNode_of_exists_zero (M : Fin (L + 1) → ℕ)
    (h : ∃ T ∈ Adm M, Mval M T = 0) : isLeafNode M :=
  (isLeafNode_iff_exists_zero M).mpr h

/-! ## Non-vacuity anchors — the classifier separates genuine branches from terminal leaves -/

/-- `(2,2,2)` is NOT a leaf (`minAdm = 3 > 0`): the dispatcher must branch on it. Guards against the
docstring's trap (i) — leaf-everywhere would make the atlas trivial (threshold `⊤ ≠ ½·minAdm`). -/
theorem not_isLeafNode_M222 : ¬ isLeafNode (fun _ => 2 : Fin 3 → ℕ) := by decide

/-- A bottomed-out node `(0,0,2)` IS a leaf (`minAdm = 0`): both pivot vertices have collapsed, no stratum
left. The terminal case the recursion descends to. -/
theorem isLeafNode_collapsed : isLeafNode (![0, 0, 2] : Fin 3 → ℕ) := by decide

/-- `(2,2,0)` IS a leaf (`minAdm = 0`) **even though** `schurState` would still apply (both pivot vertices
are `≥ 1`): the leaf test is `minAdm = 0`, NOT "no `schurState` applies". This is the load-bearing fidelity
point — a `schurState`-driven recursion that stopped only when the split fails would over-pivot here. -/
theorem isLeafNode_degenerate_tail : isLeafNode (![2, 2, 0] : Fin 3 → ℕ) := by decide

end DLNFibre.DLN.RLCT
