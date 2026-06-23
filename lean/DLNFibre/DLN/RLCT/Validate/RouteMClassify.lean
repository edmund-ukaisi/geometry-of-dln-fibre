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

/-- **Each `Mval` summand is nonnegative on `Adm`** (the per-term building block). For `T ∈ Adm M`,
the `j`-th summand `(tPrev_j − T_j)(M_{j+1} − T_j) ≥ 0`: the first factor by weak-decrease
(`tPrev_0 = M_0 ≥ T_0` from `T_0 ≤ min(M_0,M_1) ≤ M_0`; `tPrev_j = T_{j−1} ≥ T_j`), the second by the
block bound (`T_j ≤ admBound_j ≤ M_{j+1}`). The reusable lever toward the sharper `∃ s, M_s = 0`
characterization (the `Mval = 0 ⟹` every summand `= 0` step). -/
theorem Mval_summand_nonneg (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : T ∈ Adm M) (j : Fin L) :
    0 ≤ (tPrev M T j - (T j : ℤ)) * ((M j.succ : ℤ) - (T j : ℤ)) := by
  rw [Adm, Finset.mem_filter] at hT
  obtain ⟨_, hbound, hdecr, _⟩ := hT
  apply mul_nonneg
  · rw [sub_nonneg]
    simp only [tPrev]
    by_cases hj : j.val = 0
    · simp only [hj, if_true]
      have hb := hbound j
      simp only [admBound, hj, if_true] at hb
      exact_mod_cast le_trans hb (min_le_left _ _)
    · simp only [hj, if_false]
      have hle : (⟨j.val - 1, by omega⟩ : Fin L) ≤ j := by simp only [Fin.le_def]; omega
      exact_mod_cast hdecr ⟨j.val - 1, by omega⟩ j hle
  · rw [sub_nonneg]
    have hb := hbound j
    simp only [admBound] at hb
    by_cases hj : j.val = 0
    · simp only [hj, if_true] at hb
      have hm1 : T j ≤ M 1 := le_trans hb (min_le_right _ _)
      have h1 : M 1 = M j.succ := by
        congr 1; apply Fin.ext
        rw [Fin.val_succ, hj, Fin.val_one', Nat.mod_eq_of_lt (by have := j.pos; omega)]
      rw [h1] at hm1; exact_mod_cast hm1
    · simp only [hj, if_false] at hb
      exact_mod_cast hb

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

/-- **Positivity below the boundary: an all-widths-positive node has every admissible codim `≥ 1`.** If
`1 ≤ M_s` for all `s` (a chain of length `≥ 2`), then `0 < Mval M T` for every `T ∈ Adm M`. Proof: each
`Mval` summand is `≥ 0` (`Mval_summand_nonneg`), so `Mval = 0` would force every summand `= 0`; the last
summand (`T_{L-1} = 0` by admissibility, `M_L ≥ 1`) then forces `tPrev_{L-1} = T_{L-2} = 0`, and a downward
`Fin.reverseInduction` propagates `T ≡ 0`, whence `Mval M T = M_0 · M_1 ≥ 1 ≠ 0` (`Mval_zeroT_eq`) — a
contradiction. The "no interior leaf" fidelity content (`⇒` of pp2's `minAdm = 0 ⟺ ∃ s, M_s = 0`). -/
theorem Mval_pos_of_all_width_pos {L' : ℕ} (M : Fin (L' + 1 + 1) → ℕ) (T : Fin (L' + 1) → ℕ)
    (hT : T ∈ Adm M) (hpos : ∀ s, 1 ≤ M s) : 0 < Mval M T := by
  rcases lt_or_eq_of_le (Mval_nonneg_adm M T hT) with h | h
  · exact h
  · exfalso
    -- `Mval M T = 0`: every summand vanishes; downward-propagate `T ≡ 0`, then `Mval = M_0·M_1 ≥ 1`.
    have hMval : Mval M T = 0 := h.symm
    have hnn : ∀ j ∈ Finset.univ, (0 : ℤ) ≤
        (tPrev M T j - (T j : ℤ)) * ((M j.succ : ℤ) - (T j : ℤ)) :=
      fun j _ => Mval_summand_nonneg M T hT j
    have hsum : ∑ j, (tPrev M T j - (T j : ℤ)) * ((M j.succ : ℤ) - (T j : ℤ)) = 0 := by
      rw [← hMval]; rfl
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum
    have hadm := hT
    rw [Adm, Finset.mem_filter] at hadm
    obtain ⟨_, _, _, hlast⟩ := hadm
    have hTlast : T (Fin.last L') = 0 := hlast _ (by simp [Fin.last])
    have hTzero : ∀ j : Fin (L' + 1), T j = 0 := by
      intro j
      induction j using Fin.reverseInduction with
      | last => exact hTlast
      | cast i ih =>
        have hsz := hzero i.succ (Finset.mem_univ _)
        have htp : tPrev M T i.succ = (T i.castSucc : ℤ) := by
          simp only [tPrev]
          rw [if_neg (by simp [Fin.succ] : (i.succ).val ≠ 0)]
          have hidx : (⟨(i.succ).val - 1, by omega⟩ : Fin (L' + 1)) = i.castSucc := by
            apply Fin.ext; simp [Fin.succ]
          rw [hidx]
        rw [htp, ih] at hsz
        simp only [Nat.cast_zero, sub_zero] at hsz
        have hMpos : (1 : ℤ) ≤ (M i.succ.succ : ℤ) := by exact_mod_cast hpos i.succ.succ
        have hcast : (T i.castSucc : ℤ) = 0 := by
          rcases mul_eq_zero.mp hsz with h' | h'
          · exact h'
          · omega
        exact_mod_cast hcast
    rw [funext hTzero, Mval_zeroT_eq] at hMval
    have h0 : (1 : ℤ) ≤ M 0 := by exact_mod_cast hpos 0
    have h1 : (1 : ℤ) ≤ M 1 := by exact_mod_cast hpos 1
    nlinarith [h0, h1]

/-- **The leaf forces a collapsed width** (the `⇒` of pp2's degenerate-boundary characterization). A leaf
node (`minAdm M = 0`) has some width `M_s = 0` (a chain of length `≥ 2`). Contrapositive of
`Mval_pos_of_all_width_pos`: if every width were `≥ 1`, every admissible codim would be `≥ 1`, so the
minimal admissible codim could not be `0`. The load-bearing fidelity direction — a node the recursion
declares a leaf genuinely has no positive-codim stratum because a width has collapsed (not a premature
stop). -/
theorem exists_width_zero_of_isLeafNode {L' : ℕ} (M : Fin (L' + 1 + 1) → ℕ) (h : isLeafNode M) :
    ∃ s, M s = 0 := by
  by_contra hcon
  push_neg at hcon
  have hpos : ∀ s, 1 ≤ M s := fun s => Nat.one_le_iff_ne_zero.mpr (hcon s)
  obtain ⟨T, hT, hTval⟩ := (isLeafNode_iff_exists_zero M).mp h
  exact absurd hTval (by have := Mval_pos_of_all_width_pos M T hT hpos; omega)

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
