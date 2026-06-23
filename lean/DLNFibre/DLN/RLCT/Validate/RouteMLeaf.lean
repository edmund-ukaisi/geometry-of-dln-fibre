import DLNFibre.DLN.RLCT.Validate.ResolutionAtlas

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMLeaf` — the leaf classifier (UPSTREAM of `routeStep`)

The terminal-node test for the general `routeStep` dispatcher, placed UPSTREAM of `RouteMRecursion` so the
dispatcher can consume it (the classifier is logically upstream of the dispatcher that branches on it). A
node `M` is a **leaf** exactly when its minimal admissible codim `minAdm M = ((Adm M).inf' Mval).toNat` is
`0`: no positive-codim pivot stratum remains. This file is `RouteStep`-free (it depends only on
`Adm`/`Mval`/`Mval_nonneg_adm`), so `RouteMRecursion` imports it; the `RouteStep`-valued leaf ARM
(`leafStep`) + the decide-anchors live downstream in `RouteMClassify`.

The full geometric characterization (`isLeafNode M ⟺ ∃ s, M_s = 0`, the degenerate boundary; pp2 #109 g233)
and the branch-precondition bridge (`schurState_hlo_of_not_isLeafNode`: a non-leaf node has the pivot
widths `≥ 1`) are here — both consumed by the dispatcher.
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
  have hge : 0 ≤ (Adm M).inf' (Adm_nonempty M) (Mval M) :=
    Finset.le_inf' _ _ (fun T hT => Mval_nonneg_adm M T hT)
  rw [Int.toNat_eq_zero]
  constructor
  · intro hle
    have heq : (Adm M).inf' (Adm_nonempty M) (Mval M) = 0 := le_antisymm hle hge
    obtain ⟨T, hT, hTval⟩ := Finset.exists_mem_eq_inf' (Adm_nonempty M) (Mval M)
    exact ⟨T, hT, by rw [← hTval, heq]⟩
  · rintro ⟨T, hT, hTval⟩
    calc (Adm M).inf' (Adm_nonempty M) (Mval M) ≤ Mval M T := Finset.inf'_le _ hT
      _ = 0 := hTval

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
`Mval_pos_of_all_width_pos`. -/
theorem exists_width_zero_of_isLeafNode {L' : ℕ} (M : Fin (L' + 1 + 1) → ℕ) (h : isLeafNode M) :
    ∃ s, M s = 0 := by
  by_contra hcon
  push_neg at hcon
  have hpos : ∀ s, 1 ≤ M s := fun s => Nat.one_le_iff_ne_zero.mpr (hcon s)
  obtain ⟨T, hT, hTval⟩ := (isLeafNode_iff_exists_zero M).mp h
  exact absurd hTval (by have := Mval_pos_of_all_width_pos M T hT hpos; omega)

/-! ### The interior-zero witness (the `⇐` of the degenerate-boundary form)

The converse `∃ s, M_s = 0 ⟹ isLeafNode M` needs an explicit admissible stratum of codim `0` even when the
collapsed width is interior (`M_{≥2} = 0`). The **prefix-min witness** `witT M j = ⨅_{i ≤ j+1} M_i` does it:
`Mval M witT = 0` UNCONDITIONALLY (each summand telescopes), and the witness is admissible exactly when some
width is `0`. -/

/-- The telescoping identity `(a − min a b)(b − min a b) = 0` over `ℤ` — the per-summand vanishing. -/
theorem sub_min_mul_sub_min_zero (a b : ℤ) : (a - min a b) * (b - min a b) = 0 := by
  rcases le_total a b with h | h
  · rw [min_eq_left h]; ring
  · rw [min_eq_right h]; ring

/-- The **prefix-min witness** `witT M j = ⨅_{i ∈ Iic j.succ} M_i` (running rank-bottleneck through index
`j+1`). The explicit admissible-stratum witness for the interior-zero leaf. -/
noncomputable def witT (M : Fin (L + 1) → ℕ) : Fin L → ℕ :=
  fun j => (Finset.Iic j.succ).inf' Finset.nonempty_Iic M

/-- The predecessor prefix `prefInf M j = ⨅_{i ∈ Iic j.castSucc} M_i` (through index `j`) — equals
`tPrev M witT j`. -/
noncomputable def prefInf (M : Fin (L + 1) → ℕ) (j : Fin L) : ℕ :=
  (Finset.Iic j.castSucc).inf' Finset.nonempty_Iic M

/-- `witT_j = min(prefInf_j, M_{j+1})` (split `Iic j.succ = insert j.succ (Iic j.castSucc)`). -/
theorem witT_eq_min (M : Fin (L + 1) → ℕ) (j : Fin L) :
    witT M j = min (prefInf M j) (M j.succ) := by
  unfold witT prefInf
  have hins : Finset.Iic j.succ = insert j.succ (Finset.Iic j.castSucc) := by
    ext x
    simp only [Finset.mem_Iic, Finset.mem_insert]
    constructor
    · intro hx
      rcases eq_or_lt_of_le hx with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [Fin.le_castSucc_iff]; exact h)
    · rintro (rfl | hx)
      · exact le_refl _
      · exact le_trans hx (Fin.castSucc_le_succ j)
  rw [show (Finset.Iic j.succ).inf' Finset.nonempty_Iic M
      = (insert j.succ (Finset.Iic j.castSucc)).inf'
          (by rw [← hins]; exact Finset.nonempty_Iic) M from by congr 1, Finset.inf'_insert]
  exact min_comm _ _

/-- `tPrev M witT j = prefInf_j`: `j = 0 ↦ M_0` (the `Iic 0 = {0}` inf); `j ≥ 1 ↦ witT_{j-1}` (and
`(j-1).succ = j.castSucc`). -/
theorem tPrev_witT_eq_prefInf (M : Fin (L + 1) → ℕ) (j : Fin L) :
    tPrev M (witT M) j = (prefInf M j : ℤ) := by
  simp only [tPrev]
  by_cases hj : j.val = 0
  · rw [if_pos hj]
    unfold prefInf
    have hcs : j.castSucc = (0 : Fin (L + 1)) := by apply Fin.ext; simp [hj]
    simp only [hcs, show Finset.Iic (0 : Fin (L + 1)) = {0} from by
      ext x; simp [Finset.mem_Iic, Fin.le_zero_iff], Finset.inf'_singleton]
  · rw [if_neg hj]
    unfold witT prefInf
    norm_cast
    have hidx : (⟨j.val - 1, by omega⟩ : Fin L).succ = j.castSucc := by
      apply Fin.ext; simp only [Fin.val_succ, Fin.coe_castSucc]; omega
    simp only [hidx]

/-- **`Mval M witT = 0` unconditionally** — every summand telescopes to `0`
(`sub_min_mul_sub_min_zero`). -/
theorem Mval_witT_eq_zero {L' : ℕ} (M : Fin (L' + 1 + 1) → ℕ) : Mval M (witT M) = 0 := by
  unfold Mval
  apply Finset.sum_eq_zero
  intro j _
  rw [tPrev_witT_eq_prefInf, witT_eq_min, Nat.cast_min]
  exact sub_min_mul_sub_min_zero (prefInf M j : ℤ) (M j.succ : ℤ)

/-- `witT_j ≤ M_{j+1}` (`j.succ ∈ Iic j.succ`). -/
theorem witT_le_succ (M : Fin (L + 1) → ℕ) (j : Fin L) : witT M j ≤ M j.succ :=
  Finset.inf'_le _ (Finset.mem_Iic.2 le_rfl)

/-- `witT` is weakly decreasing (`Iic i.succ ⊆ Iic j.succ` for `i ≤ j`). -/
theorem witT_anti (M : Fin (L + 1) → ℕ) {i j : Fin L} (h : i ≤ j) : witT M j ≤ witT M i := by
  unfold witT
  exact Finset.inf'_mono (f := M) (Finset.Iic_subset_Iic.2 (Fin.succ_le_succ_iff.2 h))
    Finset.nonempty_Iic

/-- `witT_0 ≤ min(M_0, M_1) = admBound_0` (`0, 1 ∈ Iic (0.succ = 1)`). -/
theorem witT_zero_le {L' : ℕ} (M : Fin (L' + 1 + 1) → ℕ) :
    witT M (0 : Fin (L' + 1)) ≤ min (M 0) (M 1) := by
  apply le_min
  · exact Finset.inf'_le _ (Finset.mem_Iic.2 (by simp))
  · refine Finset.inf'_le _ (Finset.mem_Iic.2 ?_)
    have : (0 : Fin (L' + 1)).succ = (1 : Fin (L' + 1 + 1)) := by apply Fin.ext; simp
    rw [this]

/-- A collapsed width drives the last exponent to `0`: `witT (last) = ⨅ over the full chain = 0`. -/
theorem witT_last_eq_zero {L' : ℕ} (M : Fin (L' + 1 + 1) → ℕ) (s : Fin (L' + 1 + 1)) (hs : M s = 0) :
    witT M (Fin.last L') = 0 := by
  apply Nat.le_zero.1
  refine le_trans (Finset.inf'_le M (Finset.mem_Iic.2 ?_)) (le_of_eq hs)
  exact le_trans (Fin.le_last s) (by rw [Fin.succ_last])

/-- **The prefix-min witness is admissible** when a width has collapsed: weak-decrease (`witT_anti`),
block bound (`witT_le_succ` / `witT_zero_le`), and the last exponent `0` (`witT_last_eq_zero`). -/
theorem witT_mem_Adm {L' : ℕ} (M : Fin (L' + 1 + 1) → ℕ) (s : Fin (L' + 1 + 1)) (hs : M s = 0) :
    witT M ∈ Adm M := by
  have hbd : ∀ j : Fin (L' + 1), witT M j ≤ admBound M j := by
    intro j
    simp only [admBound]
    by_cases hj : j.val = 0
    · simp only [hj, if_true]
      have hj0 : j = 0 := Fin.ext hj
      rw [hj0]; exact witT_zero_le M
    · simp only [hj, if_false]; exact witT_le_succ M j
  rw [Adm, Finset.mem_filter]
  refine ⟨?_, hbd, ?_, ?_⟩
  · rw [Fintype.mem_piFinset]; intro j; rw [Finset.mem_range]; have := hbd j; omega
  · intro a b hab; exact witT_anti M hab
  · intro j hj
    have hjlast : j = Fin.last L' := by apply Fin.ext; simp [Fin.val_last, hj]
    rw [hjlast]; exact witT_last_eq_zero M s hs

/-- **The interior-zero `⇐`**: a collapsed width yields an admissible stratum of codim `0` (the prefix-min
witness). With `exists_width_zero_of_isLeafNode` (the `⇒`), this closes the full degenerate-boundary
characterization `isLeafNode_iff_width_zero`. -/
theorem exists_admissible_Mval_zero {L' : ℕ} (M : Fin (L' + 1 + 1) → ℕ)
    (s : Fin (L' + 1 + 1)) (hs : M s = 0) : ∃ T ∈ Adm M, Mval M T = 0 :=
  ⟨witT M, witT_mem_Adm M s hs, Mval_witT_eq_zero M⟩

/-- **The full degenerate-boundary characterization (pp2 #109, EXACT).** A node is a leaf **iff** some
width has collapsed: `isLeafNode M ⟺ ∃ s, M_s = 0` (chains of length `≥ 2`). The sharpest geometric form —
the recursion bottoms exactly at the degenerate boundary. `⇒` is `exists_width_zero_of_isLeafNode` (no false
leaf); `⇐` is `exists_admissible_Mval_zero` (the prefix-min witness). (The leaf VALUE semantics — `leafMonoData
0` `⊤` non-binding terminator vs the `#70` degenerate-ROOT case — are pinned in
`RouteMState.foldFamily_iInf_eq_half_minAdm`'s docstring.) -/
theorem isLeafNode_iff_width_zero {L' : ℕ} (M : Fin (L' + 1 + 1) → ℕ) :
    isLeafNode M ↔ ∃ s, M s = 0 := by
  refine ⟨exists_width_zero_of_isLeafNode M, ?_⟩
  rintro ⟨s, hs⟩
  exact (isLeafNode_iff_exists_zero M).mpr (exists_admissible_Mval_zero M s hs)

/-- **A non-leaf node has all widths positive** (the branch's `schurState` precondition). A non-leaf `M`
(`¬ isLeafNode M`, i.e. `minAdm M ≠ 0`) has every width `≥ 1` (`isLeafNode_iff_width_zero` contrapositive),
so in particular the two pivot vertices `M_0, M_1 ≥ 1` — exactly `schurState`'s `hlo`. The bridge the
dispatcher's BRANCH arm rides: the recursion is entered only at a non-leaf node, where the C1/C5 `schurState`
split applies. -/
theorem schurState_hlo_of_not_isLeafNode {L' : ℕ} (M : Fin (L' + 1 + 1) → ℕ) (h : ¬ isLeafNode M) :
    ∀ s : Fin (L' + 1 + 1), s.val ≤ 1 → 1 ≤ M s := by
  intro s _
  by_contra hcon
  exact h ((isLeafNode_iff_width_zero M).mpr ⟨s, by omega⟩)

/-- **Branch direction (the "too-weak" guard).** If every admissible stratum has positive codim
(`0 < Mval M T` for all `T ∈ Adm M`), then `M` is NOT a leaf — the recursion does not stop early. -/
theorem not_isLeafNode_of_all_pos (M : Fin (L + 1) → ℕ)
    (hpos : ∀ T ∈ Adm M, 0 < Mval M T) : ¬ isLeafNode M := by
  rw [isLeafNode_iff_exists_zero]
  rintro ⟨T, hT, hTval⟩
  exact absurd hTval (by have := hpos T hT; omega)

/-- **Leaf direction (the "too-strong" guard).** If some admissible stratum has codim `0`, then `M` IS a
leaf. Restates the `⟸` of `isLeafNode_iff_exists_zero` in usable form. -/
theorem isLeafNode_of_exists_zero (M : Fin (L + 1) → ℕ)
    (h : ∃ T ∈ Adm M, Mval M T = 0) : isLeafNode M :=
  (isLeafNode_iff_exists_zero M).mpr h

/-! ## Non-vacuity anchors — the classifier separates genuine branches from terminal leaves -/

/-- `(2,2,2)` is NOT a leaf (`minAdm = 3 > 0`): the dispatcher must branch on it. -/
theorem not_isLeafNode_M222 : ¬ isLeafNode (fun _ => 2 : Fin 3 → ℕ) := by decide

/-- A bottomed-out node `(0,0,2)` IS a leaf (`minAdm = 0`): both pivot vertices have collapsed. -/
theorem isLeafNode_collapsed : isLeafNode (![0, 0, 2] : Fin 3 → ℕ) := by decide

/-- `(2,2,0)` IS a leaf (`minAdm = 0`) **even though** `schurState` would still apply (both pivot vertices
`≥ 1`): the leaf test is `minAdm = 0`, NOT "no `schurState` applies". -/
theorem isLeafNode_degenerate_tail : isLeafNode (![2, 2, 0] : Fin 3 → ℕ) := by decide

/-- The full characterization fires on an INTERIOR-zero node: `(3,0,3)` is a leaf via the `⇐` (the
prefix-min witness handles `M_1 = 0`). -/
theorem isLeafNode_interior_zero : isLeafNode (![3, 0, 3] : Fin 3 → ℕ) :=
  (isLeafNode_iff_width_zero _).mpr ⟨1, rfl⟩

/-! ## Gate 1 — the cascade-rank side-condition from admissibility (#121-(ii) support)

The cascade lemmas (`Core.CascadeRealizable.submult_cascade` / `rankPattern_cascade`) carry the hypothesis
`ht : ∀ p, t_p ≤ d_{p.castSucc}` (the block's surviving rank is `≤` its source width). For an ADMISSIBLE
exponent vector `T` (`admPred M T`, the §4 cone) this holds: `adm_le_width` DISCHARGES it from `admPred`,
so when the cascade is instantiated at an admissible `T` over width-vector `M`, the side-condition is free.
This is the HONEST cascade side-condition (decision-independent, from `admPred`'s block bound +
weak-decrease) — distinct from the general-branch construction (which is the named `sorry`). -/

/-- **Gate 1: admissibility discharges the cascade-rank bound** `T_p ≤ M_{p.castSucc}` (`= M_p`). For
`admPred M T`: `p = 0` ⟹ `T_0 ≤ admBound_0 = min(M_0, M_1) ≤ M_0` (`min_le_left`); `p ≥ 1` ⟹ by
weak-decrease `T_p ≤ T_{p-1} ≤ admBound_{p-1}`, which is `min(M_0,M_1) ≤ M_1 = M_{1.castSucc}` for `p = 1`
(`min_le_right`) and `M_p = M_{p.castSucc}` for `p ≥ 2`. The honest side-condition the cascade (`submult_cascade`)
consumes at an admissible exponent. -/
theorem adm_le_width {L : ℕ} (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : admPred M T) (p : Fin L) :
    T p ≤ M p.castSucc := by
  obtain ⟨hbound, hdecr, _⟩ := hT
  by_cases hp : p.val = 0
  · -- p = 0: T_0 ≤ min(M_0,M_1) ≤ M_0 = M_{0.castSucc}.
    have hb := hbound p
    simp only [admBound, hp, if_true] at hb
    have hcs : M p.castSucc = M 0 := by
      apply congrArg M; apply Fin.ext; rw [Fin.val_castSucc, hp]; rfl
    rw [hcs]; exact le_trans hb (min_le_left _ _)
  · -- p ≥ 1: T_p ≤ T_{p-1} ≤ admBound_{p-1}; split p=1 (min_le_right) vs p≥2 (rfl on the index).
    have hp1le : 1 ≤ p.val := by omega
    set q : Fin L := ⟨p.val - 1, by omega⟩ with hq
    have hqv : q.val = p.val - 1 := rfl
    have hqp : q ≤ p := by rw [Fin.le_def, hqv]; omega
    have hTq : T p ≤ T q := hdecr q p hqp
    have hbq := hbound q
    by_cases hq0 : q.val = 0
    · -- q = 0 (so p = 1): admBound_0 = min(M_0,M_1) ≤ M_1 = M_{1.castSucc}.
      simp only [admBound, hq0, if_true] at hbq
      have hpv1 : p.val = 1 := by rw [hqv] at hq0; omega
      have hp1 : M p.castSucc = M 1 := by
        apply congrArg M; apply Fin.ext
        rw [Fin.val_castSucc, hpv1, Fin.val_one', Nat.mod_eq_of_lt (by omega)]
      rw [hp1]; exact le_trans hTq (le_trans hbq (min_le_right _ _))
    · -- q ≥ 1 (p ≥ 2): admBound_q = M_{q.succ} = M_p = M_{p.castSucc}.
      simp only [admBound, hq0, if_false] at hbq
      have hidx : M q.succ = M p.castSucc := by
        apply congrArg M; apply Fin.ext; rw [Fin.val_succ, Fin.val_castSucc, hqv]; omega
      rw [← hidx]; exact le_trans hTq hbq

end DLNFibre.DLN.RLCT
