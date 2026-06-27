import DLNFibre.DLN.RLCT.Validate.RouteMBoundaryClass

/-!
# `RouteMBoundaryCleanMinAdm` — the clean-boundary `minAdm` identity (`minAdm = m1·M_L`)

The load-bearing arithmetic for the BOUNDARY-CLEAN ∀M chart: for a clean-boundary `M` the achiever
codimension `minAdm M` is exactly the deepest-factor entry count `deepRows M · M (Fin.last L) = m1·M_L`
(the whole deepest factor is the rank-carrying block; all other boundary contributions vanish).

This rests on the chain↔Aoyagi bridge `rBlock j = Text(j+1) − Text(j+2)`, `cBlock j = Wext(j+1) −
Text(j+2)` (both over ℤ, along the achiever path `tach M`), so the Aoyagi block `j` IS the chain
residual `r_{j+1}×c_{j+1}` at chain boundary `j+1`. The last Aoyagi block `j = L−1` carries
`rBlock(L−1)·cBlock(L−1) = Text(L)·M_L = deepRank·M_L`, and `deepRank = deepRows` for clean.

Reusable for the SMEARED tide too (it needs `minAdm = r·M_L` with `r = deepRank < deepRows`).
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators

variable {L : ℕ}

/-! ## The chain↔Aoyagi bridge: `rBlock`/`cBlock` in `Text`/`Wext` widths -/

/-- **`tPrev (tStar) j = Text(j+1)`** along the achiever path: `tPrev j = M0` (`j=0`) `= tStar(j−1)`
(`j>0`), and `Text(j+1) = tach j = (M0 / tStar(j−1))` matches both. -/
theorem tPrev_tStar_eq_Text (M : Fin (L + 1) → ℕ) (j : Fin L) :
    tPrev M (tStar M) j = (Text M (tach M) (j.val + 1) : ℤ) := by
  rw [tPrev, Text_tach_succ M j.val (by omega)]
  by_cases hj : j.val = 0
  · rw [if_pos hj]
    rw [show (⟨j.val, by omega⟩ : Fin (L + 1)) = (0 : Fin (L + 1)) from by apply Fin.ext; simp [hj]]
    rw [tach_zero]
  · rw [if_neg hj]
    rw [show (⟨j.val, by omega⟩ : Fin (L + 1)) = (⟨j.val - 1, by omega⟩ : Fin L).succ from by
      apply Fin.ext; simp [Fin.succ]; omega, tach_succ]

/-- **`tStar j = Text(j+2)`** along the achiever path (`tStar j = tach(j+1) = Text(j+2)`). -/
theorem tStar_eq_Text (M : Fin (L + 1) → ℕ) (j : Fin L) :
    (tStar M j : ℤ) = (Text M (tach M) (j.val + 2) : ℤ) := by
  rw [show j.val + 2 = (j.val + 1) + 1 by ring, Text_tach_succ M (j.val + 1) (by omega)]
  rw [show (⟨j.val + 1, by omega⟩ : Fin (L + 1)) = j.succ from by apply Fin.ext; simp [Fin.succ],
    tach_succ]

/-- **`rBlock j = Text(j+1) − Text(j+2)`** (the chain row-residual at boundary `j+1`). -/
theorem rBlock_eq_Text (M : Fin (L + 1) → ℕ) (j : Fin L) :
    rBlock M j = (Text M (tach M) (j.val + 1) : ℤ) - (Text M (tach M) (j.val + 2) : ℤ) := by
  rw [rBlock, tPrev_tStar_eq_Text, tStar_eq_Text]

/-- **`cBlock j = Wext(j+1) − Text(j+2)`** (the chain col-residual at boundary `j+1`). -/
theorem cBlock_eq_Wext (M : Fin (L + 1) → ℕ) (j : Fin L) :
    cBlock M j = (Wext M (j.val + 1) : ℤ) - (Text M (tach M) (j.val + 2) : ℤ) := by
  rw [cBlock, tStar_eq_Text, Wext_apply M (j.val + 1) (by omega),
    show (⟨j.val + 1, by omega⟩ : Fin (L + 1)) = j.succ from by apply Fin.ext; simp [Fin.succ]]

/-! ## The interior Aoyagi blocks vanish ⟺ no interior both-drop -/

/-- **The bare "no interior both-drop" boundary condition** (chain-native): every chain boundary
`s ∈ [1, L−1]` fails to drop both row and column rank. This is the direct hypothesis the `minAdm`
collapse consumes; it is the negation of the bare interior classifier (and equivalent on the validated
grid to `¬InteriorDrop`, the col-drop-tail form — the argmin exchange argument). -/
def NoInteriorBothDrop (M : Fin (L + 1) → ℕ) : Prop :=
  ∀ s, 1 ≤ s → s < L → ¬ (Text M (tach M) (s + 1) < Text M (tach M) s ∧
    Text M (tach M) (s + 1) < Wext M s)

/-- **An interior Aoyagi block `j < L−1` vanishes under `NoInteriorBothDrop`.** Its chain boundary is
`s = j+1 ∈ [1, L−1]`: `rBlock j = Text(s) − Text(s+1) ≥ 0`, `cBlock j = Wext(s) − Text(s+1) ≥ 0`, and
the product is `0` unless both are strict — which `NoInteriorBothDrop` forbids. -/
theorem rBlock_cBlock_interior_eq_zero (M : Fin (L + 1) → ℕ) (hNo : NoInteriorBothDrop M)
    (j : Fin L) (hj : j.val < L - 1) :
    rBlock M j * cBlock M j = 0 := by
  rw [rBlock_eq_Text, cBlock_eq_Wext,
    show j.val + 1 = j.val + 1 from rfl, show j.val + 2 = (j.val + 1) + 1 from by omega]
  set s := j.val + 1 with hs
  -- `s ∈ [1, L−1]`
  have hs1 : 1 ≤ s := by omega
  have hsL : s < L := by omega
  have hr0 : (0 : ℤ) ≤ rBlock M j := rBlock_nonneg M j
  have hc0 : (0 : ℤ) ≤ cBlock M j := cBlock_nonneg M j
  rw [rBlock_eq_Text, show j.val + 2 = s + 1 from by omega] at hr0
  rw [cBlock_eq_Wext, show j.val + 2 = s + 1 from by omega] at hc0
  -- `Text(s) ≥ Text(s+1)` and `Wext(s) ≥ Text(s+1)`; not both strict
  have hnb := hNo s hs1 hsL
  -- if the product were nonzero, both factors strict ⟹ both drops ⟹ contradiction
  by_contra hne
  apply hnb
  refine ⟨?_, ?_⟩
  · -- `Text(s+1) < Text(s)`: `rBlock = Text(s) − Text(s+1) > 0`
    have : (0 : ℤ) < (Text M (tach M) s : ℤ) - (Text M (tach M) (s + 1) : ℤ) := by
      rcases lt_or_eq_of_le hr0 with h | h
      · exact h
      · exfalso; apply hne; rw [← h]; ring
    exact_mod_cast by omega
  · have : (0 : ℤ) < (Wext M s : ℤ) - (Text M (tach M) (s + 1) : ℤ) := by
      rcases lt_or_eq_of_le hc0 with h | h
      · exact h
      · exfalso; apply hne; rw [← h]; ring
    exact_mod_cast by omega

/-! ## The clean `minAdm` collapse -/

/-- **`tStar (last) = 0`** (the achiever path ends at rank `0`; the `admPred` last-exponent condition). -/
theorem tStar_last_eq_zero (M : Fin (L + 1) → ℕ) (hL : 0 < L) :
    tStar M ⟨L - 1, by omega⟩ = 0 :=
  ((Finset.mem_filter.1 (tStar_mem M)).2.2.2) ⟨L - 1, by omega⟩ (by simp)

/-- **`Text (L+1) = 0`** along the achiever path (`Text(L+1) = tach L = tStar(L−1) = 0`). -/
theorem Text_Lsucc_eq_zero (M : Fin (L + 1) → ℕ) (hL : 0 < L) :
    Text M (tach M) (L + 1) = 0 := by
  rw [Text_tach_succ M L (by omega),
    show (⟨L, by omega⟩ : Fin (L + 1)) = (⟨L - 1, by omega⟩ : Fin L).succ from by
      apply Fin.ext; simp [Fin.succ]; omega, tach_succ, tStar_last_eq_zero M hL]

/-- **The last Aoyagi block is `deepRank · M_L`** (`rBlock(L−1)·cBlock(L−1) = Text(L)·M_L`; `Text(L+1)=0`). -/
theorem rBlock_cBlock_last (M : Fin (L + 1) → ℕ) (hL : 0 < L) :
    rBlock M ⟨L - 1, by omega⟩ * cBlock M ⟨L - 1, by omega⟩
      = (deepRank M : ℤ) * (M (Fin.last L) : ℤ) := by
  rw [rBlock_eq_Text, cBlock_eq_Wext]
  have hT2 : Text M (tach M) ((L - 1) + 2) = Text M (tach M) (L + 1) := by
    congr 1; omega
  have hT1 : Text M (tach M) ((L - 1) + 1) = Text M (tach M) L := by congr 1; omega
  rw [show ((⟨L - 1, by omega⟩ : Fin L).val) = L - 1 from rfl] at *
  rw [hT2, hT1, Text_Lsucc_eq_zero M hL]
  have hWL : Wext M ((L - 1) + 1) = M (Fin.last L) := by
    rw [show (L - 1) + 1 = L by omega, Wext_apply M L (by omega)]; rfl
  rw [hWL, deepRank]
  push_cast; ring

/-- **THE clean-boundary `minAdm` identity**: `minAdm M = deepRows M · M (Fin.last L) = m1·M_L`, given
`NoInteriorBothDrop` (interior blocks vanish) and the clean equality `deepRank M = deepRows M`. The whole
deepest factor is the rank-carrying block. -/
theorem minAdm_eq_deepRows_mul_last (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hNo : NoInteriorBothDrop M) (hclean : deepRank M = deepRows M) :
    minAdm M = deepRows M * M (Fin.last L) := by
  -- `(minAdm : ℤ) = ∑_j rBlock·cBlock`; collapse to the last block
  have hsum := sum_rBlock_cBlock_eq_minAdm M
  -- split off the last index `⟨L−1,_⟩`
  have hsplit : ∑ j : Fin L, rBlock M j * cBlock M j
      = rBlock M ⟨L - 1, by omega⟩ * cBlock M ⟨L - 1, by omega⟩ := by
    rw [← Finset.sum_subset (Finset.subset_univ {(⟨L - 1, by omega⟩ : Fin L)})]
    · rw [Finset.sum_singleton]
    · intro j _ hj
      have hjne : j ≠ ⟨L - 1, by omega⟩ := by simpa using hj
      have hjlt : j.val < L - 1 := by
        have := j.isLt
        rcases Nat.lt_or_ge j.val (L - 1) with h | h
        · exact h
        · exfalso; apply hjne; apply Fin.ext; simp; omega
      exact rBlock_cBlock_interior_eq_zero M hNo j hjlt
  rw [hsplit, rBlock_cBlock_last M hL, hclean] at hsum
  -- `(minAdm : ℤ) = deepRows · M_L`, cast back to ℕ
  have : (minAdm M : ℤ) = (deepRows M : ℤ) * (M (Fin.last L) : ℤ) := hsum.symm
  exact_mod_cast this

end DLNFibre.DLN.RLCT
