import DLNFibre.DLN.RLCT.Validate.RouteMBoundaryCleanMinAdm

/-!
# `RouteMSmearedMinAdm` — the smeared-boundary `minAdm` identity (`minAdm = deepRank · M_L`)

The arithmetic the boundary-SMEARED chart's determinant consumes: for a boundary `M`
(`NoInteriorBothDrop`), `minAdm M = deepRank M · M (Fin.last L) = r·c`, the rank-carrying-block entry
count, with `r = deepRank` (NOT `deepRows` — the smeared spectator rows do not contribute). This is the
analog of the clean `minAdm_eq_deepRows_mul_last`, but it needs NO clean hypothesis: the last Aoyagi block
is `deepRank·M_L` unconditionally (`rBlock_cBlock_last`), and the interior blocks vanish under
`NoInteriorBothDrop`. In the clean case `deepRank = deepRows` so the two identities coincide; in the
smeared case `deepRank < deepRows`, and THIS is the correct one — the radial blow-up of the chart blows
up exactly `r·c = minAdm` deepest coords (the rank block), giving det `|z|^{minAdm−1}`.
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators

variable {L : ℕ}

/-- **The smeared/boundary `minAdm` identity**: `minAdm M = deepRank M · M (Fin.last L) = r·c`, given only
`NoInteriorBothDrop` (the interior Aoyagi blocks vanish). The last block is `deepRank·M_L`
(`rBlock_cBlock_last`, unconditional); no clean hypothesis. The `active.card = minAdm` fact the smeared
radial blow-up's det exponent `minAdm−1` consumes (the `r·c` rank-block coords). -/
theorem minAdm_eq_deepRank_mul_last (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hNo : NoInteriorBothDrop M) :
    minAdm M = deepRank M * M (Fin.last L) := by
  have hsum := sum_rBlock_cBlock_eq_minAdm M
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
  rw [hsplit, rBlock_cBlock_last M hL] at hsum
  have : (minAdm M : ℤ) = (deepRank M : ℤ) * (M (Fin.last L) : ℤ) := hsum.symm
  exact_mod_cast this

end DLNFibre.DLN.RLCT
