import DLNFibre.DLN.RLCT.Validate.RouteMBoundaryCleanMinAdm

/-!
# `RouteMDeepBottleneck` — the achiever bottleneck `deepRank ≤ deepRows` (∀M, 2≤L)

The keystone the ∀M achiever-chart 4-way trichotomy rests on. `RouteMBoundaryClass`'s totality
(`interiorDrop_or_boundaryClean_or_boundarySmeared`, `boundaryClean_or_boundarySmeared`) carries the
achiever-path bottleneck `r ≤ m1` — i.e. `deepRank M ≤ deepRows M` — as an UNPROVEN hypothesis
`hle`, validated only numerically (46/46 + 20/20 on the design grid). This file PROVES it ∀M
(`2 ≤ L`) from the banked admissibility `tStar_le_Msucc` (`tStar M j ≤ M j.succ`), closing the gate.

* `deepRank` = `Text M (tach M) L` (the compressed rank flowing into the deepest factor along the
  achiever path); `deepRows` = `Wext M (L−1) = M (L−1)` (the deepest factor's row count).
* The proof: at `j = ⟨L−2⟩ : Fin L`, `tStar_eq_Text` gives `deepRank = Text(L) = tStar j`, and the
  admissibility bound `tStar j ≤ M j.succ = M ⟨L−1⟩ = Wext (L−1) = deepRows`.

So the achiever path NEVER carries more rank into the deepest factor than that factor has rows — the
`r ≤ m1` bottleneck is a structural consequence of admissibility, not a numeric coincidence.

`achiever_trichotomy_total` then states the 4-way (post-`L=1`) split is UNCONDITIONALLY total for
`2 ≤ L`. **This does NOT yet discharge `hle` into `RouteMBoundaryClass`** (a separate wiring step);
it banks the lemma the wiring will consume. (Imports `RouteMBoundaryCleanMinAdm` for the banked
`tStar_eq_Text` bridge; that file sits downstream of `RouteMBoundaryClass`, so `deepRank`/`deepRows`
come transitively — no re-definition.)

Axiom-clean `[propext, Classical.choice, Quot.sound]` (admissibility arithmetic; no analysis/S2).
-/

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The achiever-path deepest-factor bottleneck `deepRank M ≤ deepRows M`** (`2 ≤ L`): the rank
flowing into the deepest factor along the achiever path is at most that factor's row count. At
`j = ⟨L−2⟩ : Fin L`, `deepRank = Text(L) = tStar j` (`tStar_eq_Text`, since `(L−2)+2 = L`) and
`tStar j ≤ M j.succ = M ⟨L−1⟩ = Wext (L−1) = deepRows` (`tStar_le_Msucc` at the admissible
`tStar M ∈ Adm M`). This is the structural fact `RouteMBoundaryClass`'s trichotomy carries as the
unproven `hle` hypothesis. -/
theorem deepRank_le_deepRows (M : Fin (L + 1) → ℕ) (hL2 : 2 ≤ L) :
    deepRank M ≤ deepRows M := by
  -- the boundary index `j = ⟨L−2⟩ : Fin L`
  have hjlt : L - 2 < L := by omega
  set j : Fin L := ⟨L - 2, hjlt⟩ with hj
  -- `deepRank M = tStar M j`: `deepRank = Text(L)`, and `Text((L−2)+2) = Text(L)`, `= tStar j`
  have hdr : deepRank M = tStar M j := by
    have hidx : j.val + 2 = L := by simp only [hj]; omega
    have heqT : (tStar M j : ℤ) = (Text M (tach M) (j.val + 2) : ℤ) := tStar_eq_Text M j
    rw [hidx] at heqT
    have : (deepRank M : ℤ) = (tStar M j : ℤ) := by rw [deepRank]; exact heqT.symm
    exact_mod_cast this
  -- the admissibility bound `tStar M j ≤ M j.succ`
  have hle : (tStar M j : ℤ) ≤ (M j.succ : ℤ) := tStar_le_Msucc M (tStar M) (tStar_mem M) j
  -- `M j.succ = M ⟨L−1⟩ = Wext (L−1) = deepRows M`
  have hsucc : M j.succ = deepRows M := by
    rw [deepRows, Wext_apply M (L - 1) (by omega)]
    congr 1; apply Fin.ext; simp only [Fin.val_succ, hj]; omega
  rw [hdr]
  have hfin : (tStar M j : ℤ) ≤ (deepRows M : ℤ) := by rw [← hsucc]; exact hle
  exact_mod_cast hfin

/-- **The 4-way (post-`L=1`) achiever trichotomy is UNCONDITIONALLY total for `2 ≤ L`** — every `M`
is at least one of INTERIOR, BOUNDARY-CLEAN, BOUNDARY-SMEARED. `deepRank_le_deepRows` discharges the
`hle` hypothesis of `interiorDrop_or_boundaryClean_or_boundarySmeared`, so the exhaustiveness gate
the ∀M achiever-chart assembly rests on is closed (bounded admissibility arithmetic, not a wall). -/
theorem achiever_trichotomy_total (M : Fin (L + 1) → ℕ) (hL2 : 2 ≤ L) :
    InteriorDrop M ∨ BoundaryClean M ∨ BoundarySmeared M :=
  interiorDrop_or_boundaryClean_or_boundarySmeared M (deepRank_le_deepRows M hL2)

end DLNFibre.DLN.RLCT
