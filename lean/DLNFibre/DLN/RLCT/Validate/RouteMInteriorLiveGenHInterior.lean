import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveGenWire
import DLNFibre.DLN.RLCT.Validate.RouteMInteriorDeepRank0GenAtom

/-!
# `RouteMInteriorLiveGenHInterior` — the general-`L` interior `hInterior` obligation, ∀L

The CAPSTONE of the general-`L` interior branch of R1-LOWER: combines the two `deepRank`
sub-strata into the achiever-dispatch spine's `hInterior` slot, unconditionally on `InteriorDrop`.

The spine's obligation is `hInterior : ∀ _ : 2 ≤ L, InteriorDrop M → BoxDiverges M c' ε`. It is
discharged by casing on the deepest-factor rank `deepRank M : ℕ` (`Nat.eq_zero_or_pos`), a gap-free
overlap-free dichotomy:

* `0 < deepRank M` → `interiorLiveGen_hInterior_of_deepRank_pos` (the LIVE-leaf atom, in
  `RouteMInteriorLiveGenWire`);
* `deepRank M = 0` → `interiorLiveGen_hInterior_of_deepRank_zero` (the E-block re-pivot
  `deepRank = 0` atom, in `RouteMInteriorDeepRank0GenAtom`).

Both consumers have the identical conclusion shape
`∀ _ : 2 ≤ L, InteriorDrop M → BoxDiverges M c' ε` and the identical context hypotheses
`(hpos) (c') (hc') (ε) (hε)`, differing only in the deepRank condition they carry — so the casing
typechecks iff both consumers faithfully match the slot.

Axiom profile: inherits both atoms' footprint —
`[propext, Classical.choice, Quot.sound, monomial_rlct]` (clean-three + the single permitted S2
axiom `monomial_rlct`), no `sorryAx`.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The spine's `hInterior` slot, discharged ∀L unconditionally on `InteriorDrop`.** For any `M`
with `2 ≤ L` and `InteriorDrop M`, the achiever box integral diverges at any `c' ≥ ½·minAdm M`.
Cases on the deepest-factor rank `deepRank M`: the `0 < deepRank M` sub-stratum routes through the
LIVE-leaf atom (`interiorLiveGen_hInterior_of_deepRank_pos`), the `deepRank M = 0` sub-stratum
through the E-block re-pivot atom (`interiorLiveGen_hInterior_of_deepRank_zero`). This closes the
interior branch of R1-LOWER at general `L`. -/
theorem interiorLiveGen_hInterior (M : Fin (L + 1) → ℕ) (hpos : 1 ≤ minAdm M)
    (c' : NNReal) (hc' : (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε) :
    ∀ _ : 2 ≤ L, InteriorDrop M → BoxDiverges M c' ε := by
  rcases Nat.eq_zero_or_pos (deepRank M) with hdr | hdr
  · exact interiorLiveGen_hInterior_of_deepRank_zero M hdr hpos c' hc' ε hε
  · exact interiorLiveGen_hInterior_of_deepRank_pos M hdr hpos c' hc' ε hε

end DLNFibre.DLN.RLCT
