import DLNFibre.DLN.RLCT.Validate.RouteMAchieverFull
import DLNFibre.DLN.RLCT.Validate.RouteMHNoBridge

/-!
# `RouteMAchieverFullHNoFree` — the general-`L` achiever box-divergence WITHOUT `hNo`

`routeMCore_box_diverges_achiever_full` (`RouteMAchieverFull.lean`) carries `hNo :
NoInteriorBothDrop M` — consumed only in its CLEAN + SMEARED trichotomy branches (both reached under
`¬InteriorDrop`); the INTERIOR branch (`interiorLiveGen_hInterior`) is unconditional. This module
DROPS `hNo` from the caller-facing achiever by a bounded case split on `InteriorDrop M`, with NO edit
to the existing achiever_full or the dispatch:

* **`InteriorDrop M`** — routes straight through the unconditional interior branch
  `interiorLiveGen_hInterior` (its `2 ≤ L` premise is forced by `InteriorDrop`'s
  `∃ p, 1 ≤ p ∧ p < L`).
* **`¬InteriorDrop M`** — the bridge `noInteriorBothDrop_of_not_interiorDrop`
  (`RouteMHNoBridge.lean`) supplies `NoInteriorBothDrop M` from `0 < Wext M L` (= `M (Fin.last L)`,
  positive by `hMpos`), which feeds the existing `routeMCore_box_diverges_achiever_full`.

Neither branch cheats the case split: the InteriorDrop branch genuinely discharges via the interior
atom; the ¬InteriorDrop branch genuinely supplies `hNo` via the combinatorial bridge.

Axiom profile: inherits `routeMCore_box_diverges_achiever_full`'s footprint
`[propext, Classical.choice, Quot.sound, monomial_rlct]` — the bridge is clean-three (S2-free), so
`monomial_rlct` still enters only through the interior/value lane.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The general-`L` achiever box-divergence, `hNo`-FREE.** For any `M : Fin (L+1) → ℕ` with
`1 ≤ minAdm M`, all widths positive (`hMpos`), and the deepest block nonempty at every positive `L`
(`hne`), the achiever box integral diverges at any `c' ≥ ½·minAdm M` and any `ε > 0`. The
`NoInteriorBothDrop` hypothesis is DROPPED: the `InteriorDrop` case routes through the unconditional
interior branch, and the `¬InteriorDrop` case obtains `hNo` from the bridge. -/
theorem routeMCore_box_diverges_achiever_full' (M : Fin (L + 1) → ℕ) (hpos : 1 ≤ minAdm M)
    (hMpos : ∀ s, 0 < M s)
    (hne : ∀ hL : 0 < L, (deepestCoords M hL).Nonempty)
    (c' : NNReal) (hc' : (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε) :
    BoxDiverges M c' ε := by
  by_cases hID : InteriorDrop M
  · -- `InteriorDrop M` ⟹ the unconditional interior branch. `InteriorDrop` forces `2 ≤ L`
    -- (its witness `p` has `1 ≤ p ∧ p < L`), and the interior atom does not read `hNo`.
    have hL2 : 2 ≤ L := by
      obtain ⟨_, _, hp1, hpL, _, _⟩ := hID; omega
    exact interiorLiveGen_hInterior M hpos c' hc' ε hε hL2 hID
  · -- `¬InteriorDrop M` ⟹ the bridge supplies `hNo`, then the existing achiever_full.
    have hWL : 0 < Wext M L := by rw [Wext_apply M L (by omega)]; exact hMpos _
    exact routeMCore_box_diverges_achiever_full M hpos hMpos hne
      (noInteriorBothDrop_of_not_interiorDrop M hWL hID) c' hc' ε hε

end DLNFibre.DLN.RLCT
