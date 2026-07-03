import DLNFibre.DLN.RLCT.Validate.RouteMSmearedSpineWire
import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveGenHInterior

/-!
# `RouteMAchieverFull` — the general-`L` achiever box-divergence with ALL branches discharged, ∀L

The CAPSTONE of R1-LOWER's achiever leg. The 4-way dispatch spine
(`routeMCore_box_diverges_achiever_spine`, `RouteMAchieverDispatch`) owes three open branch atoms
plus the boundary-clean structural side-conditions. All three atoms are now closed at general `L`:

* `L = 0` / `L = 1` — handled inside the spine (vacuity / always-boundary-clean).
* the BOUNDARY-CLEAN branch — the banked `routeMCore_box_diverges_clean`, threaded inside the spine
  from the structural side-conditions.
* the INTERIOR branch — `interiorLiveGen_hInterior` (`RouteMInteriorLiveGenHInterior`), the two
  `deepRank` sub-strata combined, unconditional on `InteriorDrop`.
* the BOUNDARY-SMEARED branch — `hSmeared_smearedClose` (`RouteMSmearedClose`), fully unconditional
  ∀L, deriving all structural data from `BoundarySmeared ∧ NoInteriorBothDrop ∧ 1 ≤ minAdm`.

Supplying the two slot-dischargers to the spine collapses the achiever box-divergence to the
structural side-conditions the caller establishes per `M` (`hMpos` — all widths positive; `hne` —
the deepest block nonempty; `hNo` — no interior both-drop). This is
`routeMCore_box_diverges_achiever_full`: the general-`L` R1-LOWER achiever `hdiv`, complete for
every `L` given `hNo`.

`hNo` (`NoInteriorBothDrop M`) is carried as a hypothesis: the achiever value leg genuinely lives on
the `NoInteriorBothDrop` stratum (the interior Aoyagi blocks vanish), and the R1-resolution assembly
provides it downstream (a hypothesis on `M`, or the general `¬InteriorDrop → NoInteriorBothDrop`
bridge; the L = 2 leg threads it).

Axiom profile: `[propext, Classical.choice, Quot.sound, monomial_rlct]`. The single permitted S2
citation `monomial_rlct` enters through the interior slot (via `interiorLiveGen_hInterior`'s
box-divergence atoms); the smeared slot is clean-three (S2-free, single-axis after shear), and the
spine adds none of its own.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The general-`L` achiever box-divergence, ALL branches discharged (the R1-LOWER `hdiv` ∀L).**
For any `M : Fin (L+1) → ℕ` with `1 ≤ minAdm M`, all widths positive (`hMpos`), the deepest block
nonempty at every positive `L` (`hne`), and no interior both-drop (`hNo`), the achiever box integral
diverges at any `c' ≥ ½·minAdm M` and any `ε > 0`. Assembled by feeding the dispatch spine its two
open slot-dischargers — the interior `interiorLiveGen_hInterior` and the smeared
`hSmeared_smearedClose` — with the clean branch handled inside the spine. Conditional only on `hNo`
(the achiever stratum) and the clean structural side-conditions; complete for every `L`. -/
theorem routeMCore_box_diverges_achiever_full (M : Fin (L + 1) → ℕ) (hpos : 1 ≤ minAdm M)
    (hMpos : ∀ s, 0 < M s)
    (hne : ∀ hL : 0 < L, (deepestCoords M hL).Nonempty)
    (hNo : NoInteriorBothDrop M)
    (c' : NNReal) (hc' : (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε) :
    BoxDiverges M c' ε :=
  routeMCore_box_diverges_achiever_spine M hpos c' hc' ε hε hMpos hne hNo
    (interiorLiveGen_hInterior M hpos c' hc' ε hε)
    (hSmeared_smearedClose M hpos c' hc' ε hε)

end DLNFibre.DLN.RLCT
