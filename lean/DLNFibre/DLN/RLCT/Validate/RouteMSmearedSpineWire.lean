import DLNFibre.DLN.RLCT.Validate.RouteMSmearedClose
import DLNFibre.DLN.RLCT.Validate.RouteMAchieverDispatch

/-!
# `RouteMSmearedSpineWire` — the smeared branch discharges the ∀M achiever spine's `hSmeared` slot

The co-import test: pull BOTH the smeared-Gen DECODE chain (`RouteMSmearedClose`, via the renamed
`deepLayerS`) and the ∀M achiever dispatch spine (`RouteMAchieverDispatch`, whose clean branch pulls
`RouteMBoundaryCleanChart`'s `deepLayer M hL`) into one environment. Post the `deepLayer → deepLayerS`
rename (Flag 2) these co-import cleanly; before it they collided (`environment already contains
DLNFibre.DLN.RLCT.deepLayer`).

`routeMCore_box_diverges_achiever_smearedClosed` — the ∀M achiever box-divergence spine with its
BOUNDARY-SMEARED slot now DISCHARGED unconditionally ∀L by `hSmeared_smearedClose` (Flag 1). The only
remaining open slot is the INTERIOR branch (`hInterior`) + the clean structural side-conditions
(`hMpos`/`hne`) — carried here as hypotheses, exactly as in the spine; the smeared obligation is gone.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The ∀M achiever box-divergence with the SMEARED branch closed.** Identical to
`routeMCore_box_diverges_achiever_spine`, except the `hSmeared` slot is filled unconditionally ∀L by
`hSmeared_smearedClose` (which derives all its structural data from `BoundarySmeared M ∧
NoInteriorBothDrop M ∧ 1 ≤ minAdm M`). The remaining open obligations are the INTERIOR branch and the
clean structural side-conditions (`hMpos`/`hne`) — the smeared branch owes nothing. This is the wiring
proof that the smeared closer discharges the spine's widened `hSmeared` slot post-rename. -/
theorem routeMCore_box_diverges_achiever_smearedClosed (M : Fin (L + 1) → ℕ) (hpos : 1 ≤ minAdm M)
    (c' : NNReal) (hc' : (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε)
    (hMpos : ∀ s, 0 < M s)
    (hne : ∀ hL : 0 < L, (deepestCoords M hL).Nonempty)
    (hNo : NoInteriorBothDrop M)
    (hInterior : ∀ _ : 2 ≤ L, InteriorDrop M → BoxDiverges M c' ε) :
    BoxDiverges M c' ε :=
  routeMCore_box_diverges_achiever_spine M hpos c' hc' ε hε hMpos hne hNo hInterior
    (hSmeared_smearedClose M hpos c' hc' ε hε)

end DLNFibre.DLN.RLCT
