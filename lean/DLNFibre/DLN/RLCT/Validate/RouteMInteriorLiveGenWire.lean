import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveGenAtom
import DLNFibre.DLN.RLCT.Validate.RouteMAchieverDispatch

/-!
# `RouteMInteriorLiveGenWire` — general-`L` interior `hInterior` (the `0 < deepRank` stratum)

Wires the landed general-`L` LIVE-leaf interior box-divergence atom
(`RouteMInteriorLiveGenAtom.routeMCore_box_diverges_interiorLiveGen`) into the achiever-dispatch
spine's `hInterior` obligation
(`RouteMAchieverDispatch.routeMCore_box_diverges_achiever_spine`), on the interior sub-stratum where
the deepest-factor rank is positive (`0 < deepRank M = Text M (tach M) L`).

## The bridge (thin; the atom is the analytic content)

The spine's obligation is `hInterior : ∀ _ : 2 ≤ L, InteriorDrop M → BoxDiverges M c' ε`. The atom
consumes six structural inputs; five are discharged from the dispatch context, one (`h0r`) is
genuine and carried explicitly (see the fidelity note):

* `ha : StructAdm M (tach M)` — the UNCONDITIONAL achiever-path admissibility `structAdm_tach M hL`.
* `hL : 0 < L` — from `2 ≤ L`.
* `h0c : 0 < Wext M L` — the FIRST CONJUNCT of `InteriorDrop M` (`InteriorDrop.1`), sound verbatim.
* `hpos : 1 ≤ minAdm M`, `hc'`, `hε` — spine context.
* `h0r : 0 < Text M (tach M) L` (= `0 < deepRank M`) — CARRIED EXPLICITLY, not derived (see below).

## Fidelity note — why `h0r` is a hypothesis, not derived (the honest scope)

`InteriorDrop M` does **not** imply `0 < deepRank M`. At `L = 2` the interior class is characterised
by `interiorDrop_L2_iff` as `0 < M 2 ∧ deepRank M < M 0 ∧ deepRank M < M 1` — an UPPER bound on
`deepRank`, with no positive lower bound; `(2,2,1)` (with `tStar = ![0,0]`) has `deepRank = 0` yet
`InteriorDrop` holds. Accordingly the L=2 interior branch (`routeMCore_box_diverges_interior_L2`)
**cases** on `Text M (tach M) 2 = 0`: the `0 < deepRank` case uses the LIVE-leaf atom, the
`deepRank = 0` case uses a SEPARATE E-block radial atom (`routeMCore_box_diverges_eDeepRank0`,
pinned to `Fin (2+1)`).

Only the LIVE-leaf atom is lifted to general `L` (`routeMCore_box_diverges_interiorLiveGen`). There
is **no** general-`L` `deepRank = 0` atom yet. So the general-`L` `hInterior` is dischargeable
directly from the landed atom **only on the `0 < deepRank` sub-stratum**; the `deepRank = 0`
sub-stratum is the remaining general-`L` interior gap (for `L ≥ 3`; at `L = 2` it is banked). The
scope was decorrelated-Codex confirmed (xhigh):
`∀ (_ : 2 ≤ L), InteriorDrop M → 0 < deepRank M → BoxDiverges M c' ε`.

Axiom profile: inherits the atom's footprint —
`[propext, Classical.choice, Quot.sound, monomial_rlct]` (clean-three + the single S2 cited axiom
`monomial_rlct`), no `sorryAx`.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The general-`L` interior `hInterior` discharge on the `0 < deepRank` sub-stratum.** For any
`M` with `2 ≤ L`, `InteriorDrop M`, and a positive deepest-factor rank `0 < deepRank M`, the
achiever box integral diverges at any `c' ≥ ½·minAdm M`. Discharged directly from the landed
general-`L` LIVE-leaf atom `routeMCore_box_diverges_interiorLiveGen`: `ha := structAdm_tach`, `hL`
from `2 ≤ L`, `h0c` from `InteriorDrop.1`, `h0r = 0 < deepRank M` (`0 < Text M (tach M) L`, `rfl`).

This is the exact shape the spine's `hInterior` slot consumes, restricted to `0 < deepRank M` — the
sub-stratum the atom covers. The complementary `deepRank M = 0` sub-stratum needs a separate
general-`L` atom (banked at `L = 2` only; the general-`L` interior gap). See the file header. -/
theorem routeMCore_box_diverges_interiorLiveGen_of_deepRank_pos (M : Fin (L + 1) → ℕ)
    (hL2 : 2 ≤ L) (hInt : InteriorDrop M) (hdr : 0 < deepRank M)
    (hpos : 1 ≤ minAdm M)
    (c' : NNReal) (hc' : (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε) :
    BoxDiverges M c' ε :=
  routeMCore_box_diverges_interiorLiveGen M (structAdm_tach M (by omega)) (by omega)
    hdr hInt.1 hpos hInt c' hc' ε hε

/-- **The spine's `hInterior` slot, discharged on the `0 < deepRank` sub-stratum** — the
`∀ _ : 2 ≤ L`-shaped consumer form. Given a positive deepest-factor rank, the interior branch
obligation `∀ _ : 2 ≤ L, InteriorDrop M → BoxDiverges M c' ε` holds by the atom. (The
`deepRank M = 0` sub-stratum is the remaining general-`L` interior obligation — see the header.) -/
theorem interiorLiveGen_hInterior_of_deepRank_pos (M : Fin (L + 1) → ℕ)
    (hdr : 0 < deepRank M) (hpos : 1 ≤ minAdm M)
    (c' : NNReal) (hc' : (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε) :
    ∀ _ : 2 ≤ L, InteriorDrop M → BoxDiverges M c' ε :=
  fun hL2 hInt =>
    routeMCore_box_diverges_interiorLiveGen_of_deepRank_pos M hL2 hInt hdr hpos c' hc' ε hε

end DLNFibre.DLN.RLCT
