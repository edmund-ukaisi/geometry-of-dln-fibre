import DLNFibre.DLN.RLCT.Validate.RouteMBridge
import DLNFibre.DLN.RLCT.Validate.Case222RouteMCover
import DLNFibre.DLN.RLCT.Validate.Case222Algebra
import DLNFibre.DLN.RLCT.Validate.Case222Rlct

/-!
# `DLNFibre.DLN.RLCT.Validate.Case222RouteMValidation` — the `(2,2,2)` general-engine milestone

The `(2,2,2)` value `rlctAtOn (dlnLoss H222 0) deepest222 = 3/2` routed through the **general**
`IsRouteMCover` / `routeM_rlctAtOn_eq_iInf` engine (the path that generalizes to all rank patterns),
rather than through the concrete `rlctAtOn_myF222_eq` of `Case222Rlct`.

**This is a MILESTONE / validation, not a new headline.** The `(2,2,2)` value is ALREADY proven
end-to-end in `Case222Rlct` (`case222_rlctAtOn_eq` / `case222_rlct`), via the concrete geometric
`≥`-cover (`rlctAtOn_myF222_eq`, clean-three, S2-free) antisymmetric with the cited `≤`-half
(`monomial_rlct`, Aoyagi/Watanabe). What this file adds is a SECOND, independent derivation of the same
value through the general abstraction — exercising `IsRouteMCover` + `routeM_rlctAtOn_eq_iInf`
end-to-end on the worked case, confirming the engine that the general routeStep will feed actually
fires on `(2,2,2)`. The chain:

* assemble `IsRouteMCover myF222 openBox (Fin 1) routeM222D routeM222K routeM222H` from fm3's banked
  cover facts (`routeM222_Fmeas/Uopen/Umem/cover_le/cover_ge_div`);
* `routeM_rlctAtOn_eq_iInf` gives `rlctAtOn myF222 0 = ⨅ i, monomialThreshold (…) = 3/2`
  (`routeM222_iInf_threshold`);
* `rlctAtOn_dlnLoss222_transport` (the `e222` measure-preserving reindex, via `dlnLoss222_eq_myF222`)
  carries the value from `Fin 8 → ℝ` back to `Params H222` at `deepest222`.

The `≤`-half of the RLCT (the `cover_ge_div`-fed divergence) rests on the cited bound; the `≥`-cover is
the geometric, S2-free content. So this is the `(2,2,2)` R1 leg, derived through the general engine.
-/

open MeasureTheory
open scoped ENNReal BigOperators Topology

namespace DLNFibre.DLN.RLCT

/-- **The `(2,2,2)` `IsRouteMCover` instance** — fm3's banked cover facts assembled into the general
`IsRouteMCover` Prop over the geometric data `F = myF222`, `U = openBox`, single leaf `ι = Fin 1`
with exponent datum `(routeM222D, routeM222K, routeM222H)` (`d = 8`, `k = (1,0,1,0,…)`,
`h = (3,0,2,0,…)`, threshold `3/2`). -/
theorem isRouteMCover_222 :
    IsRouteMCover myF222 openBox (Fin 1) routeM222D routeM222K routeM222H where
  Fmeas := routeM222_Fmeas
  Uopen := routeM222_Uopen
  Umem := routeM222_Umem
  cover_le := routeM222_cover_le
  cover_ge_div := routeM222_cover_ge_div

/-- **The `(2,2,2)` cover value through the general engine.** `rlctAtOn myF222 0 = 3/2`, derived by
feeding `isRouteMCover_222` to the GENERAL `routeM_rlctAtOn_eq_iInf` (`= ⨅ monomialThreshold`) and
collapsing the single-leaf `⨅` (`routeM222_iInf_threshold`). Independent of `Case222Rlct`'s concrete
`rlctAtOn_myF222_eq`. -/
theorem rlctAtOn_myF222_eq_routeM : rlctAtOn myF222 (0 : Fin 8 → ℝ) = 3 / 2 := by
  rw [routeM_rlctAtOn_eq_iInf myF222 openBox (Fin 1) routeM222D routeM222K routeM222H
    isRouteMCover_222]
  exact routeM222_iInf_threshold

/-- **The `(2,2,2)` R1 leg through the general engine** (the milestone). `rlctAtOn (dlnLoss H222 0)
deepest222 = 3/2`, derived through the general `IsRouteMCover` / `routeM_rlctAtOn_eq_iInf` path:
transport the loss to `myF222` (`rlctAtOn_dlnLoss222_transport` + `dlnLoss222_eq_myF222`), then read
off the general-engine cover value (`rlctAtOn_myF222_eq_routeM`). Reproduces `Case222Rlct`'s
`case222_rlctAtOn_eq` (which goes through the concrete cover) via the GENERAL abstraction — the
end-to-end validation that the engine fires on `(2,2,2)`. -/
theorem case222_rlctAtOn_eq_routeM :
    rlctAtOn (dlnLoss H222 0) deepest222 = 3 / 2 := by
  rw [rlctAtOn_dlnLoss222_transport myF222 dlnLoss222_eq_myF222, rlctAtOn_myF222_eq_routeM]

end DLNFibre.DLN.RLCT
