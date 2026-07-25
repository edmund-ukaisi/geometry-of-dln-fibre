import DLNFibre.DLN.Aoyagi.Corank2Chart334
import DLNFibre.DLN.Aoyagi.GeneralGeoAtlas
import DLNFibre.DLN.Aoyagi.LeafCoverTiling

/-!
# `DLN.Aoyagi.Corank2FanDef334` — the (3,3,4) `gWrapFan` (rung-5d cover, shared def)

The single shared definition of the (3,3,4) cover fan, so the two rung-5d cover lanes — (ii) the
`Covers`/ball-cover [`Corank2FanCover334`] and (B) the K-orbit leaf-Chart family
[`Corank2Transport334`] — build on ONE object (no divergence). Piece (i) of the cover
(routeP-p1), fed by crux (A) (`Corank2Chart334.gWrap_eq_pathMap`).

`gWrapFan` is the `fanOfSteps` fan whose CANONICAL leaf (pivots `20, 0, 1`) is exactly `gWrap`:
`blockBlowupMap {0..7,20} 20 ∘ (shearH ∘ permP)` (node 1) `∘ bbA0` (node 2) `∘ bbA1` (node 3) =
`sigmaPiv ∘ shearH ∘ permP ∘ bbA0 ∘ bbA1 = gWrap`. The interleaved `permP` folds into node 1's
INNER shear `σ = shearH ∘ permP` — legitimate because `FanTree.node`'s `σ` is an ARBITRARY per-pivot
map (not a `blockShear`). Node convention: `blockBlowupMap S p ∘ σ p` (blow-up OUTER, `σ` INNER).

Inflation `f = r ↦ r + 2·r²` (the 2-term `shearPhiH` slots 8-11 force `C = 2`; node 1's
`σ = shearH ∘ permP` box-contains via `shearH_covers` + `permP` isometry; nodes 2,3 `σ = id`
box-contain trivially). The `Covers gWrapFan 1` proof + the `⋃ charts.g '' dom = leafImages`
chart-enumeration are the (ii)/(B) lanes' obligations; this module fixes only the SHARED object.
-/

open MeasureTheory Set Metric
open DLNFibre.Core.Aoyagi
open DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap DLNFibre.DLN.Aoyagi.Corank2ChartJac
open DLNFibre.DLN.Aoyagi.Corank2GWrapDecomp
open DLNFibre.DLN.Aoyagi.LeafCoverTiling DLNFibre.DLN.Aoyagi.GeneralGeoAtlas

namespace DLNFibre.DLN.Aoyagi

/-- **The (3,3,4) cover-fan step list.** Three nodes (outer→inner): the `sigmaPiv` blow-up
(center `{0..7,20}`) with inner shear `shearH ∘ permP`; the `bbA0` blow-up (center `{0..7}`); the
`bbA1` blow-up (center `{1,5,6,7}`); shears `id` on the inner two. -/
noncomputable def gWrapFanSteps : List (FanStep 21) :=
  [ ⟨({0,1,2,3,4,5,6,7,20} : Finset (Fin 21)), by decide, fun _ ↦ shearH ∘ permP⟩,
    ⟨({0,1,2,3,4,5,6,7} : Finset (Fin 21)), by decide, fun _ ↦ id⟩,
    ⟨({1,5,6,7} : Finset (Fin 21)), by decide, fun _ ↦ id⟩ ]

/-- **The (3,3,4) cover fan** `gWrapFan R : FanTree 21` — the `fanOfSteps` fan (inflation
`f = r + 2r²`) whose canonical leaf composite is `gWrap`. The shared object for rung-5d (ii)/(B). -/
noncomputable def gWrapFan (R : ℝ) : FanTree 21 :=
  fanOfSteps (fun r ↦ r + 2 * r ^ 2) gWrapFanSteps R

end DLNFibre.DLN.Aoyagi
