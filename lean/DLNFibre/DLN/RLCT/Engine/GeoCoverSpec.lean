import DLNFibre.DLN.RLCT.Engine.GeoChart

/-!
# `DLNFibre.DLN.RLCT.Engine.GeoCoverSpec` — the cover SPECIFY skeleton (clause (A), for t10)

The SPECIFY handoff for the cover builder (coverage-t08 → t10, the two-lane pattern). Full recipe:
`threads/10-coverage/cover-specify.md`. This file carries the VALIDATED statement (below) with its one
`sorry`; t10 fills it by the recipe. q-det-INDEPENDENT (the cover reads pure `β` via `reparam_image`;
the Jacobian is t11's fold-module).

**Decided structure (see the note):** build the geometric fan-out TREE `tGeo` (bake the composite into
leaves, `geoChartMap` onto edges) and reuse the banked tree-fold — do NOT re-prove over the
`geometricLeafPaths` List. Then `geoAtlas t = leaves (tGeo id t)` and the cover is
`chartBridge_imageCover_of_ownCovers` over `tGeo`, per-node discharged by `node_pivotCover_of_atom`.

**The exact pins (all banked / t09):** `q = qNodeOf M n`; `hbij = dCenterOfNode_edgeSum` (the offset
partition tiles `Fin (dCenterOfNode n)`); `hd = dCenterOfNode_le_flatDim`; `hloc = geoChartMap`-is-the-
`qNodeOf`-conjugated-`pivotChart` (by def, on-cone); `srcBox` = the flat cube (⊇ the `pivotChartDom`
childRegions, so clause (A) is the free superset direction); headline = `chartBridge_imageCover_of_ownCovers`.
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open MeasureTheory Set

variable {L : ℕ} {M : Fin (L + 1) → ℕ}

/-- **Clause (A): the geometric atlas image-covers the zero-locus** (SPECIFY skeleton, `sorry` owned by
t10). An open neighbourhood of the zero-locus-in-the-unit-box sits inside the union of the atlas pieces'
chart images. The `htree` witness pins the tree to `buildTree` so t09's conOracle-relative
`dCenterOfNode_edgeSum` / `dCenterOfNode_le_flatDim` apply at each node. Recipe: `cover-specify.md`. -/
theorem geoAtlas_imageCover (t : ResolutionTree M) (s : ConState L)
    (htree : t = buildTree M (conOracle M) s) :
    ∃ U : Set (Params M), IsOpen U ∧
      {A : Params M | A ∈ paramsBoxM M 1 ∧ frobSq (prod M A) = 0} ⊆ U ∧
      U ⊆ ⋃ c ∈ geoAtlas t, c.chartMap '' c.srcBox := by
  sorry

end DLNFibre.DLN.RLCT.Engine
