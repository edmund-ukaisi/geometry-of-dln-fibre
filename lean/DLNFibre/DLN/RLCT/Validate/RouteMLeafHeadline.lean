import DLNFibre.DLN.RLCT.Validate.RouteMLeafChart
import DLNFibre.DLN.RLCT.Validate.RouteMRadialComp

/-!
# `RouteMLeafHeadline` — the ∀M-L2 interior-det headline from the genBlkFlatLive leaf-pivot chart

The capstone wiring for the ∀M-L2 interior-determinant headline on the LIVE-leaf chart
`phiFlatLiveAt` (`RouteMLeafChart`). Everything network-combinatorial is discharged from the banked
bricks — the structured active set `activeM` with `activeM.card = minAdm M` (`activeM_card`) and the
radial pivot `leafPivot ∈ activeM` (`leafPivot_mem_activeM`) — so the headline reads off the
pivot-generic radial wiring `radialComp_abs_det_at`, given the two genuinely-remaining
boundary-factor obligations as hypotheses:

* `hmap` — the MAP identity `phiFlatLiveAt … = B ∘ pivotBlowupOn activeM leafPivot` (obligation (1):
  the per-layer `chartParamsGen` reindex, the opaque-width analog of the `(2,2,2)`
  `chartParamsGen_Glr_eq`).
* `hasDB` — `B` has fderiv `DB` at the blown-up point (obligation (2): `B` polynomial).

Given those, `interiorDet_leaf_headline` is the unconditional headline
`|det Dφ| = |u p₀|^{minAdm−1}·|det DB|`. The `∏ engine` reading of `|det DB|` (obligation (3): the
Schur·LDU engine via the `ChartFactor` fold) is the caller's extra `hdet` hypothesis in
`interiorDet_leaf_headline_engine`.

This FREEZES the headline interface: the count, the radial wiring, and the rate are CLOSED; the two
boundary obligations (`hmap`/`hasDB`, and the `hdet` engine reading) are the named, scoped inputs.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (the banked wiring + count; no analysis beyond
the chain rule the radial wiring already uses).
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators

/-- **The ∀M-L2 interior-det headline from a boundary factor** (`L = 2`). Given the genBlkFlatLive
leaf-pivot chart `phiFlatLiveAt M ha (by norm_num) (leafPivot …) `, a boundary factor `B` with the
map identity `hmap : φ = B ∘ pivotBlowupOn activeM leafPivot` and fderiv `DB` at the blown-up point,
the chart's Jacobian abs-det factorizes as `|u_p₀|^{minAdm−1} · |det DB|`. The radial pivot
`p₀ = leafPivot` is in `activeM` (`leafPivot_mem_activeM`) and `activeM.card = minAdm M`
(`activeM_card`), so the pivot-generic radial wiring `radialComp_abs_det_at` fires. The count, the
radial wiring, and the rate are CLOSED; `B`/`DB`/`hmap`/`hasDB` are the named obligations. -/
theorem interiorDet_leaf_headline (M : Fin (2 + 1) → ℕ) (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2)
    (u : Fin (routeMAmbient M) → ℝ)
    (B : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ))
    (DB : (Fin (routeMAmbient M) → ℝ) →L[ℝ] (Fin (routeMAmbient M) → ℝ))
    (hmap : phiFlatLiveAt M ha (by norm_num) (leafPivot M ha (by norm_num) h0r h0c)
      = B ∘ pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c))
    (hasDB : HasFDerivAt B DB
      (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) u)) :
    |LinearMap.det (fderiv ℝ (phiFlatLiveAt M ha (by norm_num)
        (leafPivot M ha (by norm_num) h0r h0c)) u).toLinearMap|
      = |u (leafPivot M ha (by norm_num) h0r h0c)| ^ (minAdm M - 1)
        * |LinearMap.det DB.toLinearMap| :=
  radialComp_abs_det_at M (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c)
    (leafPivot_mem_activeM ha h0r h0c) (activeM_card ha) B
    (phiFlatLiveAt M ha (by norm_num) (leafPivot M ha (by norm_num) h0r h0c)) u DB hmap hasDB

/-- **The ∀M-L2 interior-det headline in the per-boundary engine form** (`L = 2`). Reads
`interiorDet_leaf_headline` plus the engine reading `hdet : |det DB| = ∏ engine` (the Schur·LDU
product over the `Fin 2` boundaries — boundary 0 the interior frame `|det K|^{r+c}·∏|q_i|^{…}`,
boundary 1 the leaf `= 1`) to give `|det Dφ| = |u p₀|^{minAdm−1} · ∏_s engine s`. -/
theorem interiorDet_leaf_headline_engine (M : Fin (2 + 1) → ℕ) (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2)
    (u : Fin (routeMAmbient M) → ℝ)
    (B : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ))
    (DB : (Fin (routeMAmbient M) → ℝ) →L[ℝ] (Fin (routeMAmbient M) → ℝ))
    (engine : Fin 2 → ℝ)
    (hmap : phiFlatLiveAt M ha (by norm_num) (leafPivot M ha (by norm_num) h0r h0c)
      = B ∘ pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c))
    (hasDB : HasFDerivAt B DB
      (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) u))
    (hdet : |LinearMap.det DB.toLinearMap| = ∏ s : Fin 2, engine s) :
    |LinearMap.det (fderiv ℝ (phiFlatLiveAt M ha (by norm_num)
        (leafPivot M ha (by norm_num) h0r h0c)) u).toLinearMap|
      = |u (leafPivot M ha (by norm_num) h0r h0c)| ^ (minAdm M - 1)
        * ∏ s : Fin 2, engine s := by
  rw [interiorDet_leaf_headline M ha h0r h0c u B DB hmap hasDB, hdet]

end DLNFibre.DLN.RLCT
