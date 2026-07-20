import DLNFibre.DLN.RLCT.Engine.GeoAtlasTransfer

/-!
# `DLNFibre.DLN.RLCT.Engine.GeoInvValMaint` — the value-walk maintenance + transport (loss-t15)

The four-case `InvVal3` maintenance over `tGeoG alphaGauge` and its prod-under-chart transport core
(`residualRow_pivot_eq_bmon`, the crux). Lives DOWNSTREAM of `GeoAtlasTransfer` (which imports
`GeoInvValWalk`), so it reuses walk-t20's α reads (`geoChartMapNorm_eq_id_comp_gauge_on_cone`,
`alphaGauge_ledgerMonomial_neutral`) + t14's `geoChartMap_flat_*` + this seat's payload (`InvVal3`,
`prodPrefix`, `bmonOf`) and tools (`layerEntry_eq_flat`, `prefixColFin_val_of_live`, peel).

**Wiring note (for the controller):** the final headline `leafDiagFrob_geoAtlasNorm` currently is a
`sorry` in `GeoAlphaGauge` (upstream of the walk); its proof (the `InvVal3` walk → leaf discharge)
is downstream here, so the headline must be RE-HOMED here (and `leafPullback_geoAtlasNorm` +
`ChartBridgeFaithful`'s consumption re-pointed) — a controller integration step, flagged.
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open scoped BigOperators

variable {L : ℕ} {M : Fin (L + 1) → ℕ}

/-! ## (a) The α-atlas chart on-cone unfold — foundation for the layer-under-B reads -/

/-- **The α-atlas chart on-cone unfolds to blow-up ∘ swap ∘ α-Schur.** Composes walk-t20's gauge
factorization (`geoChartMapNorm_eq_id_comp_gauge_on_cone`) with t14's id-gauge on-cone
(`geoChartMapNorm_apply_oncone`). This is what lets all the flat reads
(`geoChartMap_flat_{pivot,center,spectator}` + `flatSwapCLE_apply_flat` + `residualSchur_flat_read`)
apply to the value maintenance's `prod`-entry transport. -/
theorem geoChartMapNorm_alpha_apply_oncone (g : GeoChart M) (w : Params M)
    (hd : dCenterOfNode M g.node ≤ flatDim M) (hp : g.pivot < dCenterOfNode M g.node) :
    geoChartMapNorm alphaGauge g w
      = geoChartMap (dCenterOfNode M) (qNodeOf M) g
          (flatSwapCLE M (cNodeOf M g.node hd (⟨g.pivot, hp⟩ : Fin (dCenterOfNode M g.node)))
            (diagTargetOf M g.node g.edge (by omega)) (alphaGauge g w)) := by
  obtain ⟨node, edge, pivot⟩ := g
  rw [geoChartMapNorm_eq_id_comp_gauge_on_cone alphaGauge node edge pivot hd hp]
  simp only [Function.comp_apply]
  exact geoChartMapNorm_apply_oncone ⟨node, edge, pivot⟩ (alphaGauge ⟨node, edge, pivot⟩ w) hd hp

end DLNFibre.DLN.RLCT.Engine
