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

/-! ## Form 2: the D_J-carry invariant (elder ruling — carry the residual block, incidence form) -/

/-- **`InvVal3f2`** (elder ruling, the CARRY): `InvVal3` + a THIRD clause carrying the
residual block `D_J` at un-resolved cells (`resD`, parametric; instantiated with the incidence-form
`D_J`, Aoyagi's induction object worked.tex:482/509-519; NOT the opaque foldToState). The
cleared/dropped clauses are UNCHANGED (first two conjuncts = `InvVal3`); the residual carry is the
new content the row-J transport consumes (α-Schur reads `D_J`'s pivot-cross; the interior feeds the
next `D`). HELD SLOT: the row-J cleared off-diagonal at the pivot's LIVE columns (pnp-diag verdict
pending — interior-α + column-drop leave the live-col a-ratios). -/
def InvVal3f2 (cleared dropped : ConState L → Fin (M 0) → Prop)
    [∀ s i, Decidable (cleared s i)] [∀ s i, Decidable (dropped s i)]
    (bmon : ConState L → Params M → Fin (M 0) → ℝ)
    (resD : (s : ConState L) → Params M → Fin (M 0) → Fin (M (prefixColFin s)) → ℝ)
    (acc : Params M → Params M) (s : ConState L) : Prop :=
  ∀ (w : Params M) (i : Fin (M 0)) (j : Fin (M (prefixColFin s))),
    (cleared s i → prodPrefix s (acc w) i j = if (i : ℕ) = (j : ℕ) then bmon s w i else 0) ∧
    (dropped s i → prodPrefix s (acc w) i j = 0) ∧
    (¬ cleared s i → ¬ dropped s i → prodPrefix s (acc w) i j = resD s w i j)

/-- **Form-2 projects to the three-state `InvVal3`** (drop the `resD` conjunct). So the proven
three-state consumer side — the leaf discharge `leafDiagFrob_of_invVal3_leaf`, the width-drop fix —
applies verbatim: the D_J carry is a pure STRENGTHENING, costing nothing downstream. -/
theorem invVal3f2_to_invVal3 (cleared dropped : ConState L → Fin (M 0) → Prop)
    [∀ s i, Decidable (cleared s i)] [∀ s i, Decidable (dropped s i)]
    (bmon : ConState L → Params M → Fin (M 0) → ℝ)
    (resD : (s : ConState L) → Params M → Fin (M 0) → Fin (M (prefixColFin s)) → ℝ)
    (acc : Params M → Params M) (s : ConState L)
    (h : InvVal3f2 cleared dropped bmon resD acc s) :
    InvVal3 cleared dropped bmon acc s :=
  fun w i j => ⟨(h w i j).1, (h w i j).2.1⟩

/-- **Form-2 base at `conRoot`**: nothing cleared or dropped, and the whole prefix is the un-resolved
`D_0` (`resD conRoot = prodPrefix conRoot ∘ id`), so the residual clause is `rfl`. Trivial under the
D_J carry — `D_0` is the raw prefix product, Aoyagi's induction start. -/
theorem invVal3f2_conRoot (cleared dropped : ConState L → Fin (M 0) → Prop)
    [∀ s i, Decidable (cleared s i)] [∀ s i, Decidable (dropped s i)]
    (bmon : ConState L → Params M → Fin (M 0) → ℝ)
    (resD : (s : ConState L) → Params M → Fin (M 0) → Fin (M (prefixColFin s)) → ℝ)
    (hcl : ∀ i : Fin (M 0), ¬ cleared (conRoot : ConState L) i)
    (hdr : ∀ i : Fin (M 0), ¬ dropped (conRoot : ConState L) i)
    (hres : ∀ (w : Params M) (i : Fin (M 0)) (j : Fin (M (prefixColFin (conRoot : ConState L)))),
      resD (conRoot : ConState L) w i j = prodPrefix (conRoot : ConState L) (id w) i j) :
    InvVal3f2 cleared dropped bmon resD id (conRoot : ConState L) :=
  fun w i j => ⟨fun hc => absurd hc (hcl i), fun hd => absurd hd (hdr i),
    fun _ _ => (hres w i j).symm⟩

end DLNFibre.DLN.RLCT.Engine
