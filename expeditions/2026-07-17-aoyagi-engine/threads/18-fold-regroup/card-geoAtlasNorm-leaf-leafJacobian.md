# Statement card — `geoAtlasNorm_leaf_leafJacobian` (2d, the α-atlas R7 LeafJacobian transfer)

**Status:** sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]` (pending
rev-jac fidelity verdict + integration full-AxCheck). Delivered by walk-t20 (2d-B/2d-C),
tick 376–378, on t14's atoms-first probe mechanism.

## Claim
Over the faithful α-normalized atlas `geoAtlasNorm alphaGauge (buildTree M (conOracle M) conRoot)`
— Aoyagi's Q,P-normalized integration chart — every leaf chart satisfies the R7
`LeafJacobian` (β-det = the full-ledger monomial `∏|z_{divCoord}|^{E−1}`, ψ = id det-1,
`fc = birthFlatCoord s'`, `emb = t0Indices s'`).

## Lean
```
theorem geoAtlasNorm_leaf_leafJacobian (h : 0 < flatDim M) (c : LeafData M)
    (hc : c ∈ geoAtlasNorm alphaGauge (buildTree M (conOracle M) conRoot)) :
    LeafJacobian c
```
`GeoAtlasTransfer.lean`. Hypotheses: `0 < flatDim M`; membership over `conRoot`. No srcBox,
no cover — pointwise / srcBox-independent.

## How it is proved (one spine, two instantiations)
- `geoAtlasNorm_cocycle` — the **gauge-parametric** fold-Jacobian cocycle over `tGeoG`,
  generic in a gauge bundle `(hgdiff : differentiable) ∧ (hgdet1 : |det Dg|=1) ∧
  (hgreads : reads-neutral)`, instantiated at `alphaGauge`. **The shared spine is the
  maintenance ATOMS** (`ledger_det_maintenance_*`, reused verbatim via
  `gauge_det_maintenance_wrapper`), not one walk: there are TWO parallel walk skeletons
  (`geoAtlas_cocycle` over `tGeo`; `geoAtlasNorm_cocycle` over `tGeoG`). `geoAtlasNorm_cocycle`
  is a genuine gauge generalization, but in practice only `alphaGauge` is instantiated — the
  id side keeps its own `geoAtlas_cocycle` rather than being re-derived from the general form
  (rev-jac CHECK-3 framing correction to the earlier "instantiated at both" wording). The id
  side (`geoAtlas_cocycle`/`geoAtlas_fold_det`/`geoAtlas_leaf_leafJacobian`) is **byte-unchanged**
  (git-confirmed) — the one-spine constraint (id side untouched) holds regardless of the
  framing nuance.
- `gauge_det_maintenance_wrapper` — lifts an id maintenance conclusion to the gauge atlas:
  on-cone factor (`geoChartMapNorm_eq_id_comp_gauge_on_cone`) → chain-rule det split
  (`abs_det_fderiv_comp`) → det-1 (`alphaGauge_abs_det_one`) → reads-neutrality.
- `alphaGauge_ledgerMonomial_neutral` — α fixes every child divisor's birth-diagonal read
  (case-11/rollover = id **definitionally**, GeoAlphaGauge:282-283; case-2/case-12 via
  `residualSchurShear_fixes_of_not_mem` + the disjointness below).
- `schurCells_fst_ne_birthFlatCoord` — the ONE genuinely new proof (~10 lines): schurCells
  targets (row ≥ node.cleared+1) ⊥ child birth diagonals, from `birthFlatCoord_ne_diag_layer_cell`
  (CornerDisjoint/t17) + `DivBirthInv`-on-child freshness. The tick-343 reads-based bundle
  holding concretely — the disjointness tripwire did NOT fire.

## Why it matters
Closes the **second-to-last** owed source of `chartBridgeFaithful_buildTree`. Its sorryAx
now routes through TWO sources only: `leafDiagFrob_geoAtlasNorm` (loss-t15's value walk —
the one true mathematical hole) + `geoAtlasNorm_imageCover` (t14 Phase-2 cover, de-risked).

## Dependencies
`geoAtlasNorm_cocycle` (walk-t20); the id maintenance atoms `ledger_det_maintenance_*`
(t11/t14, reused verbatim); `CornerDisjoint` (t17); `DivBirthInv` freshness.
