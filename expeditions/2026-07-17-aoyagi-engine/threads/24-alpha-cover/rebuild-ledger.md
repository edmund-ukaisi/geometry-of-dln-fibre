# Consumer-rebuild ledger — α completion to full Q,P (loss-t15, task #22)

*Seat: `lean-formaliser` (loss-t15). Form-independent sequencing doc for the α-completion rebuild —
produced while the exact Lg/Rg cell shapes are held on pnp-rg's completed-α achiever (task #23/#24).
Feeds the navigator's parallelization pricing. Steer: consume pnp-rg's achiever for BOTH Lg and Rg
(decorrelation + seam consistency); this ledger is what the consuming build touches.*

## Context

pnp-diag (`cert-exactly-diagonal-mechanism.md`) proved `alphaGauge = residualSchurShear` is
interior-Schur only: it does `interior ↦ interior − b·a` but leaves the pivot cross `(a,b)`, so
`prod ∘ chartMap` is NOT diagonal at a leaf and `residualCore` hits 0 (LeafPullback lower bound
FALSE). The fix completes α to Aoyagi's full Q,P: **pivot-column clear (Lg, ≤S-local, cross-cell —
NOT a within-node `schurCells` addition, confirmed `battery/lg_form_specify.py`)** + **pivot-row clear
(Rg, cross-layer into S+1)**. Acceptance criterion (my consumer spec, team-lead-accepted): each
normalized block becomes `[[1,0],[0,ρ]]`, so `prod = diag` and `residualCore = 1 + Σρ² ≥ 1`. The
**acceptance oracle** is my own `battery/clearedof_walk_trace.py`'s `clear_pivot` (encodes the full
row+col reduction incl. genuinely-zero dropped rows); the corrected α must match its leaf output.

## The change, in one line

`residualSchurShear node rows cols` (a foldr of interior `flatElemShear`s over `schurCells`) gains two
more families of cells: the Lg pivot-column cells (writing ≤S / output-side coords) and the Rg
pivot-row cells (writing layer-S+1 coords). The cross cells become **written** targets, not read-only
sources — which is what flips the independence lemmas.

## Classification (SURVIVES-redo / CHANGES-constant / FALSE-rebuild / GATED-on-Rg)

### GeoAlphaGauge.lean — the source module (my edit surface)

| lemma (line) | verdict | note |
|---|---|---|
| `schurCells_ne` (:157), `schurCells_pairwise` (:199), `residualSchur_flat_read` (:225) | SURVIVES | interior cells unchanged; NEW Lg/Rg cells need analogous `ne`/`pairwise` |
| `elemShearFold_fixed` (:239), `elemShearFold_at_a` (:254) | SURVIVES (as generic list lemmas) | their APPLICATION to the cross (via `schurCells_snd_ne`) no longer covers the now-written cross cells |
| `schurCells_snd_ne` (:176) | REINTERPRET | wording (cross never an interior target) stays true for the interior sublist; the completed fold WRITES the cross — no longer the whole story. Used only at :448 (srcBox), whose proof changes anyway |
| `residualSchurShear_abs_det_one` (:410), `alphaGauge_abs_det_one` (:427) | SURVIVES-redo | det-1 CONCLUSION holds (Lg/Rg unipotent); proof extends via `foldrCompAbsDet_flatElemShear` IF new cells stay `flatElemShear`-shaped (need `a≠b,a≠c` each). If Rg's cross-layer op is not a `flatElemShear`, a new det-1 atom is needed |
| `residualSchurShear_srcBox` (:441), `alphaGauge_srcBox_bounded` (:484) | CHANGES-constant | bound compounds past `R(1+R)` (more shears). pnp-cover's `ρ(1+ρ)` radius-thread STRUCTURE survives; per-node constant grows |

### GeoAtlasTransfer.lean — walk-t20 (flag as touched)

| lemma (line) | verdict | note |
|---|---|---|
| `elemShear_qmp` (:158), `elemShear_preimage_null` (:147), `elemShearInv_differentiable` (:132) | SURVIVES | atom-level; reused for the new cells if `flatElemShear`-shaped |
| `residualSchurShear_qmp` (:223), `residualSchurShear_injective` (:234), `alphaGauge_qmp` (:244), `alphaGauge_injective` (:254), `alphaGauge_differentiable` (:398) | SURVIVES-redo | Lg/Rg are injective QMP homeomorphs (det-1); proof extends to the new cells. Feeds a.e.-injectivity (task #2c) |
| `residualSchurShear_surjective` (:969), `alphaGauge_surjective` (:979), `cubeBox_subset_alphaGauge_image` (:993) | CHANGES-constant | cover image; conclusion survives (homeomorph), the image/srcBox constant grows. Feeds the cover (task #2a) |
| `residualSchurShear_fixes_of_not_mem` (:414) | SURVIVES-redo | statement survives; `not_mem` must exclude the NEW Lg/Rg targets too |
| `schurCells_fst_ne_birthFlatCoord` (:427) | SPLIT | Lg targets (≤S) ⊥ birth diagonals (deeper cleared levels) → clean, re-provable. **Rg targets (S+1) ⊥ later-birth-corners → GATED on pnp-rg #24** (the elder's locality question + the (J,J)-fixed check) |
| `alphaGauge_ledgerMonomial_neutral` (:450) | GATED-on-Rg | depends on the two above; CONCLUSION at risk only for Rg's S+1 writes vs later births; re-establish once #24 rules |

### GeoInvValMaint.lean — mine

| lemma (line) | verdict | note |
|---|---|---|
| `alphaGauge_fixes_birthFlatCoord` (:95) | GATED-on-Rg (MOST EXPOSED) | same dependency as `ledgerMonomial_neutral`; if Rg's row-clear lands OFF the birth corners it survives with a new proof, if it can HIT a later birth corner the conclusion changes — the (J,J)+overlap question pnp-rg pins |
| `geoChartMapNorm_alpha_apply_oncone` (:32) | SURVIVES-redo | α factor shape moves; conclusion form survives, mechanical re-verify |

### Consumers (downstream)

| lemma | verdict | note |
|---|---|---|
| `geoAtlasNorm_leaf_leafJacobian` (walk-t20, GeoAtlasTransfer:~849) | SURVIVES-redo | det-based, det-1-transparent (uses `alphaGauge_abs_det_one`); redo transparency over completed gauge |
| `geoAtlasNorm_leaf_ae_injOn` (task #2c) | SURVIVES-redo | uses `alphaGauge_injective`/`qmp` |
| `geoAtlasNorm_imageCover` (task #2a) | CHANGES-constant | uses surjective/image; new cover radius |

## Dependency rebuild order (the navigator's ask)

- **Tier 0 (external, gates all): pnp-rg cell-write verdict** — exact Lg cells (≤S targets), Rg cells
  (S+1 placement), the (J,J)-fixed check, and the Rg ⊥ later-birth-corners disjointness (#24).
- **Tier 1 (GeoAlphaGauge, loss-t15):** add Lg fold [NOW-ready on Tier 0 Lg cells] + Rg fold [on Tier 0
  Rg cells] to the completed `residualSchurShear`; new-cell `ne`/`pairwise`; extend
  `*_abs_det_one`; new `srcBox` constant. Lg is independently buildable once its cells land; Rg needs
  #24.
- **Tier 2 (GeoAtlasTransfer, walk-t20, after Tier 1):** `fixes_of_not_mem` (exclude new targets);
  qmp/injective/differentiable/surjective/image (extend + new constant); `schurCells_fst_ne_birth…`
  (Lg clean now; Rg gated); `ledgerMonomial_neutral` (Rg gated).
- **Tier 3 (consumers, after Tier 2):** leafJacobian det-1-transparency; ae-injOn; imageCover;
  my `alphaGauge_fixes_birthFlatCoord` (Rg gated) + `geoChartMapNorm_alpha_apply_oncone`.
- **Tier 4 (value lane, loss-t15):** task #21 four-case maintenance re-opens over the completed α →
  `leafDiagFrob_geoAtlasNorm` closes → `leafPullback_geoAtlasNorm` → `chartBridgeFaithful_buildTree`.

## Parallelization note

Lg (Tier 1 pivot-column) and its ≤S disjointness (Tier 2 `schurCells_fst_ne_birth…` Lg part) are
buildable the moment pnp-rg names the Lg cells — they do NOT wait on the Rg overlap ruling. Rg and
everything gated-on-Rg (birth-neutrality, `alphaGauge_fixes_birthFlatCoord`) wait on #24. So the
critical path is: #24 overlap ruling → Rg build → birth-neutrality re-verify → value lane. The Lg
build, the qmp/injective/surjective extensions, and the srcBox/cover constant updates can proceed in
parallel off the Lg cells + the general det-1/homeomorph structure.
