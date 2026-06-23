# cobuild-sub34 gate status — #44c (L2 deepest gauge-chart instance)

Snapshot of what is built vs. gated, for in-repo visibility (not just teammate messages).
Branch: `fm2/deepest-gauge-chart-sub34` @ `1b841e5`. As of 2026-06-23 (post-(C)-refactor + PIN1).

## Built + GREEN (sorry-free; clean-three)

- **PIN 0 — `deepest_coreAbsorb_exists`** (`DeepestGaugeConstruction.lean` + `DeepestSchurShift.lean`).
  The concrete `deepestCoreAbsorb = coreShearHomeo (schurCutoffShift …)` (the cutoff additive Schur
  shear, det=1, MP); all four `coreAbsorb` obligations via the shift-agnostic MP peel
  `coreShear_satisfies_coreAbsorb`. `deepestCoreAbsorb_mp` exposes the MP for PIN 1.
- **PIN 1 — `deepest_regAbsorb_exists`** (`DeepestGaugeConstruction.lean`, **sorry-free**). The IFT
  local-diffeo RLCT peel, general L. Built from:
  - `rlctAtOn_comp_localDiffeo` (`DeepestRegAbsorbIFT.lean`) — the **IFT → #72 adapter** (the
    detbound card's "next layer"): `ContDiff ⊤ f` + `HasStrictFDerivAt f (e:≃L) wstar` + `f wstar=wstar`
    ⟹ `rlctAtOn (F∘f) wstar = rlctAtOn F wstar`. (`toOpenPartialHomeomorph` + `contDiffAt_symm` +
    `hasFDerivAt_symm` + `boundedUnit_fderiv_det` + `measurable_fderiv` → `rlctAtOn_boundedUnit_localHomeomorph`.)
  - `regStraightenOf E_pivot` + `hasStrictFDerivAt_regStraightenOf_refl` — the (C)-fallback total map,
    `dE_pivot(0)=fst ⟹` total deriv `id`.
  - `rlctAtOn_regAbsorb_reduce` — the `coreAbsorb.symm` conjugation stripping `coreAbsorb` from the
    coupled core term, reducing to the decoupled IFT peel.
  - **Reviewer verdict: PASS** (fidelity + soundness, 2026-06-23): non-vacuous, non-circular,
    clean-three, the `deepestEPivot` gap honestly isolated. Statement card:
    `pin1-regabsorb-statement-card.md`.
- `DeepestGaugeDiffeo.lean` — IFT det-bound bedrock (`boundedUnit_fderiv_det` etc.); statement card.
- `DeepestGaugeBlocks.lean` — matrix bedrock + `fullProduct_loss_squeeze` (route-independent two-sided
  bound) + `core_comparability_squeeze` (#54, 2-hypothesis squeeze, cross-term Young-locked by pp2).
- `DeepestSplitHaar.lean` — `IsAddHaarMeasure` on `DeepestSplit` (transport-to-flat, the #72 Haar fix).

## The single remaining gate: the shared `deepestEPivot` form (#115) + PIN 2 (#80)

`deepestEPivot` (def + 3 props `_contdiff`/`_deriv`/`_base`, `DeepestGaugeConstruction.lean:313-331`)
is `sorry` — the SHARED PIN1↔PIN2 coupling object: the nonlinear straightened reg-residual reading
reg+spec, with `dE(0)=id`. PIN 1 needs ONLY `dE(0)=id` (pp2 #91 certifies it general-L; PIN 1's peel
is form-agnostic, reviewer-confirmed). PIN 2's squeeze needs its concrete VALUE.

- **#115 (pen-and-paper, in progress, decorrelated from cobuild):** supply the exact closed form (the
  product-residual `∏(I+X_s)−I` read off the gauge slots, OR confirm it's the full `E`) + the two
  consistency checks (dE(0)=id matches #91; ContDiff ⊤ + 0↦0). cobuild consumes → fills the 3 props.
- **PIN 2 (#80, cobuild, gated on #115):** `deepest_loss_squeeze` — the two-sided bound
  `c₁·Φ ≤ loss ≤ c₂·Φ` with `Φ = ∑(regStraighten(split w)).1² + deepestCoreF(coreAbsorb(split w)).2.1`,
  via `fullProduct_loss_squeeze` + `core_comparability_squeeze`. Needs the concrete `deepestEPivot`
  value (so `(regStraightenOf deepestEPivot (split w)).1 = E`). The telescoping `prod H A = P0·∏C·QL`
  is tracked separately (#111).

## PIN 2 E_pivot-INDEPENDENT matrix core (BANKED @3008c64, sorry-free)

Per the team-lead's 2026-06-23 split-by-E_pivot-dependence, the matrix-side squeeze is closed
(`DeepestGaugeBlocks.lean`): `frobenius_sum_reindex` (energy invariant under row/col reindex) +
`frobenius_sq_eq_blocks` (`‖N‖²_F` = the four `r⊕M`-block sum of `N` reindexed) +
`dlnLoss_block_squeeze` (composes those with the banked `fullProduct_loss_squeeze`: `dlnLoss`
two-sidedly bounded by `∑(P00−1,P01,P10)² + ‖Rcore‖²` given the block decomposition + leak hyp). No
`E_pivot` dependence — acts on `dlnLoss`'s own `prod − B`.

## OPEN: the `deepestEPivot` layout obstruction (surfaced to crux2, 2026-06-23)

A load-bearing **soundness obstruction** blocks `deepestEPivot`'s `_deriv` (and hence PIN 1's last prop
+ PIN 2's bridge): `dE(0) = fst` rests on the split's reg slot `Fin nReg` being the STRUCTURED
`(Σ_s X_s, Y_L, Z_1)` layout (g125), but `regGaugeIdxSplit` (`DeepestSplitReindex.lean:236`) is
`Fintype.equivFin`-OPAQUE — its own docstring states the `Fin nReg` half does NOT carry per-layer
`X/Y/Z` structure. The genuine derivative is the rank-`nReg` projection `(all X_s,Y_s,Z_s) ↦ (Σ_s X_s,
Y_L, Z_1)`, which equals `fst` ONLY if the opaque bijection sends the boundary generators to the
`nReg`-half — not guaranteed. Confirmed real: `deepestEPivot = fst + (o(|w|) remainder)` is INCOMPATIBLE
with PIN 2's squeeze (which needs `deepestEPivot ≈ E ≈ Σ X_s ≠ raw reg` at first order — the g161
counterexample). So `dE(0) = fst` requires the reg slot to BE the boundary generators, a coordinate
convention crux2 owns (`DeepestSplitReindex`, single-writer). Awaiting crux2's call: (1) restructure the
reg slot to the legible `(Σ X_s, Y_L, Z_1)` layout, or (2) a pack-by-construction that I'm missing.

## Assembly status

`deepest_gauge_construction` + `deepest_gauge_chart_construct` build GREEN, threading PIN 0
`deepestCoreAbsorb` + PIN 1 `regStraightenOf deepestEPivot` + PIN 2 `deepest_loss_squeeze`. Open
sorries: `deepestEPivot` (def + 3 props, blocked on the layout obstruction) and `deepest_loss_squeeze`
(matrix core banked; the E_pivot-bridge + framed-product bridge remain). PIN 1's IFT peel + PIN 2's
matrix squeeze are banked sorry-free; the gate is the `deepestEPivot` coordinate convention.
