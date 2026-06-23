# cobuild-sub34 gate status — #44c (L2 deepest gauge-chart instance)

Snapshot of what is built vs. gated, for in-repo visibility (not just teammate messages).
Branch: `fm2/deepest-gauge-chart-sub34` @ `c88492e`. As of 2026-06-23.

## TL;DR — the cast-independent lane is CLOSED; one machinery dep remains

Everything cobuild-sub34 can build cast-free is BANKED GREEN sorry-free: PIN 0 (`deepest_coreAbsorb_exists`),
PIN 1 (`deepest_regAbsorb_exists` — the `regAbsorb_rlct` producer, via the IFT adapter
`rlctAtOn_comp_localDiffeo` + `boundedUnit_fderiv_det` + the `DeepestSplit` Haar instance), the PIN 2
matrix core (`dlnLoss_block_squeeze` + `conjugation_frobenius_comparable`), `deepestEPivot` def +
`deepestEPivot_contdiff`, the #95-(I) frames, the gauge-decode contract `deepest_isGaugeSliceDecode`, and
the `deepest_gauge_squeeze_exists` ASSEMBLY (`deepest_gauge_chart_construct`) green-with-3-named-sorries.

The ONLY remaining work is crux2's **3 `prodAux` fold lemmas** (#123, Codex-deferred): value-fold
(→ `deepestEPivot_base`), derivative-fold (→ `deepestEPivot_deriv`, the g239 `D_E` transcription), and
telescope-fold (→ `deepest_loss_squeeze` + PIN 2-B). ALL THREE funnel through the same dependent-Fin
`prodAux` cast (the team-lead-confirmed re-scope: no cast-free lane bypasses differentiating/folding the
`prodAux` product). cobuild WIRES the three on arrival → `DeepestGaugeChart` sorry-free → cert-review.

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

## `deepestEPivot` def + infra (BANKED, sorry-free) + the props

- `deepestEPivot` CONCRETE def + `regResidualPack` @20ad514; `framedParamsReg` (T=0) + `_zero` @2f3508e;
  `contDiff_prodAux_entry`/`contDiff_prod_entry` @9aaead1; `regGaugeSlotCLE` + `contDiff_readX/Y/Z_entry`
  + `contDiff_framedParamsReg_entry` @ecd8d6f.
- **`deepestEPivot_contdiff` PROVED** (sorry-free) @11899a7: `contDiff_pi` over the `Fin nReg` output,
  each coordinate a reindexed `prod`-entry, assembled from the ContDiff product/read infra.

## RESOLVED: the `_deriv` layout obstruction → the SHEAR CLE (crux2 #120, 2026-06-23)

The obstruction I surfaced (`dE(0) = fst` needs the opaque `Fin nReg` to be the `(Σ X_s, Y_L, Z_1)`
boundary generators) was RULED by crux2's #120 (@9d6dc21): **don't restructure the reg slot** (X-sum is
not index-`Equiv`-expressible); instead **CORRECT the `_deriv` spec** — `dE(0)` is the invertible
**unitriangular shear** `[[I, Σ],[0, I]]` (det 1; reg-out = reg-X + Σ gauge-X's, gauge-out unchanged),
NOT `fst`. The IFT peel `rlctAtOn_comp_localDiffeo` takes ANY `≃L`, so the shear closes PIN 1.
**ABSORBED** @416d76b: `regStraightenTotalCLM D_E` + `hasStrictFDerivAt_regStraightenOf_gen` (the total
derivative from `E_pivot`'s reg-derivative `D_E`); `deepest_regAbsorb_exists` takes `D_E` + an invertible
`e` with `(e:→L) = regStraightenTotalCLM D_E`; `deepestEPivot_deriv` bundled `∃ D_E e, … ∧ (e:→L)=…`.
No interface churn left — the spec is settled.

## The remaining `deepestEPivot` props (the two dependent-Fin/shear grinds)

- **`_base`** (`deepestEPivot 0 = 0`): the idempotent product-at-0 fold —
  `prod H (framedParamsReg 0) = reindex(blockdiag[I,0])` (product of `reindex(blockdiag[I,0])` layers,
  idempotent), so the residual `(P11−I, P12, P21) = 0`. A `prodAux` dependent-Fin induction + the
  block-idempotency `fromBlocks 1 0 0 0 ^k = fromBlocks 1 0 0 0` — same difficulty class as the
  telescoping #111.
- **`_deriv`** (the bundled shear): the concrete shear `D_E` + `HasStrictFDerivAt deepestEPivot D_E 0`
  (the #91 block-derivative transcription, `origin/g213-pin1-de0 @09475f2`) + the unitriangular inverse
  `[[I, −Σ],[0, I]]` packaging the invertible `e`. THE analytic gap.

## PIN 2-B frame input COMPLETE (#95 Condition (I), in my tree)

crux2's #95 Condition (I) (@1c23203) is merged + GREEN in my `DeepestFrame.lean`: the three
block-normal companions `deepestPoint_interior_eq_corM` (interior frame = id),
`deepestPoint_layer0_cols_vanish` + `deepestPoint_layerLast_rows_vanish` (the boundary-inner conjuncts,
ENTRY form (A) — my recommended choice-stable shape, last cols/rows zero). So the framed product
telescopes `∏A = P_0⁻¹·(∏corM)·Q_{L-1}⁻¹` with only the 2 endpoint frames surviving. The frame side of
PIN 2-B is fully unblocked.

## NET: the single remaining machinery dependency

After all the convergences (the IFT adapter `rlctAtOn_comp_localDiffeo`, the det-bound
`boundedUnit_fderiv_det`, the `DeepestSplit` Haar instance, `conjugation_frobenius_comparable`,
`dlnLoss_block_squeeze`, the #95-(I) frames, `deepestEPivot_contdiff` — all GREEN on my branch), the
open work funnels through exactly TWO machinery pieces held by the owners:
- **pp2's `D_E`** (the #91 block-derivative in my `regStraightenTotalCLM` encoding) → closes `_deriv`.
- **crux2's #111 `prodAux_succ` cast** (`obtain rfl + rfl`, COMPLETED) → closes `_base` (the idempotent
  fold) AND PIN 2-B's boundary `prodAux` telescoping.
When both land, I wire them into the already-built producer/adapter (closing #82), assemble PIN 2-B
(frames #95-(I) + `conjugation_frobenius_comparable` + `dlnLoss_block_squeeze` + the leak), and ping
crux2 for the #80+#82 cert-review.

## Assembly status

`deepest_gauge_construction` + `deepest_gauge_chart_construct` build GREEN, threading PIN 0
`deepestCoreAbsorb` + PIN 1 `regStraightenOf deepestEPivot` + PIN 2 `deepest_loss_squeeze`. Open
sorries: `deepestEPivot` (def + 3 props, blocked on the layout obstruction) and `deepest_loss_squeeze`
(matrix core banked; the E_pivot-bridge + framed-product bridge remain). PIN 1's IFT peel + PIN 2's
matrix squeeze are banked sorry-free; the gate is the `deepestEPivot` coordinate convention.
