# genm-pbuild2 build state — #146 (r,r,p) ∀p directMorse CLOSED + deliverable skeleton

Branch: `genm-pbuild2` (branched from `origin/genm-pbuild@55454923`; do NOT edit `genm-pbuild`).
Continues the predecessor's `build-state-genm-pbuild.md`.

## LANDED clean-three `[propext, Classical.choice, Quot.sound]` (force-rebuilt `#print axioms`)

In `RouteMSchurDirectMorseP.lean` (the 5-sub-lemma chart-cover chain — directMorse CLOSED):
- `gFlatGen_blowup_radial`, `flatBoxGen_blowup_mem_iff`, `chart_integrand_factorGen` (sub-lemmas 1–3).
- `innerSGenP_offpivot` (the `y pivot`-invariance helper).
- `schur_matBoxGenP_chart_lt_top` (sub-lemma 4, the `piRatioG` Tonelli a-axis×ratio split, ~120 lines).
- **`schurCoreP_directMorse`** (sub-lemma 5, the chart-cover assembly) — THE LAST directMorse lemma.

**Key simplification found:** `matToFlatGen r = matToFlatG r`, `flatBoxGen r T = flatBoxG r T`,
`gFlatGen r 4 = gFlatG r` are ALL `rfl` (defeq) — so `RmatG` / `RmatGnorm` / `piRatioG` / `pivotBlowupOn(Deriv)`
/ all the `piRatioG_*` helpers are reused DIRECTLY, no `(r,p)` re-derivation. The 4 sub-lemmas were
near-verbatim `4 → p` transcriptions; sub-lemma 4 (the 120-line core) compiled first try.

In `RouteMBoxThresholdRRP.lean` (the #146 reshape, clean-three):
- `eParamsRRP` / `measurePreserving_eParamsRRP` / `eParamsRRP_preimage_box` / `prod_two_layer_rrp` /
  `frobSq_prod_eq_eParamsRRP` / `routeMLayerBoxIntegral_rrp_eq` — `4 → p` of the RR4 reshape.
- `minAdm_rrp_half_eq` (`½·minAdm(![r,r,p]) = schurLambdaP p r`, by `rfl` from the `schurLambdaP` def).

In `RouteMSchurCapAP.lean` (the cap-A leaf bricks, clean-three, NO sorry):
- `coreSchurGenValP` / `coreSchurGenValP_lt_top` (finite from the width-`p` IH at `j=1`) /
  `schurResidGP_translate_le` (shift-uniform domination into the IH box, via `matBoxSq_translate_le`).
  These are the recursion-facing `4 → p` leaf bricks the cap-A carve stands on (no N2b, no `zEG`).

## LANDED with documented `sorryAx` (cap-A ONLY)

In `RouteMSchurRecStepP.lean`:
- **`schurRecStep_p (p) : SchurRecStep p (schurLambdaP p)`** — the dispatch. `le_or_gt (schurLambdaP p r) (p/2)`:
  cap-B (`≤ p/2`, `r ≥ 3`) is `schurCoreP_directMorse` (REAL, no recursion; both caps fire:
  `c' < lam r ≤ p/2` and `c' < lam r ≤ r²/2` via `hlam.radial_le`). The interior stratum (`> p/2`) and the
  corank leaves `r ∈ {1,2}` route to `schurCoreP_capA` (the open carve, `sorry`).
- `schurCoreP_capA` — the SOLE sorry. Conclusion `SchurCore p r c' T` for `c' < schurLambdaP p r`.

In `RouteMBoxThresholdRRP.lean`:
- **`routeMBoxThresholdFinite_rrp (r p) : RouteMBoxThresholdFinite (![r,r,p])`** — the #146 deliverable
  SKELETON. `sorryAx` ONLY via `schurCoreP_capA`; the reshape + cap-B `schurCoreP_directMorse` it wires
  in are clean-three.

## REMAINING: `schurCoreP_capA` (the `4 → p` cap-A carve + the `r∈{1,2}` leaves)

The `4 → p` transcription of `RouteMSchurFiring`'s cap-A carve chain (`schurRatioResidGen_mid` ~190 LoC +
its deps, ~lines 727–1900 in `RouteMSchurFiring.lean`, ~800–1170 LoC total). The leaf bricks above are done.
Remaining sub-chain (each a `4 → p` swap; Morse block `Fin 4 → Fin p`, threshold `2 = 4/2 → p/2`, IH
`SchurLowerIH 4 schurLambda → SchurLowerIH p (schurLambdaP p)`):
1. `innerSGenP_eq_norm` — the pivot-normalised form (`4 → p` of `innerSGen_eq_norm`, :998).
2. `zEGP` + `measurePreserving_zEGP` + `zEG_*_apply` analogs — the `z ↦ (M,v)` carve CoV (`def zEG`, :1315);
   p-FREE (it reshapes the `r²−1` ratio coords, not the `S`-width) — likely reusable AS-IS (`zEG` is `S`-free).
3. `core_T_peel_le_aeG` — ALREADY `(m+1)`-general (Morse `morseBox (m+1)` at threshold `(m+1)/2`); instantiate
   `m+1 = p`. NO transcription.
4. `bgShiftG` / `bgShiftG_entry_le` (:1212) — `S`-free, reusable AS-IS.
5. `resolvedShiftRG_le` (:875) — the JOINT brick (a.e. peel + `schurResidGP_translate_le`); `4 → p` swap, uses
   `core_T_peel_le_aeG` (p-general) + the DONE `schurResidGP_translate_le` + `coreSchurGenValP`.
6. `innerSGenCarveP_le` (:1515, ~150 LoC) — the N2b minor-pivot split + `Fin p` top-row shear. The heart;
   SHARES the N2b machinery with the DONE cap-B `frobSq_capB_inner_lt_top` (same `schur_minorPivot_split` j=1,
   same `frobSqTopRowP_eq_shearP`); the difference is cap-A KEEPS the residual (→ `resolvedShiftRGP_le`).
7. `schurRatioResidGenP_mid` (:1710, ~190 LoC) + the `c' ≤ p/2` subcritical wrapper (`schurRatioResidGen`, :1902).
8. `schur_matBoxGenP_chart_capA_lt_top` — the cap-A per-chart (REUSE `schur_matBoxGenP_chart_lt_top`'s
   structure; swap the ratio residual `schurRatioResidP_capB_lt_top → schurRatioResidGenP`).
9. `schurCoreP_capA` for `r ≥ 3 ∧ lam r > p/2` = the cover sum (mirror `schurCoreGen_firing`).
10. The `r ∈ {1,2}` `(r,p)` leaves (`schurCoreP_one`, `schurCoreP_two`) — `4 → p` of `schurCore4_one/_two`.

RISK: cap-A is recursion-driven (the IH `M22 ↦ Sc` translation-domination) AND cast-heavy (the same
`pivotBlowupOn`/`piRatioG`/opaque-width territory). Best as its own focused tide, NOT the tail of a session.
NO research wall — the truth-value is banked (the firing proves it at `p=4`); it is a mechanical (large) lift.
