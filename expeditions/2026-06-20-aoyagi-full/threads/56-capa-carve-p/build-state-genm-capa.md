# genm-capa build state — #146 cap-A carve: INTERIOR done clean-three, r=2 base is the sole open piece

> **UPDATE (genm-capa2 @ branch `genm-capa2`, off @105cadfd): `schurCoreP_two` CLOSED, sorry-free.**
> `routeMBoxThresholdFinite_rrp` (#146) is now FULLY sorry-free, **clean-three**
> `[propext, Classical.choice, Quot.sound]` (forced `#print axioms`, oleans force-rebuilt:
> CapACarveP/RecStepP/RRP deleted then rebuilt). Whole chain clean: `schurCoreP_two` /
> `schurCoreP_capA` / `schurRecStep_p` / `routeMBoxThresholdFinite_rrp`.
> - **cap-B half** (`c' < p/2`, all p≥4 + small-p slice): 4-chart radial cover at r=2 (cover machinery
>   `matBoxGen_outer_flat`/`gFlatGen_cover_sum` is r-general, NOT hr-gated) + the banked
>   `frobSq_capB_inner_two_le`; the 3≤r-gated `RmatGnorm` avoided by inline row/col-permuting `RmatG`
>   (r-general `RmatG_pivot`/`RmatG_entry_le`). Lemmas: `schurRatioResidP_capB_two_lt_top`,
>   `schur_matBoxGen2_chart_capB_lt_top`, `schurCoreP_two_capB`.
> - **interior half** (`p/2 ≤ c' < schurLambdaP p 2`, only p∈{1,2,3}): took the predecessor's KEY option —
>   reproduced the reshape ONCE at `hr : 2 ≤ r` (NOT literal r=2). The firing's `3≤r` is an artefact
>   (bodies need only `0<r`/`1≤r`/`0<r*r`); copies suffixed `2`: `RmatGnorm2`/`slotMatG2`/`cellR2`/
>   `zσG2`/`zEG2` + readbacks `RmatGnorm2_carve_M22/g/b`/`ScCarve2_eq`, then the carve chain
>   `innerSGenCarve2_le` (via the landed `1≤r` shears `frobSqTopRowP_eq_shearP1`/`stepShearP_r1`),
>   `resolvedShiftRG2_le` (+ `schurResidGP2_translate_le`/`coreSchurGenValP2_lt_top`),
>   `schurRatioResidGen2_mid`/`schurRatioResidGen2`, `schur_matBoxGen2_chart_capA_lt_top`,
>   `schurCoreP_two_interior`. NO cast thrash — the `2≤r` (vs literal r=2) route kept indices generic
>   `Fin (r-1)`, sidestepping the Fin-1-collapse cast-risk; built first try after each sub-lemma.
> All `2≤r` copies are verbatim-from-firing with `3≤r → 2≤r`; reusable for a future unified `2≤r` carve.


Branch: `genm-capa` (off `origin/genm-pbuild2`@04c2eb85). Tip after this thread: `bfe1ff14` (pushed).
Do NOT edit `genm-pbuild`/`genm-pbuild2` or `RouteMSchurFiring`/`RouteMSchurDirectMorseP` (siblings;
single-writer firing).

## LANDED clean-three `[propext, Classical.choice, Quot.sound]` (forced `#print axioms`, olean-rebuilt)

New file `RouteMSchurCapACarveP.lean` (1167 LoC). All sorry-free EXCEPT `schurCoreP_two`:
- `coreJoinGP`/`coreEntryPolyGP`/`frobSqGP_ne_zero_ae`/`frobSqShiftGP_ne_zero_ae` — `Fin p` a.e.-positivity.
- `resolvedShiftRGP_le` — JOINT brick: `core_T_peel_le_aeG (m:=p-1)` (subst `p=pm+1`) + DONE `schurResidGP_translate_le`.
- `matBox_rowperm_lintegralGP` / `innerSGenP_eq_norm` — pivot-normalised inner-S form (reuses `frobSq_rmatMul_permGP`).
- **`innerSGenCarveP_le`** — the N2b carve heart. The `4→p` lift was DEFEQ-trivial: `RmatGnorm`/`zEG`/
  `bgShiftG`/`ScCarve_eq`/`RmatGnorm_carve_*`/`zEG_fst/snd_apply` REUSED VERBATIM from the firing (they're
  `S`-width-free). Only `schur_minorPivot_split (p:=p)`, `frobSqTopRowP_eq_shearP`, `stepShearP_r` swapped.
- `schurRatioResidGenP_mid` + `schurRatioResidGenP` (subcritical fold; needs `hmid : p/2 < schurLambdaP p r`).
  IH arithmetic: `schurLambdaP_peel_le p (j:=1) : schurLambdaP p r ≤ p/2 + schurLambdaP p (r-1)` ⟹
  `c'-p/2 < schurLambdaP p (r-1)`.
- `schur_matBoxGenP_chart_capA_lt_top` — cap-A per-chart (mirror DirectMorseP's `schur_matBoxGenP_chart_lt_top`,
  swap cap-B residual → `schurRatioResidGenP`; radial cap `c'<r²/2` via `schurLambdaP_le_sq`).
- `schurCoreP_capA_interior` — r≥3 `r²`-chart cover (mirror `schurCoreP_directMorse`).
- `schurCoreP_one` (+ `schurLambdaP_one : schurLambdaP p 1 = 1/2`, `schurOneP_morse_lt_top`, `frobSq_one_eqP`) —
  `Fin p` corank-1 Morse leaf.
- `schurCoreP_capA'` — the FULL dispatch: p=0 vacuous (`schurLambdaP_p_zero`), r=0 vacuous, r=1 leaf, r=2
  `schurCoreP_two`, r≥3 internal `le_or_gt (schurLambdaP p (n+3)) (p/2)`: cap-B `schurCoreP_directMorse` |
  interior `schurCoreP_capA_interior`.
- **r=2 cap-B bricks (BANKED, clean):** `frobSqTopRowP_eq_shearP1` / `stepShearP_r1` (the `1≤r` relaxations of
  the directMorse shears) + `frobSq_capB_inner_two_le` (the `z`-uniform N2b→shear→Morse-dominator bound at
  r=2, `c'<p/2`). These are the cap-B half of `schurCoreP_two`, ready to wire.

`RouteMSchurRecStepP.lean`: `schurCoreP_capA` now `:= schurCoreP_capA' p r hIH c' hc0 hc' T hT` (its sorry GONE).
`routeMBoxThresholdFinite_rrp` / `schurRecStep_p` / `schurCoreP_capA` carry `sorryAx` ONLY via `schurCoreP_two`
(NO `monomial_rlct` at this layer). Module-closure green (8292 jobs); no name clashes (grep + closure build).

## THE ONE OPEN SORRY: `schurCoreP_two` (line ~1136, the r=2 corank-2 base)

`SchurCore p 2 c' T` for `0 < c' < schurLambdaP p 2`. `schurLambdaP p 2 = min(4,1+p,2p)/2`:
p=1→1, p=2→3/2, p=3→2, p≥4→2. The carve (RmatGnorm/zEG) is hr:3≤r-GATED in the firing ⟹ doesn't fire at r=2.

### Two regimes (split on `le_or_gt c' (p/2)` — or on `schurLambdaP p 2 ≤ p/2`):
- **cap-B (`c' < p/2`):** = ALL of p≥4 (`schurLambdaP p 2 = 2 ≤ p/2`) + the `c'<p/2` slice of small p. A 4-chart
  radial cover at r=2: `matBoxGen_outer_flat 2 p` + `gFlatGen_cover_sum 2 p` (r-general, NO hr) → 4 charts;
  per chart `chart_integrand_factorGen 2 p` (r-general) → radial axis (`radial_aAxis_divisor_lt_top 2`, `c'<2`)
  × `∫_z innerSGenP 2 p`; the angular residual = a `z`-uniform bound from the LANDED `frobSq_capB_inner_two_le`
  (per z, `RmatG 2 pivot (e.symm(0,z))` has pivot 1 + entries ≤1 via `RmatG_pivot`/`RmatG_entry_le`; swap
  pivot to (0,0) via `frobSq_rmatMul_permGP`+`matBox_rowperm_lintegralGP`, then `frobSq_capB_inner_two_le`),
  integrated over the finite ratio box. MIRROR `schurRatioResidP_capB_lt_top` + `schur_matBoxGenP_chart_lt_top`
  at r=2 (those carry hr:3≤r via RmatGnorm — rewrite using `RmatG` directly, pivot-swap). ~120 LoC, mechanical.
- **interior (`p/2 ≤ c' < schurLambdaP p 2`):** ONLY p∈{1,2,3}. Needs the r=2 carve = an `r=2` (or `2≤r`)
  copy of the cube reshape `RmatGnorm2`/`slotMat2`/`cellR2`/`zσ2`/`zEG2`/`RmatGnorm_carve_*2`/`ScCarve2_eq`
  (firing lines 956–1504, swap `3≤r → 2≤r`, `3*3≤r*r → 2*2≤r*r`; `Fin (r-1)=Fin 1` collapses help) +
  `innerSGenCarve2_le` + `schurRatioResidGen2_mid` (reuse the LANDED `resolvedShiftRGP_le`… BUT it carries
  hr:3≤r — also needs a `2≤r` copy, OR `schurResidGP_translate_le`/`coreSchurGenValP_lt_top` at `2≤r`).
  ~200 LoC, cast-heavy (the opaque-width territory CLAUDE.md flags). NO RESEARCH WALL.

### CHEAPEST ROUTE (Codex xhigh, scoping-answer.md + r2base-answer.md):
- Codex R2 (manual 4-chart at r=2) is cheapest; the chart change-of-variables/Jacobian is the hardest step.
- KEY UNEXPLORED OPTION (Codex scoping, med-high confidence): RELAX the firing carve to `2≤r`. I could NOT
  (firing is single-writer), but a CLEANER fix exists: reproduce the reshape ONCE at `hr:2≤r` in
  RouteMSchurCapACarveP (RmatGnorm2/slotMat2/zEG2 etc.), then BOTH r=2 interior AND a future unified carve
  use it. The `2≤r` reshape closes the default-branch `slotMat` index bound (`2*2=4>1`) cleanly.
- The cap-B half is ALREADY banked (`frobSq_capB_inner_two_le`); wire it first (closes p≥4 entirely + the
  `c'<p/2` slice), then the interior small-p carve.

Codex artefacts: `codex/scoping-{prompt,answer}.md`, `codex/r2base-{prompt,answer}.md`.

RESUME from `@bfe1ff14`: build `schurCoreP_two` (cap-B wire from the landed brick, then the r=2 cube-reshape
for interior p∈{1,2,3}); when it's sorry-free, `routeMBoxThresholdFinite_rrp` (#146) is FULLY sorry-free.
Best as a focused fresh tide (cast-heavy reshape), not the tail of the heart session.
