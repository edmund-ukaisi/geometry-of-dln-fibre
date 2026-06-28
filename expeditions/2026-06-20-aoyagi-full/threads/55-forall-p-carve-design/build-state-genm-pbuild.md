# genm-pbuild build state — #146 (r,r,p) ∀p directMorse leg (live)

Branch: `genm-pbuild` (worktree `/home/ubuntu/workspace/genm-pbuild-wt`; created after the
`.claude/worktrees/genm-assemble` worktree was switched to `genm-l2wire2` — pushed work was safe).
Base: capstone @c2777384 + grafted genm-n4 box files (Item-58 green-confirmed, closed carve intact).

## LANDED (sorry-free, clean-three [propext, Classical.choice, Quot.sound], pushed)

- `RouteMSchurThresholdP.lean` (piece iv) — the full ∀p threshold arithmetic (schurLambdaP, the 3
  SchurThreshold fields incl. keystone `minAdm_rrp_subadd`, `schurLambdaP_four_eq`).
- `RouteMSchurDirectMorseP.lean`:
  - shared Fin-p plumbing (3/3): `frobSqTopRowP_eq_shearP`, `stepShearGP`/`stepShearP_r`,
    `innerSGenP`/`measurable_innerSGenP`.
  - **`frobSq_capB_inner_lt_top`** (the genuinely-new cap-B inner bound, @2feb12cb): for R (r≥3, pivot 1,
    |entries|≤1) and c'<p/2, `∫_{S∈matBox r p T} frobSq(R·S)^{−c'} < ⊤`, NO recursion. Codex route B (keep
    residual + `radial_morse_dominates_absZ_lt_top`; route A drop-residual is WRONG — zero-guard false).

## REMAINING (the directMorse assembly + carve-peel + dispatch + hfin)

1. **`frobSq_capB_inner_le` (REFACTOR — load-bearing for the cover).** The `_lt_top` form does NOT compose
   for the z-box integration (it gives `< ⊤` per z, not a z-uniform constant). Restate as a `_le` to the
   z-UNIFORM bound `ENNReal.ofReal(c₀^{−c'}) · Kbound p c' (r·T) · vol(matBox (r-1) p (r·T))` — using
   `radial_morse_dominates_absZ_le` (gives `≤ Kbound (m+1) c' Tp * μ Z`, W-INDEPENDENT hence z-uniform;
   c₀ is the chart-wide constant, z-free). This is the composable form. [LOW-MED — same proof, `_lt_top` →
   `_le` ending at the explicit bound.]
2. **`schurRatioResidP_capB_lt_top`** (the per-chart angular residual, SPECIFY was validated then lost in
   the worktree switch — re-add): `∫_z innerSGenP r p c' T pivot ((piRatioG r N hN pivot).symm (0,z)) < ⊤`
   for c'<p/2. Per z, R := RmatGnorm (pivot 1 by `RmatGnorm_pivot`, bounded by `RmatGnorm_offpivot_le`) →
   `frobSq_capB_inner_le` gives a z-uniform constant → integrate over the finite-volume ratio box
   (`lintegral_const` × finite vol). [MED — the per-z setup mirrors `schurRatioResidGen_mid`'s carve CoV,
   but simpler: no IH, no Sc readback chain.]
3. **`schurCoreP_directMorse`**: `SchurCore p r c' T` for 0<c'<min(p,r²)/2. `matBoxGen_outer_flat` +
   `gFlatGen_cover_sum` (DONE p-general, RouteMSchurGenCover) → r² charts; each = radial axis
   (`radial_aAxis_divisor_lt_top`, DONE, c'<r²/2) × `schurRatioResidP_capB_lt_top` (c'<p/2);
   `ENNReal.sum_lt_top`. Mirrors `schurCoreGen_firing`. [MED — the chart-level reduction
   (`chart_integrand_factorG`/piRatioG) is the intricate part; reuse the firing's `schur_matBoxG_chart_lt_top`
   structure.]
4. **cap-A carve-peel** `schurRatioResidGenP_mid` (the `4→p` of schurRatioResidGen_mid, hc2: p/2<c') — reuses
   plumbing 1/2/3 + the carve (p-free) + innerSGenP + the IH + the residual (NOT dropped). The LARGE-by-LoC
   piece but mechanical (angular machinery p-free; only the S-integrand chain needs Fin p).
5. **`schurRecStep_p`** dispatch: `rcases le_or_lt (lam r) (p/2)` → directMorse | peel; r=0 vacuous; 1≤p.
   Then `core_schurGen_lt_top (p) (schurLambdaP p) (schurLambdaP_satisfies_threshold p) schurRecStep_p`.
6. **`routeMBoxThresholdFinite_rrp`** = generalize genm-n4's `eParamsRR4`/RR4 box reshape `4→p`, instantiate
   `routeMCore_threshold_lt_top` at M=![r,r,p].

Codex artefacts: `codex/directMorse-{design,assembly}-{prompt,answer}.md`. Design: §9–§13 on genm-assemble-design.
§12 NOTE TO UPDATE: the cap-B route KEEPS the residual (uses the antitone abs-Z Morse dominator), it does
NOT "drop residual" as §12 sketched — the drop-residual zero-guard is false (Codex route A).


## UPDATE (live) — directMorse down to ONE assembly lemma

LANDED since the last note (all sorry-free, clean-three, pushed to genm-pbuild):
- `frobSq_capB_inner_le` — the z-UNIFORM composable bound (ofReal(c₀^{−c'})·Kbound·vol, R-free via the
  W-independent abs-Z dominator `radial_morse_dominates_absZ_le`).
- `frobSq_rmatMul_permGP` — Fin-p row/col perm of frobSq(R·S) (shared plumbing).
- `schurRatioResidP_capB_lt_top` — the per-chart cap-B angular residual: per z, innerSGenP = ∫_S
  frobSq(RmatGnorm·S)^{−c'} (Fin-p row-perm MP + frobSq_rmatMul_permGP); RmatGnorm pivot-1 + bounded →
  frobSq_capB_inner_le bounds by the z-uniform C; integrate C over the finite ratio box. DONE.

REMAINING in directMorse: ONLY `schurCoreP_directMorse` (the chart-cover assembly). Inputs all landed:
- the cover `matBoxGen_outer_flat` + `gFlatGen_cover_sum` (DONE (r,p)-general),
- the radial axis `radial_aAxis_divisor_lt_top` (DONE),
- the angular residual `schurRatioResidP_capB_lt_top` (just DONE).
The assembly mirrors `schur_matBoxG_chart_lt_top` (RouteMSchurFiring:1982): per chart, `pivotBlowupOnDeriv_det
= |y p|^{r²−1}` + `chart_integrand_factorG` (needs the (r,p) gFlatGen analog) + the `piRatioG` Tonelli split
(a-axis divisor × ratio residual). The intricate per-chart reduction — the one remaining directMorse piece.
Then cap-A carve-peel + dispatch + routeMBoxThresholdFinite_rrp.


## schurCoreP_directMorse — the precise remaining chart-cover chain (resumption detail)

The ONE remaining directMorse lemma. It mirrors `schur_matBoxG_chart_lt_top` (RouteMSchurFiring:1982) +
`schurCoreGen_firing` (:2063), but the per-chart factor machinery is `gFlatG`/`innerSGen`-based (Fin-4) and
must be `gFlatGen`/`innerSGenP`-generalized. Sub-lemmas to transcribe (each a mechanical gFlatG→gFlatGen /
innerSGen→innerSGenP / 4→p swap, but cast-heavy — the pivotBlowupOn/piRatioG opaque-width territory):

1. `gFlatGen_blowup_radial` — the (r,p) analog of `gFlatG_blowup_radial` (gFlatGen at the blow-up point =
   (y_p)²-radial × innerSGenP). [the gFlatGen blow-up identity]
2. `flatBoxGen_blowup_mem_iff` — the (r,p) analog of `flatBoxG_blowup_mem_iff` (membership ⟺ |y_p|≤T).
   [likely p-FREE — it's about the flat box, check if reusable as-is]
3. `chart_integrand_factorGen` — the (r,p) analog of `chart_integrand_factorG` (41 lines; the per-chart
   factor = radial indicator × innerSGenP). Uses 1+2.
4. `schur_matBoxGenP_chart_lt_top` — the (r,p) analog of `schur_matBoxG_chart_lt_top` (~120 lines; the
   piRatioG MP + Tonelli a-axis(radial_aAxis_divisor_lt_top, c'<r²/2) × ratio-residual
   (schurRatioResidP_capB_lt_top, c'<p/2) split). The intricate core.
5. `schurCoreP_directMorse` = `rw [SchurCore, matBoxGen_outer_flat, gFlatGen_cover_sum]` +
   `ENNReal.sum_lt_top` over the r² charts, each by (4). Trivial given (4).

RISK: cast-heavy (the pivotBlowupOn/piRatioG/opaque-width quirk, CLAUDE.md). Mechanical but detailed —
best done fresh, not at the tail of a long session. NO research wall. After it: cap-A carve-peel + dispatch
+ routeMBoxThresholdFinite_rrp.
