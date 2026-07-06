# D1 step-5 chart-cert de-risk — VERDICT: BOUNDED-MULTI-TIDE (not a wall) (genm-d1chartderisk, 2026-07-06)

Scout de-risk (Codex unavailable — exact source cross-verification on canonical + `genm-hchartexpl` + `genm-hAtV`). Controller-persisted from the agent's report (the agent's worktree lacked the expedition dir).

## Verdict: BOUNDED-MULTI-TIDE — the L=2 D1 ≥-leg chart-cert is a large-but-bounded from-scratch build; ∀-L inherits only the pre-existing #120.

### Q1 — the deepest-analog tell (strongest signal): NOT walled at L=2
`deepest_gauge_squeeze_exists` (`DeepestGaugeChart.lean:353`) is a bare sorry **only because it is the general-L version**, gated on **#120** (the L≥3 grouped recursive diffeo) — bounded-but-unbuilt at L=2, NOT Mathlib-walled:
- `deepest_gauge_construction_L2` (`DeepestL2Wiring.lean:657`) + `_ofBundle` (:132) are **sorry-free / clean-three** (verified: zero bare-sorry in lines 132–701; the only 3 bare sorries — 913/916/1058 — are inside the L≥3 arm). The whole deepest-point L=2 chart pipeline (IFT chart via `rlctAtOn_boundedUnit_localHomeomorph`, MP split, `coreAbsorb` Schur shear, `regStraighten`, spectator peel, core id) was carried to completion at L=2.
- So Item-109's "constant-rank/gauge-chart packaging hits a Mathlib gap" was correct about the general-L IFT route (#120) + the Ψsymm dead-end — NOT about L=2. The "BOUNDED" kill-condition (a Mathlib gap biting at L=2) is NOT met; the packaging is demonstrably available at L=2 via two banked chart-transfer engines (`rlctAtOn_boundedUnit_localHomeomorph`, `rlctAtOn_eq_of_contDiff_chart`).

### Q2 — the explicit chart cert (`hchart_explicit`, step 5): each piece bounded
Downstream `d1ge_L2_hAtV_of_explicit_chart` (`D1L2SchurAssembly.lean:54`) is sorry-free/clean-three/pushed; its 6 hyps are the step-5 data. Discharging:
1. `hchart` — engine `rlctAtOn_eq_of_contDiff_chart` (`S1IFTChart.lean:228`) banked; needs a C²-self-map + invertible derivative + germ. Invertibility = `exists_jacFlatL2_minor` (`D1HChartRank.lean:634`, banked, UNCONDITIONAL at general v, Cauchy–Binet). The abstract analogue `dln_hchart_residual` (`D1HChartResidual.lean:343`) already runs the whole pipeline sorry-free/clean-three.
2. Fresh (not laundered reuse): `dln_hchart_residual` uses `chartΦ` whose inverse is the opaque IFT `Ψsymm` (residual unreadable, `hfact` fails). Route A replaces it with EXPLICIT corner-elimination coords `p=(M11−I,M12,M21)`, residual `qₑ(0,t)=A0red·A1red` readable.
3. `hfact` — algebraic core = banked exact `Core.schur_product_factor`.
4. steps 6–9 (`rlctAt_ge_nReg_add_slice_of_residual`, `rlctAtOn_spectator_peel`, `rlctAtOn_unit_invariant_aux`, `rlctAtOn_comp_homeomorph`, `core_zero_le_of_params`=Thm 4) — all banked/assembled; Route A never computes a degraded M' value (Thm-4 domination) ⟹ UNCONDITIONAL at L=2 (no hbox).

**Genuinely-new labour:** define explicit `qₑ`(p,t) + `Φ_expl` (bump-globalised, ~mirror `dln_hchart_residual`), the germ, + the **essential/flat split `e` + bounded Gram unit `u`** for `hfact`. ~600–1500 LoC / multi-file.

### Q3 — ∀-L
The ∀-L lift (`rlctAt_deepest_le_of_optimal`, Skeleton:1172) = the same corner-elimination iterated; the multi-layer grouped straightening = **#120** (the already-tracked L≥3 wall). No new D1-specific obstruction; L=2 is the bounded base case.

### The one piece most likely to consume tides (the seam)
The essential/flat split (`e`,`u`,`hfact`): `A0red=W−ZX⁻¹Y`, `A1red=V−UM11⁻¹M12` are RATIONAL in the slice coords ⟹ `e` = a rational reindex globalised to a homeomorphism, `u` absorbing the Gram/Jacobian non-orthonormality (modelidwit's Gram-sandwich bounds it). Intricate, NOT a Mathlib gap. De-risk first (a pen-and-paper witness for the rational reindex + bounded Gram unit at (4,4,4)/r=1 — the `genm-splitwit` thread).

### Corroboration
The independent Aoyagi explicit-blow-up route also adjudicated bounded: KC-2 (`genm-d1uniform-aoyagi`) = BLOWUP-UNIFORM (Aoyagi §5's (S,J) induction closes in normal-crossing for every reduced dim vector, no hidden per-v resolution). Two independent routes land D1 ≥-leg bounded.

### Bottom line
The from-scratch D1 ≥-leg at L=2 is CHARGEABLE, NOT a second monument alongside hbox (D1's chart cert has no order-4 pathology, unlike hbox). A large multi-tide chart-cert build heavily reusing banked bricks + a demonstrated L=2 precedent (`deepest_gauge_construction_L2`). Charge step 5; de-risk the `e`/`u`/`hfact` split first.
