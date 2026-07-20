# Cert — region-glue tide, scoped fidelity audit

Reviewer (independent, scoped fidelity). Branch `expedition/aoyagi-engine--revglue`, worktree
`/home/ubuntu/workspace/rev-glue-wt`. Date 2026-07-18.

**VERDICT: scoped-VALIDATE.** The `region_glue` discharge from `ChartBridge` is sound and faithful;
the gate clears for wiring `region_glue := region_glue_of_chartBridge (resolutionOf M) …`. Two
minor prose notes (report-only, non-blocking) below. No fidelity mismatch, no soundness break, no
laundering.

## Evidence base

- Build: `./scripts/lb DLNFibre.DLN.RLCT.Engine.RegionGlueAssembly` → exit 0 (whole chain green,
  ~8561 modules). The four subject modules `Built` clean; the only sorries in the cone are
  `EngineObligations` L27 (`monomialization_terminates`) and L89 (`region_glue` itself — still
  sorried, as expected; discharging it is what this gate authorizes) plus unrelated pre-existing
  sorries elsewhere (Skeleton, DeepestGaugeChart, RouteMSchur…).
- Forced `#print axioms` (reviewer scratch, since removed): BOTH
  `region_glue_of_chartBridge` and `leaf_chart_image_lintegral_lt_top` →
  `[propext, Classical.choice, Quot.sound]`. No `sorryAx`.
- Decorrelated Codex (xhigh) on the signature-fit questions (items 1+2): FIT across the board.
  Artefacts: `codex/revglue-sigfit-{prompt,answer}.md`.

## Item 1 — `region_glue_of_chartBridge` fidelity to `region_glue`'s contract: VALIDATE

`region_glue_of_chartBridge` (`RegionGlueAssembly.lean:84`) has, with `t := resolutionOf M`:
`hbridge : ChartBridge M t`, `c' : ℝ`, `hrat : ∀ e ∈ terminalExponents t, c' < e/2`, conclusion
`routeMLayerBoxIntegral M c' 1 < ⊤` — matching `region_glue` (`EngineObligations.lean:89`) binder
for binder. Verified operationally: a scratch `example` reproducing `region_glue`'s statement
verbatim, discharged by `region_glue_of_chartBridge (resolutionOf M) hbridge c' hrat`, ELABORATED
(build exit 0). The proposed one-line discharge typechecks. Codex FIT.

## Item 2 — `leaf_chart_image_lintegral_lt_top` hypothesis-tuple fidelity: VALIDATE

The eight `ChartBridge` per-leaf conjuncts (`EngineDefs.lean:79-85`: `MeasurableSet srcBox`;
bounded-cube `∃R>0, srcBox ⊆ pf⁻¹ cubeBox R`; `Injective divCoord`; `Injective resCoord`;
`Disjoint (range divCoord) (range resCoord)`; `∃N, volume N = 0 ∧ InjOn chartMap (srcBox\N)`;
`LeafPullback`; `LeafJacobian`) are EXACTLY the eight non-ratio hypotheses of
`leaf_chart_image_lintegral_lt_top` (`RegionGluePerLeaf.lean:119-128`), same order — the assembly's
`obtain ⟨hsrcM, hbdd, hdcInj, hrcInj, hdisj, hnull, hlp, hlj⟩ := hleaf l hl`
(`RegionGlueAssembly.lean:118`) destructures cleanly. None stronger than the bridge supplies; none
weaker than soundness needs.

The two ratio hypotheses `hdivExp : ∀ k, c' < divExp k/2` and `hres : 0 < resRank → c' < resRank/2`
are NOT in `ChartBridge` — the assembly derives them from `hrat` over
`terminalExponents t = (leaves t).flatMap (map divExp (finRange numDiv) ++ if 0<resRank then
[resRank] else [])` (`ResolutionTree.lean:268`) via correct membership witnesses
(`RegionGlueAssembly.lean:120-123`): `divExp k` through flatMap→append-left→map;
`resRank` (under `0 < resRank`) through flatMap→append-right→`if_pos`→singleton. Every exponent the
lemma needs bounded is in `terminalExponents`; no missed threshold. Codex FIT.

## Item 3 — non-laundering: VALIDATE

- `#print axioms` clean-three on both theorems (above). The glue theorems are parametric in
  `t`/`l`/`hbridge`/`hrat` and never call `resolutionOf` or `region_glue`, so they do not inherit
  `sorryAx` from the imported (sorried) `EngineObligations`.
- `grep -niE 'rlct|cited_aoyagi_dln|monomial_rlct|rlctAt|c\*'` across the four files: only "RLCT"
  namespace/path tokens — no consumption of the cited RLCT equality or any `rlct = c*` object.
- ℕ-subtraction→rpow (`RegionGluePerLeaf.lean:172`): `hdivpos : ∀ k, 1 ≤ divExp k` is DERIVED
  (`divExp k = 0` ⟹ `hdivExp k : c' < 0`, contra `hc' : 0 < c'`), not assumed; `Nat.cast_sub
  (hdivpos k)` (L217) and `Real.rpow_natCast` then convert `|u|^(divExp k − 1 : ℕ)` to
  `|u|^((divExp k:ℝ)−1−2c')` soundly.

## Item 4 — elder-checklist conformance: VALIDATE (one meaning-preserving route note)

- N̄ measurable-superset: `exists_measurable_superset_of_null hNnull`
  (`RegionGluePerLeaf.lean:135`). ✓
- `residualCore` never integrated: bounded pointwise via the LeafPullback squeeze in `hpt`
  (L174-235); only the measurable `|det Dcomp| · frobSq(chartMap ·)^(−c')` is integrated
  (`hbound`, L237). Uses only the LOWER squeeze `loP·base ≤ rcore` to bound `rcore^(−c')` above via
  `rpow_neg_antitone`; the UPPER squeeze `hiP` and `ψsymm`/lower-`det` bound are carried but unused
  — matching `LeafJacobian`'s "carried but not load-bearing" docstring. ✓
- Null-image discard: `chartMap '' srcBox = chartMap ''(srcBox\N̄) ∪ chartMap ''(srcBox∩N̄)`,
  second image null via `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`
  (L154-158); area formula `lintegral_image_eq_lintegral_abs_det_fderiv_mul` on `srcBox\N̄`
  (L161). The FULL image is covered (null part contributes 0). ✓
- Coordinate handling: the checklist's "Tonelli via injective/disjoint coords" was IMPLEMENTED as a
  split-free AM-GM domination (`model_read_lt_top`, `RegionGlueModelRead.lean:215`) — the Morse
  factor `(∑ x_{rc i}²)^{−c'}` dominated a.e. off the coordinate hyperplanes
  (`Measure.ae_eval_ne`), collapsed to a single all-axis product by the two-family reindex
  `prod_two_family_eq` (injective/disjoint coords load-bearing HERE), closed by
  `prod_abs_rpow_cube_lt_top`. This is a meaning-preserving route deviation from the checklist
  sketch; the injective/disjoint hypotheses remain load-bearing and the proven statement is
  unchanged. Not a fidelity break.
- Finite-leaves cover, no subcover extraction: `lintegral_leaves_cover_lt_top` is a `List`
  induction over `leaves t` on `lintegral_union_le` (`RegionGlueAssembly.lean:51`). ✓
- Scaling-bridge globalization: `routeMLayerBoxIntegral_lt_top_of_small_box`
  (`RegionGlueGlobalize.lean:89`). ✓
- Corners: `c' ≤ 0` (`routeMLayerBoxIntegral_nonpos_lt_top`, compact/continuous bound) and `L = 0`
  (`RegionGlueAssembly.lean:92-104`, constant integrand) both present. ✓

## Item 5 — bedrock/wording: VALIDATE (two minor prose notes, report-only)

- Banned-wording grep clean on the four glue files. Single hit `EngineDefs.lean:56`
  "not load-bearing" is an object-level factual claim (which hypothesis data the proof uses) — keep.
- NOTE (name=content, non-blocking): `RegionGlueAssembly.lean:18` and `:81` state the L=0 corner as
  "`prod M A = 1`". For `L=0`, `prod M A = prodAux M A 0` is a constant base matrix (the `[I|0]`
  base), independent of `A` — not the scalar `1`. The proof correctly proves and uses only
  CONSTANCY (`prod M A = prod M 0`, `rfl`), so soundness is unaffected; recommend rewording to
  "`prod M A` is constant in `A`". Report-only.
- No other overclaim; docstrings' names match their content, and the `LeafJacobian` docstring is
  honest about its unused inverse data.

## Scope

This certifies `region_glue`'s PROVABILITY-FROM-`ChartBridge` and the fidelity of the discharge
chain. It does NOT certify the construction (`monomialization_terminates`) can satisfy
`LeafPullback`/`LeafJacobian`'s monomial assertions — rung 3-4's burden, out of this scope.
