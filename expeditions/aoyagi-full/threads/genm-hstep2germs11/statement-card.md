# Statement card — genm-hstep2germs11 (#120 `hstep2`, item 2 = the `hsub3reg` germ COMPLETE)

**Status:** Producer 2 of 3 (the `hsub3reg` reg-preservation germ) **COMPLETE, sorry-free,
axiom-clean** `[propext, Classical.choice, Quot.sound]` (forced `#print axioms hsub3reg_gen_germ`
loses `sorryAx`). **Fidelity REVIEWED — SURVIVED** (reviewer thread: all 5 questions PASS +
decorrelated Codex no-vacuity read; the `∀ᶠ` neighborhood is genuinely non-trivial, the bundle
hypotheses are jointly realized by `deepestPoint_frame_pivot_triangular_exists` so not vacuous, and
the corner value-lemmas are non-circular). `hstep2` (`DeepestL2Wiring:1060`, L ≥ 3 arm) **LEFT
UNTOUCHED** — the compose needs the diffeo triple (Producer 1) which is a multi-thread wall (see below).

**Reviewer follow-ups (both benign):** (i) the L≥3 compose must do the `hregval` rewrite (the germ is
in `deepestEFull` form; `deepest_diffeo_bridge_gen_assembled` wants `regStraighten` form — unlike the
L=2 assembled bridge which converts internally); (ii) wire the leaf module into the build root /
`AxCheck` so it does not silently rot (nothing imports it, so the aggregate build does not re-check it).

Branch: `genm-hstep2germs11` (pushed, @ `1b2da945`). Base: `origin/expedition/aoyagi-full` @ `a869dbf9`.

## File delivered

- `lean/DLNFibre/DLN/RLCT/Validate/DeepestChainUnitGerm.lean` (new, ~731 L, 0 sorry) — the base-chain
  eventual-unit infrastructure + the concrete general-`L` reg-preservation germ `hsub3reg`.
  STANDALONE (builds via `scripts/lb`, force-recompiled green; no name clashes with siblings). **NOT yet
  imported into `DLNFibre.lean`** — the controller wires it (single-writer).

## Theorems delivered (one line each)

Reusable infrastructure (Codex-flagged as reused by Producers 1b and 3):
- `eventually_isUnit_of_continuousAt_det` — generic: `det` continuous at `x₀` + `det(M x₀) ≠ 0` ⟹ `M`
  eventually a unit (`ContinuousAt.eventually_ne` + `Matrix.isUnit_iff_isUnit_det`).
- `contDiff_deepestChain_framedParamsPivot_entry` — each base-chain entry is `ContDiff ⊤` in the split
  parameter (`k < L` reindex of `contDiff_framedParamsPivot_entry`; `k ≥ L` constant corner).
- `contDiff_partProd_entry` — each `partProd` entry `ContDiff ⊤` (prefix-length induction, matrix mul).
- `contDiffAt_matrix_det_of_entries_at` — `ContDiffAt` analog of `contDiff_matrix_det_of_entries`.
- `reindex_symm_fromBlocks_one_eq_corner` — `reindex(rThr.symm)(rThr.symm)(fromBlocks 1 0 0 0) = corner`.
- `deepestChainLayer_corner_toBlocks₁₁` / `_toBlocks₂₁` — the reindexed corner's `(1,1) = I` / `(2,1) = 0`.
- `framedParamsPivot_wstar_eq_corner` — the framed chain layer at the basepoint IS the split corner
  (non-last via `hNF`; last via `hcorner` ← `fromBlocks 1 0 0 0`, uniform-corner route).

Value-at-basepoint + eventual-unit germs (the three `hP`/`hA`/`hN` families of
`deepestEFull_sq_sum_eq_of_chain_movedC`):
- `deepestChain_wstar_toBlocks₁₁_eq_one` / `_₂₁_eq_zero` — chain layer `(1,1) = I`, `(2,1) = 0` at wstar.
- `eventually_isUnit_deepestChain_toBlocks₁₁` — `hA`, per layer (det route + tail `= 1`).
- `partProd_wstar_toBlocks₁₁_eq_one`, `partProd_toBlocks₁₁_stabilize`,
  `eventually_isUnit_partProd_toBlocks₁₁` — `hP` (value by induction; tail stabilises off the prefix).
- `nMix_tail_eq_one`, `nMix_wstar_eq_one`, `contDiffAt_nMix_entry`, `eventually_isUnit_nMix` — `hN`
  (the matrix-inverse family: `nMix = 1 + (P₁₁⁻¹·P₁₂)(Z·A₁₁⁻¹)`; entries `ContDiffAt` at the basepoint
  via `Matrix.nonsing_inv_eq_ringInverse` + `contDiffAt_matrix_inv_entry_of_det_ne_zero`).

**The deliverable:**
- **`hsub3reg_gen_germ`** — `∀ᶠ x near wstar, ∑ deepestEFull(psiSplitRawGen(split x))² =
  ∑ deepestEFull(split x)²`. Assembles the three `∀ k` unit germs (the `∀ k` collapses to a finite range
  via `Filter.eventually_all_finset` + the corner-tail stabilisation) with the banked move identity
  `psiSplitRawGen_deepestChain_hmove` and the banked pure-algebra `deepestEFull_sq_sum_eq_of_chain_movedC`.

**Fidelity anchor:** `hsub3reg_gen_germ`'s conclusion is the `deepestEFull`-form of the `hsub3reg`
hypothesis of `deepest_diffeo_bridge_gen_assembled` (`DeepestDiffeoBridgeGenConj`); the compose wraps it
via `hregval : (regStraighten q).1 = deepestEFull … q` (exactly as the L=2 arm wraps `hsub3reg_conj_germ`).

## What remains to CLOSE `hstep2` (Codex-vetted decomposition, `codex/triple-decomp-answer.md`)

Closing `hstep2` needs `deepest_diffeo_bridge_gen_assembled` applied with THREE producers; #2 is done.

1. **The diffeo triple (Producer 1, the crux) — MULTI-THREAD WALL (~>1000 L, Codex xhigh).** Supply, for
   `psiSplitRawGen`, the three inputs of the banked `DeepestPsiFlatCutGen` plumbing: (a) `psiSplitRawGen
   0 = 0` (mechanical); (b) `ContDiffAt (psiSplitRawGen − id)` on a bump support ⊆ a unit locus
   (Codex route: prove `ContDiffAt` at every `q ∈ U` open unit-locus, then pick `χ` with `tsupport χ ⊆ U`
   via `Metric.mem_nhds_iff` + `rIn = ε/4, rOut = ε/2`); (c) `HasStrictFDerivAt (psiSplitRawGen − id) 0 0`
   (degree-2 vanishing, per-layer-block `HasStrictFDerivAt … 0` then pack, mirroring the L=2 apparatus).
   The general depth-`L` `movedC`-through-inverse smoothness/derivative has **no existing infrastructure**
   and is comparable to a large fraction of the 2668-line L=2 `DeepestDiffeoBridgeL2Conj`. Codex-recommended
   FIRST scout: one per-layer `psiReadBlk − identityRead` derivative-zero theorem to confirm the boundary
   `forcedDecode` is compared to the right "identity read" (the one place (c) could be FALSE).
2. **`hsub4core` Schur→Score telescope (Producer 3) — bounded-to-medium.** `∀ᶠ,
   deepestCoreF(deepestCoreAbsorbConj(psiSplitRawGen(split x))).2.1 = Score x` via
   `prodSchurCore_eq_blockSchur_partProd` + banked boundary Schur-invisibility
   (`blockSchur_lowerFrame_left`/`_rightUpper_right`) + endpoint/`−B` normalization. Independent of #1; a
   separate thread can build it in parallel. Risk: the `Score = blockSchur(partProd …)` dictionary may not
   be in the needed general-`L` form.
3. **COMPOSE (item 6).** In `DeepestL2Wiring.lean:1060` (L ≥ 3 arm), mirror the L=2 arm (lines 627-648):
   build `hDA`/`hbdy` (`deepBlkA_isUnit_gen`/`deepBlk_boundary_gen`), the ∀-s `hPtri`/`hQtri` + `hQUpper`
   (bundle + interior), set `psi := deepestPsiFlatCut … psiSplitRawGen χ wstar`, discharge the triple via
   `DeepestPsiFlatCutGen`, wrap `hsub3reg_gen_germ` via `hregval`, supply `hsub4core`, then `exact
   deepest_diffeo_bridge_gen_assembled …`. On close: forced `#print axioms deepest_gauge_construction`
   must lose `sorryAx` (clean-three); verify `aoyagi_learning_coefficient_L2` clean-four.

**No conceptual obstruction** (hmove proven ⟹ `psiSplitRawGen` correct; reg-preservation now proven). The
remaining gap is the analytic triple (Producer 1, genuine multi-thread) + the telescope (Producer 3).

## Notes for the controller

- Build discipline: force-recompiled green (`touch` + `scripts/lb`); no sibling name clashes (`rg`-checked).
  Not wired into `DLNFibre.lean` (single-writer) — add `import DLNFibre.DLN.RLCT.Validate.DeepestChainUnitGerm`.
- ~33 `linter.style.longLine` warnings remain (verbose 12+-hypothesis signatures, inherent; non-blocking).
- Deprecations noted (`Fin.coe_cast`/`Fin.coe_castLE`, still valid at the pin) — cosmetic.
