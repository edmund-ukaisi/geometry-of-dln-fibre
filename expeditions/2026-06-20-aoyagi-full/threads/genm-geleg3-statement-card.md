# Statement card — asymmetric general-`L` Schur telescope (piece iii, rungs 1–3)

> **Claim.** The `(1,1)`-Schur complement of the `L`-layer block product is the ordered product of the
> per-layer reduced factors, reached from the partial-product (prefix) pivots ALONE — no per-layer
> pivot (`hLayer`). This is the reduced-core factorisation the general-`L` corner-elimination chart
> reads, and it establishes that the chart avoids `hLayer`/Cauchy–Binet (only piece-(i) prefix pivots
> are needed).
>
> - **Lean:** `DLNFibre.DLN.RLCT.prefixPivotDomGen`, `blockSchur_mul_asym`,
>   `blockSchur_partProd_succ_asym`, `blockSchur_partProd_asym_fold` (+ defs `redFactorGen`, `redProd`)
>   (`lean/DLNFibre/DLN/RLCT/Validate/D1GeSchurTelescope.lean` @ `9558c5ae`)
> - **Gloss.**
>   - `prefixPivotDomGen` (rung 1): at an optimal `v` (`prod H v = B`, `B.rank = r`), the common pivot
>     `ι` of `exists_common_pivot_gen` (piece i) makes every partial-product block pivot invertible:
>     `((partProd (genChain …) k).toBlocks₁₁).det ≠ 0` for all `k ≤ L`. Composes piece (i)'s prefix
>     minor `det ≠ 0` with piece (ii)'s `genPartProd_toBlocks₁₁`.
>   - `blockSchur_mul_asym` (rung 2): for `Fin`-core-blocked `G0`, `G1` with `G0₁₁` and `(G0·G1)₁₁`
>     invertible (the left + product pivots, NOT `G1`'s own), `blockSchur (G0·G1) = blockSchur G0 ·
>     (G1₂₂ − G1₂₁·(G0·G1)₁₁⁻¹·(G0·G1)₁₂)`. `toBlocks`-native recast of `Core.schur_product_factor`.
>   - `redFactorGen`, `blockSchur_partProd_succ_asym` (rung 2): `R_k` and the single-step peel
>     `blockSchur (partProd C (k+1)) = blockSchur (partProd C k) · R_k` from the two prefix pivots.
>   - `redProd`, `blockSchur_partProd_asym_fold` (rung 3): `blockSchur (partProd C L) = redProd C L
>     = R_0·R_1·…·R_{L−1}`, given `∀ k ≤ L, Invertible (partProd C k).toBlocks₁₁`.
> - **Proved.** All four theorems, unconditionally, sorry-free, over `ℝ`. Forced `#print axioms` (all)
>   = `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.
> - **Assumed.** rung 1: `prod H v = B`, `B.rank = r`, `hr`. rungs 2–3: the prefix-pivot
>   invertibility (`Invertible (partProd C k).toBlocks₁₁`), supplied by rung 1. NO per-layer pivot.
> - **Cited.** none. Reuses banked `Core.schur_product_factor` (the asymmetric brick, reviewed),
>   `partProd`/`blockSchur` (`DeepestSchurRecursion`), and pieces (i)/(ii).
> - **Deferred.** The chart itself (rungs 4–8): `schurChartRawGen` (same-type packed chart map) +
>   readbacks, `recoverProductGen`, `schurChartRawInvGen` (rational two-sided inverse), the `ContDiff`
>   lemmas, and `schurChart_global_gen` + `schur_loss_germ_gen` (the `∃ Φ, ContDiff² ∧ HasFDerivAt ∧
>   fixes 0 ∧ germ` producer). These are the ~1000-line analytic bulk of piece (iii), NOT done here.
> - **Structure & ideas observed.** The asymmetric route (Codex-decomposed): iterate
>   `schur_product_factor` on `(prefix P_s)·(layer v_s)`, where each step needs only the two prefix
>   pivots. The telescope has NO interspersed unipotent corrections (contrast the symmetric `coreProd`
>   of `schur_product_ldu_rec`) — a cleaner fold, at the cost of the reduced factors `R_k` being
>   product-pivot-relative rather than layer-relative.
> - **Route.** Asymmetric telescope, prefix-pivots-only (Codex xhigh,
>   `threads/genm-geleg1/codex/piece-iii-decomp-{prompt,answer}.md`).
> - **Status.** sorry-free (rungs 1–3 of piece iii; pending reviewer + rungs 4–8).
