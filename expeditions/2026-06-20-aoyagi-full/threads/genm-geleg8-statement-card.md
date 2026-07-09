# Statement card — general-`L` chart globalisation (piece iii, rung 8) → chart-data (iii) COMPLETE

> **Claim.** The general-`L` corner-elimination chart is globalised: a `ContDiff ℝ 2` map `Φ` on the
> flat parameter space, fixing `0`, with an invertible derivative at `0`, that carries the
> flat-shifted DLN loss to an explicit block-chart Frobenius readout near the flat origin. This closes
> piece (iii) of the D1 `≥`-leg chart data (the analytic heart), leaving only piece (iv) (the Schur
> residual `qₑ` + slice split of the readout) before the whole `≥`-leg.
>
> - **Lean:** `DLNFibre.DLN.RLCT.schurChart_global_gen`, `schur_loss_germ_gen_at_pivot`
>   (+ supporting `blockToChainGen` / `chainToBlockGen` / `rowEq` / `colEq` / `schurChartRawSelfGen`
>   / `schurReadoutF_gen` and the inverse-chart smoothness `contDiffAt_schurChartRawInvGen_entry`)
>   in `lean/DLNFibre/DLN/RLCT/Validate/D1GeGlobalize.lean` (new module, off canonical `fd0df6ac`).
> - **Gloss.**
>   - **Bridge (rung 8a).** `blockToChainGen` / `chainToBlockGen` : `BlockParamsGen H r` (`Fin L`, `H`
>     widths) ↔ the `ℕ`-indexed `deepestChainWidth` chain the banked algebra reads. Built as per-slot
>     `Matrix.reindex` by the composite equiv `rowEq`/`colEq` (`sumSplit (ι ·)` at the `H`-width vertex,
>     then a `finCongr` width recast, then the chain split `genChainSplit`). Two round trips
>     (`chainToBlockGen_blockToChainGen` = R1, `blockToChainGen_chainToBlockGen` = R2 on the first `L`
>     slots) and the **KEY relation** `blockToChainGen (blockFlatEquivGen x) = genChain … (flat⁻¹ x)`
>     on the first `L` slots (`blockToChainGen_blockFlatEquivGen`) — the latter by construction, letting
>     `reindex_prod_eq_genPartProd` feed the germ. Chain-level congruences
>     (`recoverProductGen_congr`, `schurChartRawInvGen_congr`, …) formalise "reads only the first `L`
>     slots".
>   - **The chart (rung 8b).** `schurChartRawSelfGen := chainToBlockGen ∘ schurChartRawGen ∘
>     blockToChainGen` (a `BlockParamsGen` self-map, the general-`L` `schurChartRaw`).
>     `schurChart_global_gen` mirrors the L = 2 `schurChart_global`: the flat chart `Φraw w = b⁻¹
>     (schurChartRawSelfGen (b w + P₀) − schurChartRawSelfGen P₀)` (`b = blockFlatEquivGen`), bump-
>     globalised to `ContDiff ℝ 2`, with invertible derivative via the finite-dimensional **left-inverse**
>     route `derivEquiv_of_left_inverse` (`Ψ∘Φ =ᶠ id` only — `Ψ` the inverse self-map, its left-inverse
>     identity `leftInverse_selfGen` from `schurChartRawInvGen_schurChartRawGen` + R1/R2 + the
>     congruences). Forward-chart entrywise `ContDiff` from the banked `contDiffAt_schurChartRawGen_entry`;
>     **inverse-chart entrywise `ContDiff`** from the NEW `contDiffAt_schurChartRawInvGen_entry` (this
>     module) — needed because `derivEquiv_of_left_inverse` requires `Ψ` differentiable at `Φ 0`.
>   - **The loss germ (rung 8c).** `schurReadoutF_gen C Br x = ∑ₐᵦ ((recoverProductGen (blockToChainGen
>     (b x + C)) last − Br)ₐᵦ)²`. `schur_loss_germ_gen_at_pivot` mirrors the L = 2
>     `schur_loss_germ_L2_at_pivot`: near `0`, `recoverProductGen` recovers the reindexed product
>     (`recoverProductGen_schurChartRawGen` + R2 + KEY + `reindex_prod_eq_genPartProd`), and Frobenius
>     reindex-invariance (`sum_sq_reindex_gen`) identifies the readout with `lossFlatShift H B v`.
> - **Proved.** Both headline theorems + all supporting lemmas, sorry-free, over `ℝ`. Forced
>   `#print axioms` on both headlines = `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no
>   `cited_aoyagi_dln`.
> - **Assumed (hypotheses).**
>   - `schurChart_global_gen`: a base block-param `P₀`, `hL : 1 ≤ L`, and every prefix pivot
>     `(partProd (blockToChainGen P₀) k).toBlocks₁₁` (`k ≤ L`) nonsingular.
>   - `schur_loss_germ_gen_at_pivot`: an optimal-`v` common pivot `ι` (per-vertex injections) with
>     every prefix pivot `(partProd (genChain … v) k).toBlocks₁₁` (`k ≤ L`) nonsingular — exactly what
>     the banked `prefixPivotDomGen` (piece i + ii) delivers at an optimal `v`.
> - **Cited.** none. Reuses the banked chain algebra (`schurChartRawGen`, `schurChartRawInvGen`,
>   `recoverProductGen`, `recoverProductGen_schurChartRawGen`, `schurChartRawInvGen_schurChartRawGen`,
>   `reindex_prod_eq_genPartProd`, `genChain`), the block model (`blockFlatEquivGen`), the rung-7 ContDiff
>   lemmas + `derivEquiv_of_left_inverse` (`D1GeChartGlobal`), and the bump-globalisation
>   `exists_contDiff_eventuallyEq_of_contDiffOn`.
> - **Shape note (`L` vs `last`).** `schur_loss_germ_gen_at_pivot` and `schurReadoutF_gen` are stated
>   over `H : Fin (last + 1 + 1) → ℕ` (i.e. `L = last + 1` baked in) because `recoverProductGen (·) last`
>   / `schurChartRawInvGen (·) last` carry the last-slot index. `schurChart_global_gen` is stated over
>   general `L` with `hL : 1 ≤ L` (destructures internally). The general-`L` `≥`-leg wiring destructures
>   `hL : 1 ≤ L` to obtain `last` when consuming the germ.
> - **The isolated addition beyond the prior recipe.** The prior tide's recipe listed the forward chart
>   ContDiff as banked but did **not** flag the INVERSE chart's smoothness. It is required
>   (`derivEquiv_of_left_inverse` needs `Ψ` differentiable at `Φ 0`) and is built here as
>   `contDiffAt_schurChartRawInvGen_entry` (+ `contDiffAt_invLayerSucc_entry`,
>   `contDiffAt_gen_partProd_entry`) — mechanical, mirroring the forward lemmas.
> - **Not wired.** The aggregator `DLNFibre.lean` and `AxCheck.lean` are NOT edited (single-writer;
>   the controller wires this module). The next and only remaining piece for the whole `≥`-leg is piece
>   (iv): split `schurReadoutF_gen` into the consumer's `∑ p² + ∑ qₑ²` form + slice value, feeding
>   `d1ge_hAtV_of_explicit_chart_genL`.
> - **Status.** sorry-free, axiom-clean three; green (`scripts/lb DLNFibre.DLN.RLCT.Validate.D1GeGlobalize`,
>   force-recompiled); pending reviewer fidelity check + controller integration.
