# Statement card — Item 1: the concrete general-`L` reg-preservation `hsub3reg`, #120 `hstep2`

Thread `genm-hstep2germs5`. Delivers **Item 1** of the cert §6 build order: the concrete general-`L`
reg-preservation germ (`hsub3reg`), conditional only on the abstract move identity (the concrete
`psiSplitRawGen` design — Item 2, NOT started here). Assembles the two banked halves — the `Fin`-side
bridge `reindexECol_regBlocks_eq_of_chain_movedC` (transports the abstract Invariant A `regBlocks_movedC`
to the DLN framed products) and the direct residual expansion `deepestEFull_sq_sum_eq_blocks` — via a new
pivot-column reconciliation.

Module: `lean/DLNFibre/DLN/RLCT/Validate/DeepestHsub3regGen.lean`
(branch `genm-hstep2germs5`). `scripts/lb` import-closure green (2742 jobs, forced recompile); no name
clashes with siblings (clash-scan clean). **NOT wired into `DLNFibre.lean`** — controller wires
(single-writer aggregator).

## The headline result (sorry-free, axiom footprint `[propext, Classical.choice, Quot.sound]`)

> **`deepestEFull_sq_sum_eq_of_chain_movedC`** — the concrete general-`L` reg-preservation. For
> `J = frontEmbed` and split points `q₁ q₂ : DeepestSplit H r (deepestNGauge H r)`, IF the abstract chain
> of the framed moved point is the joint move of the framed base point,
> `deepestChain (framedParamsPivot … q₁) = movedC (deepestChain (framedParamsPivot … q₂)) (Z0edit0 (…) L)`,
> and the base chain satisfies the pivot / partial-pivot / pivot-mix `IsUnit` hypotheses (`hP`/`hA`/`hN`),
> THEN `∑ i, deepestEFull … q₁ i ^ 2 = ∑ i, deepestEFull … q₂ i ^ 2`.

- **Lean names.** `deepestEFull_sq_sum_eq_of_chain_movedC` + the reconciliation scaffold
  `deepestChainWidth_last`, `chainCol_symm_inl_eq`, `chainCol_symm_inr_eq`,
  `pivotFront_toBlocks₁₁_eq_chainCol`, `pivotFront_toBlocks₂₁_eq_chainCol`,
  `pivotFront_toBlocks₁₂_eq_chainCol`.
- **English gloss.** `deepestEFull q` is the reg-residual energy — the sum of squares of the `{11−1,12,21}`
  residual blocks of `reindex (rThr 0) (pivotThr J) (prod (framedParamsPivot … q))`. The theorem says: if
  the moved point's framed layer product is the abstract joint move `movedC` of the base point's (which
  fixes pivots, edits every up-block `Y'_s`, overrides the layer-0 down-block `Z'_0`, and reconstructs
  cores), then the reg energy is unchanged. This is `hsub3reg`, the LINK-1 germ input of
  `deepest_diffeo_bridge_gen_conj_impl`, once `psiSplitRawGen` (Item 2) supplies the move identity at
  `q₁ = psiSplitRawGen (split x)`, `q₂ = split x`.

## The two pieces

1. **Item 1(a) — the pivot-column reconciliation.** `deepestEFull_sq_sum_eq_blocks` reads the residual
   off `reindex (rThr 0) (pivotThresholdSplit … J)`; the bridge produces agreements off `deepestChainCol L`.
   At `J = frontEmbed`, `pivotThresholdSplit_frontEmbed` collapses the pivot split to the threshold split,
   and `deepestChainCol L` reconciles with `rThr (H (Fin.last L))` up to a fixed reduced-width `finCongr`
   (`deepestChainWidth_last : deepestChainWidth H L = H (Fin.last L)`). The `{11,21}` inl-column blocks
   transfer directly (`congr 1`, both symm formulas select the first `r` columns); the `{12}` inr-column
   block transfers via the reduced-width relabel (`pivotFront_toBlocks₁₂_eq_chainCol` — a `.submatrix id
   (finCongr …)`), the SAME relabel for `q₁` and `q₂`, so agreement survives.
2. **Item 1(b) — the direct residual route.** `deepestEFull_sq_sum_eq_blocks` expresses the reg energy as
   the sum of squares of the residual blocks of the FRAMED product `prod (framedParamsPivot … q)` (NOT the
   raw decode), so block agreement ⟹ sum equality directly — the `endpointP0/endpointQL` frame machinery
   (`resid_regBlocks_eq_of_mid_agree` + `deepestEFull_sq_sum_eq_of_resid_blocks`) that the L=2 germ route
   used is UNNECESSARY on this route.

## Proved / Assumed / Cited / Deferred

- **Proved.** `deepestEFull_sq_sum_eq_of_chain_movedC` + the six reconciliation lemmas, sorry-free; forced
  `#print axioms deepestEFull_sq_sum_eq_of_chain_movedC` reports `[propext, Classical.choice, Quot.sound]`
  (no `sorryAx`). Non-vacuity: the hypotheses are satisfiable near the deepest point (the `corM`-corner
  tail keeps `hP`/`hA`/`hN` satisfiable in the reduced-rank `r ≥ 1` regime — the banked
  `deepestChain_tail_toBlocks₁₁`), and `J = frontEmbed` holds throughout the `deepest_gauge_construction`
  pipeline (`hJfront'`).
- **Assumed (the precise remaining path — Item 2, the crux).** The abstract move identity `hmove`, i.e.
  the concrete `psiSplitRawGen` design + its move identity
  `deepestChain (framedParamsPivot (psiSplitRawGen q)) = movedC (deepestChain (framedParamsPivot q)) (Z0edit0 …)`.
  Codex-vetted design (this thread's `codex/psigen-design-{prompt,answer}.md`): NO hidden inconsistency in
  the `read := absolute-moved-block − deepBlk` convention (the core slot writes the RAW `movedT`, not
  `S̃_s`); the only genuine wall — the last layer's `pivotThr (pivotJSucc J)` vs `deepestChain`'s
  `rThr` coordinate mismatch — is NEUTRALISED at `J = frontEmbed`
  (`pivotThresholdSplit_pivotJSucc_frontEmbed`), which the pipeline has. Estimated ~1200–2200 Lean lines
  (all-layer `Y'_s` reads + layer-0 `Z0edit0` read + full core tuple `T'_s` + the `Fin L`/`ℕ` cast layer).
- **Cited.** None. Pure `Matrix`/`Equiv`/`Ring` algebra over `ℝ`, on the banked `Fin`-bridge
  (`reindexECol_regBlocks_eq_of_chain_movedC`, `DeepestFinBridgeGen`) + `deepestEFull_sq_sum_eq_blocks`
  (`DeepestGaugeConstruction`) + `pivotThresholdSplit_frontEmbed` (`FrontPivotProducer`).
- **Deferred (the remaining path to `hstep2`).**
  - **Item 2 (crux, NOT started):** the concrete `psiSplitRawGen` in `DeepestSplit` coords (pull the moved
    data from the abstract chain `Cq := deepestChain (framedParamsPivot q)`: `Y' s := movedY Cq s`,
    `T' s := movedT Cq (Z0edit0 Cq L) s`, `Z0edit0`; write via a `regGaugeSlotEquiv.symm` gauge edit + a
    `paramsEquivFlat` core-slot update); the **move identity** (funext s; by_cases `s < L`; match the four
    blocks; tail = corM corner); the **diffeo triple** (`psi 0 = 0`, `ContDiffAt`, `D(ψ − id)(0) = 0`,
    firing `DeepestPsiFlatCutGen`); the **split-compat germ** `split (psi x) = psiSplitRawGen (split x)`;
    and **`hsub4core`** (`deepestCoreF (deepestCoreAbsorbConj (psiSplitRawGen (split x))).2.1 = Score x`,
    via the banked `prodSchurCore_eq_blockSchur_partProd` wired to `deepestCoreAbsorbConj`).
  - **Item 3 (compose):** `deepest_diffeo_bridge_gen_assembled` (LINK-1, byte-matches the `hstep2:1060`
    RHS) with the diffeo triple + this Item-1 `hsub3reg` germ + `hsub4core` + Item-4
    (`DeepestDeepBlkBoundaryGen`) → close the `hstep2` sorry.

## Status
sorry-free. `hstep2` UNTOUCHED (not laundered). Pending controller AxCheck (wire into `DLNFibre.lean`) +
independent fidelity review (does `deepestEFull_sq_sum_eq_of_chain_movedC` faithfully capture the
`hsub3reg` reg-preservation claim?).
