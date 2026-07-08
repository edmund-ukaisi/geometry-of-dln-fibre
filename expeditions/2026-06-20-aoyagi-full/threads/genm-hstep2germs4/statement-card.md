# Statement card — the `Fin`-side product bridge (Item 1 core), #120 `hstep2`

Thread `genm-hstep2germs4`. Delivers the **Item 1 core** of the cert §6 build order: the general-`L`
cast bridge from the DLN framed layer product `prod H A` (a `Fin`-width `prodAux` fold, cast-laden through
the per-layer `finCongr` succ-steps) to the **network-free abstract chain** `partProd (deepestChain …)` of
the banked `DeepestPsiSplitGenMoved` / `DeepestSchurRecursion` framework. Once the DLN product reindexes to
the abstract `partProd`, the banked `regBlocks_movedC` (Invariant A, both halves) transfers to the DLN
framed product — the algebraic heart of the concrete `hsub3reg`.

Module: `lean/DLNFibre/DLN/RLCT/Validate/DeepestFinBridgeGen.lean`
(branch `genm-hstep2germs4` @ `f8fb80f6`). `scripts/lb` import-closure green (2684 jobs, forced recompile);
no name clashes with siblings (clash-scan clean). **NOT wired into `DLNFibre.lean`** — controller wires
(single-writer aggregator).

## The headline results (all sorry-free, axiom footprint `[propext, Classical.choice, Quot.sound]`)

> **`reindex_prodAux_eq_partProd`** — the core fold bridge. For any `A : Params H`, `r`, `hr`, and every
> prefix length `k < L + 1`:
> `reindex (rThresholdSplit r (H 0) (hr 0)) (deepestChainCol H r hr k hk) (prodAux H A k hk)
>   = partProd (deepestChain H r hr A) k`.
> Induction on `k`: base `reindex e e 1 = 1` (`submatrix_one_equiv`); succ peels the last layer
> (`prodAux_succ` + `reindex_mul_split_gen`) and matches the layer via the `finCongr`-composition collapse
> (`submatrix_submatrix` + `congr`). This isolates the opaque-width cast grind **once**.

- **Lean:** `DLNFibre.DLN.RLCT.reindex_prodAux_eq_partProd`, `reindex_prod_eq_partProd`,
  `reindexECol_regBlocks_eq_of_chain_movedC`, `reindex_mul_split_gen` +
  scaffold defs `deepestChainWidth`, `deepestChain`, `deepestChainSplit`, `deepestChainCol`,
  `deepestChainLayer` (+ width lemmas `deepestChainWidth_castSucc/_succ`, `H_eq_deepestChainWidth`,
  `r_le_deepestChainWidth`) + the tail witness `deepestChain_tail_toBlocks₁₁`.
- **Gloss.**
  - `deepestChain H r hr A s` = the `s`-th DLN layer reindexed into `r ⊕ (deepestChainWidth · − r)` block
    shape (an `ℕ`-indexed, cast-free chain over the min-clamped width `deepestChainWidth H s := H ⟨min s L, ·⟩`).
    Beyond the last layer (`s ≥ L`) the default is the **block-normal corner** `diag(I_r, 0)` (`corM`-shape),
    NOT `0`: its threshold-`(1,1)` block is `I_r` (`deepestChain_tail_toBlocks₁₁`) and its `(2,1)` block is
    `0`, so off the used prefix the partial-product `(1,1)` pivots and the pivot-mix `nMix` stay units. The
    tail is never read by `partProd … L` (fold bridge unaffected); it exists to keep the `regBlocks_movedC`
    `∀ k`-unit hypotheses satisfiable in the reduced-rank `r ≥ 1` regime. (The deepest-point interior is
    itself this corner — `deepestPoint_interior_eq_corM`.)
  - `reindex_mul_split_gen` : the `DeepestBlockDecomp.reindex_mul_split` shared-middle cancel, freed of the
    `Fin r ⊕ Fin (· − r)` middle shape (needs only `[Fintype μ]`), so the abstract chain's
    `Fin r ⊕ Fin (deepestChainWidth · − r)` middle applies.
  - `reindex_prod_eq_partProd` : the `k = L` specialization on the full product `prod H A`.
  - `reindexECol_regBlocks_eq_of_chain_movedC` : **conditional transport** — given the abstract move
    identity `deepestChain … Aψ = movedC (deepestChain … Aq) (Z0edit0 (deepestChain … Aq) L)` and the
    pivot/partial-pivot/pivot-mix `IsUnit` hypotheses on the base chain, the three reg-residual blocks
    (`{11,12,21}`) of `reindex (rThr 0) (deepestChainCol L) (prod H A·)` agree between `Aψ` and `Aq`.
    Combines the bridge with the banked `regBlocks_movedC`.
- **Proved.** All theorems + the scaffold, sorry-free; forced `#print axioms` on the four named results
  reports `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
- **Assumed.** In the conditional transport: the `∀ k` `IsUnit` hypotheses on the base chain's layer /
  partial-pivot `(1,1)` blocks and `nMix` — **satisfiable** near the deepest point (the interior/tail are the
  corner `diag(I_r,0)`, so `(1,1) = I_r`, `(2,1) = 0 ⟹ nMix = 1`, and the prefix pivots are units in a
  neighbourhood where the framed product is the corner) — and the abstract move identity (the concrete
  `psiSplitRawGen` design, Item 2). (A prior draft's `else 0` tail made these `∀ k` hypotheses
  *unsatisfiable* for `r ≥ 1`; the `corM`-corner tail — reviewer-flagged fix — restores satisfiability.)
- **Cited.** None. Pure `Matrix`/`Ring`/`Equiv` algebra over `ℝ`; builds on the banked `partProd`/`movedC`/
  `regBlocks_movedC` (`DeepestPsiSplitGen*`) and `prodAux_succ` (`Foundations.Loss`).
- **Deferred (the precise remaining path to `hsub3reg`, then `hstep2`).**
  1. **Pivot-column reconciliation** (bounded cast): transfer the block-agreements from the
     `deepestChainCol L` reindex to the `pivotThresholdSplit r (H (Fin.last L)) J` reindex the consumer
     `deepestEFull` reads. At `J = frontEmbed`, `pivotThresholdSplit_frontEmbed` gives
     `pivotThr J = rThr (H last)`; the gap is the `deepestChainWidth H L = H (Fin.last L)` (`min L L = L`)
     `finCongr` relabel on the `toBlocks₁₂` (inr) column (the `{11,21}` inl-column blocks transfer directly).
  2. **Wire the two already-general-`L` finishers** (both in `DeepestDiffeoBridgeL2`, no `L=2` hypothesis):
     `resid_regBlocks_eq_of_mid_agree` (lifts bare-`prod` `{11,12,21}`-agreements at `pivotThr J` to the
     endpoint-framed `endpointP0·(prod−B)·endpointQL` block-agreements) then
     `deepestEFull_sq_sum_eq_of_resid_blocks` (⟹ `∑ deepestEFull(q₁)² = ∑ deepestEFull(q₂)²`). This yields a
     per-`x` conditional `hsub3reg`, conditional only on the move identity of item 3.
  3. **The abstract move identity** `deepestChain (framedParamsPivot (psiSplitRawGen q)) =
     movedC (deepestChain (framedParamsPivot q)) (Z0edit0 …)` — the concrete `psiSplitRawGen` design
     (cert Item 2). NOT started; the crux design decision (a wrong definition walls it).
  4. **`hsub4core`** (`Score` untwist) via `prodSchurCore_eq_blockSchur_partProd` + `deepestCoreAbsorbConj`,
     transported through the same bridge (`blockSchur (partProd (deepestChain …) L)`).
  5. **`psiSplitRawGen` diffeo triple** (feed the banked `DeepestPsiFlatCutGen`) + **compose** via
     `deepest_diffeo_bridge_gen_assembled` (`hDA`/`hbdy` discharged by the banked `DeepestDeepBlkBoundaryGen`;
     frames from the L≥3-arm bundle) → close `DeepestL2Wiring:1060`.
- **Status.** sorry-free. `hstep2` UNTOUCHED (not laundered). Independent fidelity review (decorrelated
  Codex): the two unconditional bridges SURVIVED; it flagged a vacuity defect in the conditional transport
  (the `else 0` tail made the `∀ k`-unit hypotheses unsatisfiable for `r ≥ 1`) + a matching card overclaim —
  **both addressed** here (the `corM`-corner tail + `deepestChain_tail_toBlocks₁₁`; the "Assumed" bullet
  corrected). Pending controller AxCheck (wire into `DLNFibre.lean`).
