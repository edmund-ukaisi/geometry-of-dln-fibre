# Statement card — genm-hstep2germs8: #120 `hstep2` — interior framed-chain block decode banked

Thread `genm-hstep2germs8`. Tasked to CLOSE the `hstep2` sorry (`DeepestL2Wiring:1060`, the L ≥ 3 arm)
via the germs7 5-item plan (`psiSplitRawGen` def + `hmove` + diffeo triple + Schur→Score telescope +
compose). **Outcome: HONEST-PARTIAL. The genuinely-missing item-2 sub-piece — the INTERIOR
(frame-trivial) framed-chain per-layer block decode — is banked, sorry-free + axiom-clean. `hstep2`
LEFT UNTOUCHED.** No obstruction found; the remaining work is the concrete `psiSplitRawGen` + full
`hmove` + the Schur→Score telescope + compose, unchanged in size from germs7's estimate.

## Delivered (banked this thread)

**New module `lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedChainDecode.lean`** (~145 LoC), sorry-free,
axiom-clean `[propext, Classical.choice, Quot.sound]` (forced `#print axioms`), no name clashes with
siblings. Imports `DeepestFinBridgeGen` + `DeepestFramedProductPivot` (both already in the aggregator's
closure). **NOT yet wired into `DLNFibre.lean`** (controller's single-writer job — see below).

Six theorems:

- `chainWidth_castSucc_sub` / `chainWidth_succ_sub` — the interior reduced-width bridges
  (`H s.castSucc − r = deepestChainWidth H s − r`, and the `.succ` version). The `finCongr` relabels the
  decode blocks use.
- `framedParamsPivot_frame_one_eq` — **the frame-trivial layer collapse.** For a layer `s` with trivial
  frames (`Pf s = 1`, `Qf s = 1`) that is not the pivot-carrying last layer (`s ≠ lastLayer`),
  `framedParamsPivot … q s = reindex (rThr.symm) (rThr.symm) (fromBlocks (1 + gaugeReadX) gaugeReadY
  gaugeReadZ coreRead)`. The `framedLayer 1 1 = corM + reindex(fromBlocks X Y Z T)` degeneration, with
  `corM = reindex(fromBlocks 1 0 0 0)` folded into the pivot (`fromBlocks_add`).
- `rThr_finCongr_split_inl` / `rThr_finCongr_split_inr` — the index-image facts: the threshold split
  `rThresholdSplit` absorbs the `deepestChainSplit`/`finCongr` prefix, sending `inl i ↦ inl i` and
  `inr j ↦ inr (reduced-width relabel of j)`. Network-free `Fin`/`Equiv` algebra.
- **`deepestChain_framedParamsPivot_blocks_of_frame_one`** — the headline of this thread. For an interior
  layer (`s ≠ lastLayer hL`, `Pf s = 1`, `Qf s = 1`), the four residual blocks of the abstract chain layer
  `deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) (s : ℕ)` decode into the gauge/core reads:
  `toBlocks₁₁ = 1 + gaugeReadX`, `toBlocks₁₂ = gaugeReadY`, `toBlocks₂₁ = gaugeReadZ`,
  `toBlocks₂₂ = (paramsEquivFlat (deepestM)).symm q.2.1 s` — each on the reduced-width relabel.

This is exactly the germs7 item-2 note "no framed-chain block decode exists yet (only the frame-FREE
`reindex_decode_blocks_split`)": it is the **interior collapse of `hmove`'s `funext s; by_cases s < L`**.
For the boundary layers (0 / last) the frame is `q`-DEPENDENT and the banked `DeepestFramedBoundaryMove`
forced-decode identities apply instead (not built here).

## Proved / Assumed / Cited / Deferred

- **Proved (this thread).** The six `DeepestFramedChainDecode` theorems (sorry-free, axiom-clean). The
  interior half of the per-layer framed-chain decode.
- **Cited/used.** `framedParamsPivot`/`framedParams`/`framedLayer` (`DeepestFramedProduct(Pivot)`),
  `deepestChain`/`deepestChainLayer`/`deepestChainWidth_castSucc`/`_succ` (`DeepestFinBridgeGen`),
  `gaugeReadX/Y/Z` (`DeepestSchurShift`), `rThresholdSplit_symm_inl`/`_inr` (`DeepestFrameRaw`).
- **Deferred (the precise remaining build, in order; unchanged from germs7 estimate).**
  1. **`psiSplitRawGen` — the concrete def** (`DeepestSplit → DeepestSplit`, frame-dependent). Interior
     gauge Y-tags → `movedY`, layer-0 Z-tag → `Z0edit0`, core-slot → `movedT` (via
     `regGaugeSlotEquiv.symm` + `Function.update` + `paramsEquivFlat`, mirroring the L=2 lens
     `psiSplitRawL2Core`/`l2g'`/`l2T1p`); the boundary layers (0/last) pack the FORCED reads of
     `DeepestFramedBoundaryMove`. ~300-500 L.
  2. **`hmove` — the framed-chain move identity** `deepestChain (framedParamsPivot (psiSplitRawGen q)) =
     movedC (deepestChain (framedParamsPivot q)) (Z0edit0 …)`. `funext s; by_cases s < L`: the INTERIOR
     collapse is now **this thread's `deepestChain_framedParamsPivot_blocks_of_frame_one`** (applied to
     both `psiSplitRawGen q` and `q`, matching the moved blocks against `movedC`'s
     `((Cq_s)₁₁, movedY, movedZ, movedT)`); the boundary applies
     `fromBlocks_lowerFrame_mul_forcedDecode`/`_rightUpper_`. Then `hsub3reg` is the banked
     `deepestEFull_sq_sum_eq_of_chain_movedC` (needs the base-chain pivot/partial-pivot/pivot-mix `IsUnit`
     hyps `∀ᶠ x near wstar` — an openness argument on the unit locus). ~300-600 L now that the interior
     decode is banked.
  3. **Diffeo triple** — `DeepestPsiFlatCutGen` (`contDiff_deepestPsiFlatCut`, `hasStrictFDerivAt_…`,
     `deepestPsiFlatCut_fixpoint`, `deepestPsiFlatCut_split_germ`) BANKED; fires from `psiSplitRawGen 0 = 0`,
     `ContDiffAt` on the bump support, `D(psiSplitRawGen − id)(0) = 0`. ~150 L.
  4. **`hsub4core` — the Schur→Score telescope** (the hard piece; boundary Schur-invisibility banked in
     `DeepestFramedBoundaryMove`). The general-`L` `∏_s blockSchur(decode)_s → Score` via
     `prodSchurCore_eq_blockSchur_partProd` (banked) + `blockSchur_lowerFrame_left`/`_rightUpper_right` +
     the endpoint/`−B` normalization. ~400-700 L.
  5. **COMPOSE** — `deepest_diffeo_bridge_gen_assembled` (BANKED, `DeepestDiffeoBridgeGenConj`, byte-matches
     the `hstep2:1060` RHS after `hca_def`) supplying `psi`, `psiSplitRawGen`, the triple, `hsub3reg`,
     `hsub4core`, + the bundle frame hyps (`hDA`/`hbdy` must also be established). Closes `hstep2`. ~100 L.

## Controller action needed
- **Wire `DeepestFramedChainDecode` into `DLNFibre.lean`** (single-writer aggregator; add import at end).
  Isolated build green + forced `#print axioms` clean + rg-clash clean; not aggregator-built here.
- **Not added to `AxCheck.lean`** — the six theorems are lemma-level bricks (no `sorry`, axiom-clean); add
  to AxCheck only when a load-bearing downstream result consumes them.

## Status
`hstep2` UNTOUCHED (not laundered; the L ≥ 3 arm sorry is intact at `DeepestL2Wiring:1060`). The interior
framed-chain block decode germs7 flagged as missing is now banked in verified Lean. Build:
`scripts/lb DLNFibre.DLN.RLCT.Validate.DeepestFramedChainDecode` green (forced-recompile), sorry-free,
axiom-clean. `scripts/sorries`: unchanged (none in the new module). Branch `genm-hstep2germs8` @ 8d7235bf.
No obstruction.
