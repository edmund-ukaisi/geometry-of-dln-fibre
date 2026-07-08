# Statement card — genm-hstep2germs9: #120 `hstep2` — psiSplitRawGen DEF + interior move landed

Thread `genm-hstep2germs9`. Tasked to CLOSE the `hstep2` sorry (`DeepestL2Wiring:1060`, the L ≥ 3 arm),
**item 1 (`psiSplitRawGen` DEFINITION) FIRST and non-negotiable** (deferred across germs5-8). **Outcome:
item 1 DEFINED + pushed; the item-2 read round-trips + the INTERIOR-layer move identity PROVEN
sorry-free.** No obstruction (Codex-reconfirmed design B′). `hstep2` LEFT UNTOUCHED.

Branch `genm-hstep2germs9` @ `0f68f5c5` (base `origin/expedition/aoyagi-full` @ `5fc70d2c`).

## Delivered (banked + pushed, this thread)

**Module 1 — `lean/DLNFibre/DLN/RLCT/Validate/DeepestPsiSplitRawGen.lean`** (~165 LoC), sorry-free,
axiom-clean `[propext, Classical.choice, Quot.sound]` (forced `#print axioms psiSplitRawGen`). Imports
`DeepestFramedChainDecode` (already in aggregator closure). **NOT wired into `DLNFibre.lean`** (controller
single-writer).

- `forcedDecodeLeft` / `forcedDecodeRight` — the FORCED block reads matching `DeepestFramedBoundaryMove`.
- `psiFrame0` / `psiFrameLast` — the boundary frames `Pf firstLayer` / `Qf lastLayer` in chain-width
  block form.
- `psiTargetD` — the effective target `D_s := movedC C Z0e (s) − fromBlocks 1 0 0 0` (chain-width).
- `psiGhat` — per-layer chain-width read: interior `= D_s`, first layer `= forcedDecodeLeft F0 D_s`, last
  layer `= forcedDecodeRight Ql D_s`.
- `psiReadBlk` — the H-width relabel of `psiGhat` (via `finCongr` submatrix).
- **`psiSplitRawGen`** — the concrete general-`L` joint move `DeepestSplit → DeepestSplit`, packing
  `psiReadBlk`'s four blocks (`X'/Y'/Z'` via `regGaugeSlotEquiv.symm`, `T'` via `paramsEquivFlat`),
  mirroring the L=2 lens `psiSplitRawL2Core`. **This is the item-1 deliverable deferred 4×.**

**Module 2 — `lean/DLNFibre/DLN/RLCT/Validate/DeepestPsiSplitRawGenMove.lean`** (~205 LoC), sorry-free,
axiom-clean (forced `#print axioms` on all lemmas). Imports `DeepestPsiSplitRawGen`. **NOT wired.**

- `regGaugeSlotEquiv_psiSplitRawGen` + `gaugeReadX/Y/Z_psiSplitRawGen` + `coreRead_psiSplitRawGen` — the
  **read round-trips**: `psiSplitRawGen q`'s gauge/core reads recover `psiReadBlk q s`'s `toBlocks` (both
  equivs round-trip; the packed `g'` reduces on each `RegGaugeIdx` tag).
- `gaugeReadX/Y/Z_psiSplitRawGen_eq_psiGhat` + `coreRead_psiSplitRawGen_eq_psiGhat` — the wrapped reads
  (absorbing the interior-decode reindex) equal `psiGhat`'s four `toBlocks`.
- **`psiSplitRawGen_deepestChain_interior`** — the **INTERIOR-layer move identity**: for an interior layer
  (`s ∉ {firstLayer, lastLayer}`, `Pf s = 1`, `Qf s = 1`),
  `deepestChain (framedParamsPivot (psiSplitRawGen q)) (s) = movedC (deepestChain (framedParamsPivot q))
  (Z0edit0 …) (s)`. Composes the banked interior decode with the round-trips; interior `psiGhat =
  movedC − corM`, so `fromBlocks`-reassembling + adding back the `corM`-corner recovers `movedC`.

This SORRY-FREE interior move is strong evidence the item-1 definition is **correct** (not laundered): the
def + round-trips compose exactly with the banked `deepestChain_framedParamsPivot_blocks_of_frame_one` to
reproduce `movedC` at interior layers.

## Design — Codex-reconfirmed B′ (`threads/genm-hstep2germs9/codex/`)
Codex (xhigh) re-adjudicated the `psiSplitRawGen` definition shape: verdict **B′** (boundary forced-decode
of the effective target `movedC − corM`), **OBSTRUCTION: none**. The corM-subtraction consistency (X
effectively unchanged, move touches only Y/Z/T) is derivable from the block algebra; confirmed.

## Proved / Assumed / Cited / Deferred
- **Proved (this thread).** The `psiSplitRawGen` definition (typechecks, axiom-clean); the 5 read
  round-trips; the interior-layer move identity. All sorry-free, axiom-clean.
- **Cited/used.** `deepestChain_framedParamsPivot_blocks_of_frame_one` (`DeepestFramedChainDecode`, germs8),
  `movedC`/`movedY`/`movedZ`/`movedT`/`Z0edit0` (`DeepestPsiSplitGenMoved`/`…LeftCol`), `regGaugeSlotEquiv`,
  `paramsEquivFlat`, `gaugeReadX/Y/Z`, `framedParamsPivot`.
- **Deferred (precise remaining, in order).**
  1. **`hmove` boundary layers (0/last) + `funext s` assembly.** The two boundary layers need a
     *framed-chain boundary decode* (analogue of the banked interior decode) — NOT yet built: unfold
     `framedParamsPivot` at layer 0 (`framedLayer (Pf 0) (Qf 0 = 1)` = `corM + F0·decode`), reindex into
     chain-width, apply the banked `fromBlocks_lowerFrame_mul_forcedDecode` with the frame block
     decomposition (needs `F0.toBlocks₂₂ = 1`, `F0.toBlocks₁₂ = 0` [hPtri], `P11·Pinv = 1` [frame unit],
     all satisfiable from the triangular bundle); symmetric for the last layer with
     `fromBlocks_rightUpper_mul_forcedDecode` (pivotThr→rThr via `J = frontEmbed`). Then `funext s;
     by_cases` gluing the interior lemma + the two boundary lemmas + the `s ≥ L` tail. ~300-500 L.
  2. **Diffeo triple** — `DeepestPsiFlatCutGen` (banked) fires from `psiSplitRawGen 0 = 0` (needs the
     deepest-point chain facts: at `q = 0` every read is 0, so `psiGhat 0 = 0`), `ContDiffAt` on the bump
     support (the reads go through `Ring.inverse` of the pivot/nMix — smooth near the deepest point), and
     `D(psiSplitRawGen − id)(0) = 0`. ~150-250 L.
  3. **`hsub4core` Schur→Score telescope** (unchanged from germs7/8 estimate). ~400-700 L.
  4. **COMPOSE** — `deepest_diffeo_bridge_gen_assembled` (banked) + `deepestEFull_sq_sum_eq_of_chain_movedC`
     (hsub3reg, consuming the full `hmove`) + all bundle frame hyps → close `hstep2` at
     `DeepestL2Wiring:1060`. ~150 L (mirrors the L=2 closure `DeepestL2Wiring:482-648`).

## Controller action needed
- **Wire `DeepestPsiSplitRawGen` then `DeepestPsiSplitRawGenMove` into `DLNFibre.lean`** (single-writer
  aggregator; add imports at end, in that order). Both build green in import-closure (forced-recompile),
  forced `#print axioms` clean, rg-clash clean against siblings.
- **Not added to `AxCheck.lean`** — these are lemma/def-level bricks (no `sorry`, axiom-clean); add when a
  load-bearing downstream result (the closed `hstep2`) consumes them.

## Status
`hstep2` UNTOUCHED (L ≥ 3 arm sorry intact at `DeepestL2Wiring:1060`; not laundered). The item-1 definition
deferred 4× is landed + pushed; the item-2 interior half is proven sorry-free, validating the def. Build:
`scripts/lb DLNFibre.DLN.RLCT.Validate.DeepestPsiSplitRawGenMove` green (forced-recompile, pulls in the def
module), sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`. `scripts/sorries`: unchanged
(none in the new modules). No obstruction.
