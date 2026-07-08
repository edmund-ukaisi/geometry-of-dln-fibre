# Statement card — genm-hstep2germs10 (#120 `hstep2`, items 1 + 2)

**Status:** items 1 (boundary framed-chain decode) + 2 (full move identity `hmove`) COMPLETE,
sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`. `hstep2`
(`DeepestL2Wiring:1060`) LEFT UNTOUCHED (items 3-6 remain; see below).

Branch: `genm-hstep2germs10` (pushed). Base: `origin/expedition/aoyagi-full` @ `efcaad98`.

## Files delivered

- `lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedBoundaryDecode.lean` (new, ~340 L, 0 sorry) —
  the FRAME-DEPENDENT boundary framed-chain decode + the two boundary move identities.
- `lean/DLNFibre/DLN/RLCT/Validate/DeepestHmoveGen.lean` (new, ~150 L, 0 sorry) — the full
  function-level move identity `hmove`.

Both are STANDALONE modules (build via `scripts/lb`, force-recompiled green). They are NOT yet
imported into the `DLNFibre.lean` aggregator — the controller should wire them (single-writer).

## Theorems delivered

`DeepestFramedBoundaryDecode`:
- `frame_mul_reindex` / `frame_mul_reindex_right` — pull a square frame through a reindex (left / right).
- `reindex_mul` — split `reindex (P·M)` at a chosen middle relabel (`submatrix_mul_equiv`).
- `reindexChain_fromBlocks` (castSucc–succ), `reindexChainSq_fromBlocks` (castSucc–castSucc),
  `reindexChainSq_succ_fromBlocks` (succ–succ) — the chain-width reindex of a threshold `fromBlocks`
  = chain-block `fromBlocks` (whole-matrix analog of the interior block decode).
- `framedParamsPivot_frame_firstLayer_eq` / `_lastLayer_eq` — H-width frame-keeping layer expansion
  (`corM + Pt·fromBlocks reads` / `corM + fromBlocks reads·Qt`; lastLayer collapses the pivot split to
  the threshold split via `J = frontEmbed`).
- `deepestChain_framedParamsPivot_firstLayer` / `_lastLayer` — chain-width decode
  `= corM + psiFrame0·(reads)` / `= corM + (reads)·psiFrameLast`.
- `blockLower_mul_forcedDecodeLeft` / `blockUpper_forcedDecodeRight_mul` — the `toBlocks`-form frame moves.
- `psiGhat_firstLayer` / `psiGhat_lastLayer` — the `psiGhat` boundary branches.
- **`psiSplitRawGen_deepestChain_firstLayer`** / **`_lastLayer`** — the two boundary halves of `hmove`:
  `deepestChain (framedParamsPivot (psiSplitRawGen q)) (boundary) = movedC (deepestChain
  (framedParamsPivot q)) (Z0edit0 …) (boundary)`.

`DeepestHmoveGen`:
- `deepestChain_tail_toBlocks₂₁` / `_toBlocks₂₂` — tail block-vanishing (`s ≥ L`, the block-normal corner).
- `movedC_tail` — the moved chain agrees with the original off the used prefix (`s ≥ 1`, `₂₁ = ₂₂ = 0`).
- **`psiSplitRawGen_deepestChain_hmove`** — the FULL function-level move identity
  `deepestChain (framedParamsPivot (psiSplitRawGen q)) = movedC (deepestChain (framedParamsPivot q))
  (Z0edit0 …)`, `funext s; by_cases s < L` (interior banked + boundary item 1 + tail).

**Fidelity anchor:** `psiSplitRawGen_deepestChain_hmove`'s conclusion byte-matches the `hmove`
hypothesis of the banked `deepestEFull_sq_sum_eq_of_chain_movedC` (`DeepestHsub3regGen:133-135`) with
`q₁ = psiSplitRawGen … q`, `q₂ = q` — so it feeds `hsub3reg` directly.

## Design (Codex-vetted whole-matrix route)

The interior decode (`DeepestFramedChainDecode`) is frame-trivial and decodes per-block. The boundary
frames are block-triangular with identity `₂₂` (from `deepestPoint_frame_pivot_triangular_exists`), so the
per-block route mixes blocks. The **whole-matrix** route (Codex-confirmed): frame-keeping layer expansion
→ chain-width reindex of the whole `corM + frame·reads` matrix (distribute over `+`; `reindexChain_fromBlocks`
for `corM`, `reindex_mul` + `submatrix_mul_equiv` to factor the frame) → the banked forced-decode frame move
(`fromBlocks_lowerFrame_mul_forcedDecode` / `_rightUpper_`) collapses `psiFrame0 · psiGhat = movedC − corM`,
then `corM + (movedC − corM) = movedC`.

## Remaining to CLOSE `hstep2` (items 3-6, NOT done this thread)

The compose (`deepest_diffeo_bridge_gen_assembled`, `DeepestDiffeoBridgeGenConj`) needs, beyond the bundle
data facts (all in scope in the L≥3 arm) and `psiSplitRaw := psiSplitRawGen …`:

3. **The diffeo triple** (`DeepestPsiFlatCutGen`): `psi := deepestPsiFlatCut … psiSplitRawGen χ wstar`;
   `hcontdiff`/`hderiv`/`hfix`/`hsplitPsi` from `contDiff_deepestPsiFlatCut` /
   `hasStrictFDerivAt_deepestPsiFlatCut` / `deepestPsiFlatCut_fixpoint` / `deepestPsiFlatCut_split_germ`.
   These require: `psiSplitRawGen 0 = 0` (reads at `q=0` all vanish — mechanical); `ContDiffAt ⊤
   (psiSplitRawGen − id)` on the bump support (**HARD**: `psiSplitRawGen` runs through `Ring.inverse` of
   the frame corners and `movedC`'s chain-block inverses, smooth only on units — needs bump-support ⊆
   units + ContDiffAt of matrix inverse on units); and `HasStrictFDerivAt (psiSplitRawGen − id) 0 0`
   (**HARD**: the degree-2 vanishing of the deviation's derivative). This is the genuine analytic gap
   the mission's WATCH flagged.
4. **`hsub3reg` germ**: `∀ᶠ x near wstar, ∑ deepestEFull(psiSplitRawGen(split x))² = ∑ deepestEFull(split x)²`
   via `deepestEFull_sq_sum_eq_of_chain_movedC` (now consuming the LANDED `hmove`) — but it needs the
   IsUnit germs `hP`/`hA`/`hN` (`∀ k`, partProd/layer `₁₁` and `nMix` units for the base chain
   `deepestChain (framedParamsPivot (split x))`) to hold for `x` near `wstar`. At `x = wstar` (split = 0)
   the chain is the block-normal corner (all units); needs continuity of the chain blocks in `x` +
   openness of `IsUnit` (`eventually_ne` on the determinant). ~150 L of new analytic machinery (no banked
   support found).
5. **`hsub4core` Schur→Score telescope**: `∀ᶠ, coreF(deepestCoreAbsorbConj (psiSplitRawGen (split x))).2.1
   = Score x` via `prodSchurCore_eq_blockSchur_partProd` (Inv-B, banked) + boundary Schur-invisibility
   (banked `blockSchur_lowerFrame_left` / `_rightUpper_right`) + endpoint/`−B` normalization + product
   telescope.
6. **COMPOSE**: `rw [deepest_diffeo_bridge_gen_assembled …]` at `DeepestL2Wiring:1060` (L≥3 arm). On close:
   FORCED `#print axioms deepest_gauge_construction` must lose `sorryAx` → clean-three; verify
   `aoyagi_learning_coefficient_L2` clean-four.

**No obstruction** — the design is sound (interior + both boundary halves proven ⟹ `psiSplitRawGen` is
correct). The remaining gap is analytic (item 3 ContDiff/derivative) + germ (item 4 IsUnit) + telescope
(item 5), not conceptual.
