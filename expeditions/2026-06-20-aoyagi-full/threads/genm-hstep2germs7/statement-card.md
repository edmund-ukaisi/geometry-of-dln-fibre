# Statement card — genm-hstep2germs7: #120 `hstep2` — boundary-frame move-identity CORE banked

Thread `genm-hstep2germs7`. Tasked to CLOSE the `hstep2` sorry (`DeepestL2Wiring:1060`, the L≥3 arm) with
the germs6 CORRECTED (frame-dependent boundary) recipe, in 5 items. **Outcome: HONEST-PARTIAL. The
abstract *core* of the correction (item 2's block algebra) is banked, sorry-free + axiom-clean. `hstep2`
LEFT UNTOUCHED.** No obstruction found; the remaining work is the DLN-glue wiring + the two coupled
geometric germs, unchanged in size from germs6's estimate.

## Delivered (banked, this thread)

**New module `lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedBoundaryMove.lean`** (~205 LoC), sorry-free,
axiom-clean `[propext, Classical.choice, Quot.sound]` (forced `#print axioms` on all four theorems), no
name clashes with siblings. Imports `DeepestPsiSplitGenMoved` + `DeepestBlockDecomp` (both already in the
aggregator's closure). **NOT yet wired into `DLNFibre.lean`** (controller's single-writer job — see below).

Four theorems — the verified abstract core of the germs6 design CORRECTION:

- `fromBlocks_lowerFrame_mul_forcedDecode` — the **layer-0 boundary move identity** (block-lower left
  frame, `₂₂=1`). Given `hP : P11 * Pinv = 1`, the FORCED reads
  `decode = fromBlocks (Pinv·A) (Pinv·Y) (Z − P21·(Pinv·A)) (T − P21·(Pinv·Y))` satisfy
  `(fromBlocks P11 0 P21 1) · decode = fromBlocks A Y Z T`. Pure `fromBlocks_multiply` + the `P11·Pinv=1`
  cancel. Over a general `CommRing`. This is the block content of the move identity at layer 0.
- `fromBlocks_rightUpper_mul_forcedDecode` — the **last-layer boundary move identity** (block-upper right
  frame, `₂₂=1`). Given `hQ : Qinv * Q11 = 1`, the FORCED reads
  `decode = fromBlocks (A·Qinv) (Y − A·Qinv·Q12) (Z·Qinv) (T − Z·Qinv·Q12)` satisfy
  `decode · (fromBlocks Q11 Q12 0 1) = fromBlocks A Y Z T`. The symmetric mirror. Over a general `CommRing`.
- `blockSchur_lowerFrame_left` — **Schur-invisibility** of a block-lower left `₂₂=1` frame:
  `blockSchur ((fromBlocks P11 0 P21 1) · M) = blockSchur M` (`[Invertible P11] [Invertible A]` +
  framed-pivot `Invertible`). Specialization of the banked two-sided `schur_frame_transform` to
  `DP = DQ = 1`, bridged `Ring.inverse ↔ (·)⁻¹`. Over `ℝ`.
- `blockSchur_rightUpper_right` — the mirror for a block-upper right frame. Over `ℝ`.

These are exactly the "key lemmas" the germs6 Codex re-adjudication named
(`blockSchur_leftLower_22_one_cancel`, `blockSchur_rightUpper_22_one_cancel`, and the forced-reads block
identities). They discharge, in verified Lean, the two facts the correction rests on: (i) the corrected
frame-dependent boundary reads reconstruct `movedC` blockwise; (ii) the one-sided `₂₂=1` boundary frames
are Schur-invisible (so `hsub4core`'s `Score` product is unaffected by the boundary frames).

Instantiation for `movedC` (the connection to `DeepestPsiSplitGenMoved`): take
`A = (deepestChain … q)_s.toBlocks₁₁`, `Y = movedY (deepestChain … q) s`, `Z = movedZ … (Z0edit0 …) s`,
`T = movedT … s`. Then `fromBlocks A Y Z T = movedC (deepestChain … q) (Z0edit0 …) s` by the `movedC`
definition, and `fromBlocks_lowerFrame_mul_forcedDecode` says the framed FORCED-decode layer equals it.

## Proved / Assumed / Cited / Deferred

- **Proved (this thread).** The four `DeepestFramedBoundaryMove` theorems above (sorry-free, axiom-clean).
  Together they verify the germs6 correction's block algebra: the corrected boundary reads (a) give the
  literal framed `movedC`, and (b) are Schur-invisible.
- **Cited.** `schur_frame_transform` (`DeepestBlockDecomp:244`), `blockSchur`/`movedC`/`movedY`/`movedT`
  (`DeepestPsiSplitGenMoved`). Codex frame2 re-adjudication (`genm-hstep2germs6/codex/`), verdict
  REACHABLE-AS-BANKED.
- **Deferred (the precise remaining build, in order; unchanged from germs6 estimate).**
  1. **`psiSplitRawGen` — the concrete def** (`DeepestSplit → DeepestSplit`, frame-dependent). Interior
     reads frame-blind (`Y'_s = movedY`, etc.); boundary reads via the FORCED formulas now VERIFIED above.
     Write via `regGaugeSlotEquiv.symm` (pack the target X'/Y'/Z' blocks per layer into the (reg,gauge)
     slot) + `paramsEquivFlat (deepestM)` (pack the target T' into the core slot). The target blocks are
     functions of `q` through `deepestChain (framedParamsPivot … q)` + the frames `Pf/Qf` +
     `deepBlkA_0`/`deepBlkZ_last`. ~300-500 L. Needs: the exact `RegGaugeIdx` un-flatten inverse.
  2. **The framed-chain per-layer block decode + the move identity** `hmove` (item-2 DLN glue). NEW: no
     framed-chain block decode exists yet (only the frame-FREE `reindex_decode_blocks_split`,
     `DeepestLDUReadback:342`). Build the per-layer readback of `deepestChain (framedParamsPivot … q) s`
     as `reindex(Pf_s) · decode · reindex(Qf_s)`; `funext s; by_cases s < L` — interior (`Pf=Qf=1`,
     `DeepestPivotFrameTriangular:244-248`) collapses to `decode = movedC`; boundary applies the banked
     `fromBlocks_lowerFrame_mul_forcedDecode` / `_rightUpper_`. The `IsUnit` pivot hyps hold at the
     deepest point. ~400-700 L (the block-algebra core is now banked; remaining = DLN cast/reindex grind).
  3. **Diffeo triple** — `DeepestPsiFlatCutGen` is ALREADY BANKED (`contDiff_deepestPsiFlatCut`,
     `hasStrictFDerivAt_deepestPsiFlatCut`, `deepestPsiFlatCut_fixpoint`, `deepestPsiFlatCut_split_germ`).
     It fires from any `psiSplitRaw` with `hraw0 : psiSplitRaw 0 = 0`, `hcd` (ContDiffAt on the bump
     support), `hderiv0 : D(psiSplitRaw − id)(0) = 0`. So item 3 = prove those THREE analytic properties of
     `psiSplitRawGen` (item 1). ~150 L.
  4. **`hsub4core`** — the general-`L` Schur→Score readback (the hard remaining piece; numerically
     certified, `DeepestDiffeoBridgeGenConj.lean:33`, not yet in Lean). The boundary Schur-invisibility
     half is now banked (`blockSchur_lowerFrame_left`/`_rightUpper_right`); the remaining content is the
     product-telescope `∏_s blockSchur(decode)_s → Score` via `prodSchurCore_eq_blockSchur_partProd`
     (banked, `DeepestPsiSplitGenMoved`) + the endpoint-frame telescope + the `−B` corner normalization.
     ~400-700 L.
  5. **COMPOSE** — `rw [deepest_diffeo_bridge_gen_assembled …]` (ALREADY BANKED, `DeepestDiffeoBridgeGenConj`)
     supplying `psi = deepestPsiFlatCut … psiSplitRawGen …`, `psiSplitRaw = psiSplitRawGen`, the triple
     (item 3), `hsub3reg` (= `deepestEFull_sq_sum_eq_of_chain_movedC` consuming item 2's `hmove`),
     `hsub4core` (item 4), + the bundle frame hyps (`deepestPoint_frame_pivot_triangular_exists`). Closes
     `hstep2` at `DeepestL2Wiring:1060`. ~100 L.

## Controller action needed
- **Wire `DeepestFramedBoundaryMove` into `DLNFibre.lean`** (single-writer aggregator; add import at end).
  Isolated build green + forced `#print axioms` clean + rg-clash clean; not aggregator-built here.
- **Not added to `AxCheck.lean`** — the four theorems are lemma-level bricks (no `sorry`, axiom-clean); add
  to AxCheck only when a load-bearing downstream result consumes them.

## Status
`hstep2` UNTOUCHED (not laundered; the L≥3 arm sorry is intact at `DeepestL2Wiring:1060`). The abstract
CORE of the germs6 correction is banked in verified Lean (was previously only prose + Codex). Build:
`scripts/lb DLNFibre.DLN.RLCT.Validate.DeepestFramedBoundaryMove` green (forced-recompile), sorry-free,
axiom-clean. `scripts/sorries`: 20 sorry (unchanged — none in the new module). The five deferred items
(esp. items 1, 2, 4 — the DLN glue + Schur→Score) remain for the next tide, now with the block-algebra
heart de-risked. No obstruction.
