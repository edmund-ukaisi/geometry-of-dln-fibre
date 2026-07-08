# Statement card — genm-hstep2germs6: #120 `hstep2` DESIGN CORRECTION (recipe wrong; corrected recipe reachable)

Thread `genm-hstep2germs6`. Tasked to CLOSE the `hstep2` sorry (`DeepestL2Wiring:1060`, the L≥3 arm)
by building the concrete `psiSplitRawGen` + the move identity + the diffeo triple + compose, on the
banked germs5 lemma `deepestEFull_sq_sum_eq_of_chain_movedC`.

**OUTCOME: `hstep2` NOT closed. A material design flaw in the prescribed recipe was found (and
corrected). No Lean files changed — build unchanged at `0bbc750c`; `hstep2` left UNTOUCHED (not
laundered).** The deliverable is the corrected design + reachability re-adjudication.

## The finding (the flaw the germs5/cert/design-review missed)

The prescribed `psiSplitRawGen` writes FRAME-BLIND reads — cert convention `read := movedData − deepBlk`
(mission step 1: `Y' s := movedY Cq s`, core slot `T' s := movedT Cq …`, written verbatim). This does
**NOT** satisfy the banked lemma's hypothesis
`hmove : deepestChain (framedParamsPivot (psiSplitRawGen q)) = movedC (deepestChain (framedParamsPivot q)) (Z0edit0 …)`
at the two **boundary** layers, because `framedParamsPivot` conjugates each layer by the endpoint gauge
frames `Pf_s · (·) · Qf_s` (`framedLayer`, `DeepestFramedProduct.lean:142`).

- **Interior layers are fine.** The triangular bundle `deepestPoint_frame_pivot_triangular_exists`
  (`DeepestPivotFrameTriangular.lean:244-248`) GUARANTEES `Pf_s = Qf_s = 1` for all strict-interior
  `s` (`0 < s`, `s+1 < L`). So the framed chain equals the frame-free decode chain there; frame-blind
  reads match `movedC` verbatim.
- **The two boundary layers carry one-sided frames**, and there the frame-blind reads FAIL. Layer 0:
  `Pf_0` block-LOWER with ₂₂ = 1, `Qf_0 = 1`, so the framed chain block is
  `Cq'_0 = fromBlocks (1+P11·X') (P11·Y') (P21·X'+Z') (P21·Y'+T')` (reindex(Pf_0) = fromBlocks P11 0 P21 1).
  Frame-blind `Y'_0 = movedY(Cq_0)` gives `Cq'_0.₁₂ = P11·movedY ≠ movedY = (movedC Cq_0)₁₂` (off by the
  frame factor `P11`, which equals `deepBlkA_0⁻¹`). The last layer is the symmetric block-UPPER `Qf`.

The prior Codex design review (germs5 `codex/psigen-design-answer.md`) reviewed the ABSTRACT `movedC`
algebra and flagged frame mixing as a *risk* ("You need a proved per-layer block readback after framing …
Triangular hypotheses may prevent leakage but still may introduce block-unit factors"), but the recipe
that was banked (frame-blind reads) does not account for it.

## The correction (verified reachable)

`psiSplitRawGen` must write **frame-dependent** boundary reads (interior stays frame-blind). Layer 0
(computed; `P11 = deepBlkA_0⁻¹`, `P21` = the (2,1) block of `reindex(Pf_0)`):

    X'_0 = X_0                                          (unchanged)
    Y'_0 = P11⁻¹ · movedY(Cq_0)          (= deepBlkA_0 · movedY)
    Z'_0 = Z0edit0 − P21 · X_0
    T'_0 = movedT(Cq_0) − P21 · P11⁻¹ · movedY(Cq_0)

With these, the LITERAL framed move identity holds at layer 0 (verified blockwise):
`₁₁ = 1+P11·X`, `₁₂ = P11·(P11⁻¹·movedY) = movedY`, `₂₁ = P21·X + (Z0edit0−P21·X) = Z0edit0`,
`₂₂ = P21·P11⁻¹·movedY + movedT − P21·P11⁻¹·movedY = movedT`. The last layer is symmetric (block-UPPER
`Qf`, `deepBlkZ_last = 0`).

Crucially these SAME frame-dependent reads keep `hsub4core` consistent: the frame-free decode Schur core
at each boundary layer equals `blockSchur(movedC Cq_s)` — the block-lower left / block-upper right frames
with identity ₂₂-block are **Schur-invisible** (Codex-computed, `codex/move-identity-frame2-answer.md`
Q1: the `P21` row-op cancels inside the (1,1)-pivot Schur; `P11` cancels via `Adec = P11⁻¹·Am`,
`Ydec = P11⁻¹·MY`). This Schur-invisibility is **already banked**: `schur_frame_transform`
(`DeepestBlockDecomp.lean:244`) gives `Schur(P·M·Q) = DP·Schur(M)·DQ`, which at `DP = DQ = 1` (the
bundle's identity ₂₂-blocks, `hP22one`/`hQ22one`) is `Schur(P·M·Q) = Schur(M)`. No new Schur-frame
bedrock is required.

The frame factors are `q`-independent constants (the frames are fixed), so the frame-dependent reads are
still `ContDiff` and vanish at `q = 0` — the diffeo triple (`DeepestPsiFlatCutGen`) is unaffected.

## Reachability verdict (decorrelated Codex, xhigh, corrected premise)

`codex/move-identity-frame2-answer.md`: **REACHABLE-AS-BANKED** for the reg side (`hsub3reg` via the
banked `deepestEFull_sq_sum_eq_of_chain_movedC` with the corrected `psiSplitRawGen`). (The first consult
`move-identity-frame-answer.md` returned NEEDS-REARCHITECT, but under the WRONG premise "interior frames
non-trivial"; that premise is retracted — the bundle guarantees interior frames = identity.)

## Proved / Assumed / Cited / Deferred

- **Proved (this thread).** Nothing in Lean. The design correction + the blockwise verification of the
  corrected layer-0 reads (on paper, above) + the decorrelated Codex re-adjudication.
- **The precise remaining build (for the next tide / controller), in order:**
  1. **`psiSplitRawGen` (corrected).** Interior reads = `movedData − deepBlk`; the two boundary layers
     use the frame-dependent reads above (`Y'_0 = deepBlkA_0·movedY`, etc.), plus the symmetric last
     layer. Write via `regGaugeSlotEquiv.symm` (gauge edit) + `paramsEquivFlat` core-slot update. The
     frame factors are expressible via `deepBlkA_0`, `deepBlkZ_0` (network-free, available). ~400-600 L.
  2. **The FRAMED-chain readback + move identity.** No per-layer framed-chain block decode exists yet
     (only the frame-FREE `reindex_decode_blocks_split`, `DeepestLDUReadback:342`). Build the framed-layer
     block decode `Cq_s = fromBlocks …` (interior = decode readback; boundary = frame-mixed via
     reindex(Pf_0) = fromBlocks P11 0 P21 1), then `funext s; by_cases s < L` matching four blocks; tail =
     corM corner; last-layer `pivotThr`/`rThr` neutralised at `J = frontEmbed`. ~500-800 L.
  3. **Diffeo triple** → `DeepestPsiFlatCutGen` (`psiSplitRawGen 0 = 0`, ContDiffAt, `D(ψ−id)(0)=0`). ~150 L.
  4. **`hsub4core` — the GENUINE remaining new-ish piece.** The general-L Schur-product-to-Score readback
     (`∏_s blockSchur(decode(psi q)_s) → Score` via Invariant B `prodSchurCore_eq_blockSchur_partProd` +
     endpoint-frame telescope + the `−B` corner normalization). This is the general-L analog of the L=2
     `prod_deepestM_eq_schur_ldu_readback`, flagged "numerically certified, NOT yet in Lean"
     (`DeepestDiffeoBridgeGenConj.lean:33`). NOT bounded plumbing — the hardest remaining piece. ~400-700 L.
  5. **Compose** `deepest_diffeo_bridge_gen_assembled` (byte-matches `hstep2:1060` RHS) with the triple +
     `hsub3reg` + `hsub4core` + `deepBlk_boundary_gen`/`deepBlkA_isUnit_gen` (`DeepestDeepBlkBoundaryGen`).
     ~100 L.
- **Cited.** `schur_frame_transform` (`DeepestBlockDecomp:244`) — boundary-frame Schur-invisibility,
  banked. `deepestPoint_frame_pivot_triangular_exists` interior-triviality clause. Codex xhigh (two
  consults, both persisted under `codex/`).
- **Deferred.** The full close (items 1-5 above), with item 4 (`hsub4core` general-L Schur→Score) the
  genuine remaining content, not plumbing.

## Status
`hstep2` UNTOUCHED (not laundered). Build unchanged at `0bbc750c` (no Lean edits). Design flaw found +
corrected + reachability re-adjudicated. Two Codex artifacts persisted. Controller decision needed: the
corrected `psiSplitRawGen` (frame-dependent boundary reads) supersedes the germs5/cert frame-blind
recipe; a follow-up tide builds items 1-5.
