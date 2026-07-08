# Statement card — genm-hcfinish (hC COMPLETE)

## ✅ hC COMPLETE (2026-07-08) — `coreAbsorbConj_reindex_eq_blockSchur_movedC_decode`

The full keystone `hC` for `q = split x`, green, sorry-free, forced
`#print axioms = [propext, Classical.choice, Quot.sound]` (no `sorryAx`/`native`/cited). Its conclusion
matches the keystone `deepestCoreF_coreAbsorbConj_psiSplitRawGen_eq_score_at_chart`'s `hC` hypothesis
verbatim (at `q = split x`). Boundary + assembly landed via option (b): the moved-framed-pivot unit is
derived via hmove inside the assembly (`(F' 0)₁₁ = (F 0)₁₁ = P11·(D 0)₁₁`), so hC's hypothesis set stays
the keystone's expected set (no new hyp). **Controller: wire the module into `DLNFibre.lean` + AxCheck, and
green-gate the full `lake build DLNFibre` (isolated build does not catch aggregate name clashes; I rg-checked
my new top-level names — none clash).** Route detail below is the historical record.

---

**Branch:** `origin/genm-hcfinish` (pushed). **Base:** `origin/genm-hstep2hc` @ `0c04d285`.
**File:** `lean/DLNFibre/DLN/RLCT/Validate/DeepestHsub4coreHCGen.lean` (extended in place; NOT yet wired
into `DLNFibre.lean` — controller wires, single-writer). Green, `scripts/sorries` = 0.
**Forced `#print axioms`** (olean deleted, re-elaborated) on the load-bearing lemmas = `[propext,
Classical.choice, Quot.sound]` — no `sorryAx`, no `native_decide`, no `monomial_rlct`, no `cited_aoyagi_dln`.
No name clashes vs siblings.

## Delivered (all green, axiom-clean)

- **Lemma 2** `deepBlkZ_interior_zero`, `deepBlkT_interior_zero` — interior deepest `(2,1)`/`(2,2)` blocks
  vanish (corner `diag(I_r,0)` kills rows `≥ r`).
- **Abstract frame machinery** (the core-side counterpart of the reg-side `regBlocks_movedC`, decoupled
  from reindex bookkeeping):
  - `leftFrame_ringInverse_cancel`, `rightFrame_ringInverse_cancel`, `conj_ringInverse_cancel` —
    `Ring.inverse` cancels through unit frames (via `invOf`).
  - `blockSchur_lowerFrame_of_blocks`, `blockSchur_upperFrame_of_blocks` — a one-sided block-triangular
    frame (identity `₂₂`, unit `₁₁`) is `blockSchur`-invisible (direct block algebra).
  - `partProd_frame_pre` / `partProd_frame_last` — the partial-product telescope
    (`partProd Cf k = PL·partProd Cd k` for `1≤k≤M`; `partProd Cf (M+1) = PL·partProd Cd (M+1)·QU`).
  - **`Kcoup_frame_endpoints`** — endpoint frames preserve `Kcoup` (`Kcoup Cf s = Kcoup Cd s`); the crux
    abstract lemma. `P11`/`Q11` cancel through `Kcoup`'s inverse (interior `leftFrame`, last `conj`).
- **Lemma 3** `deepestChain_framed_eq_decode_interior` — interior framed chain = decode chain (frames = 1).
- **Boundary decompositions** `deepestChain_framed_layer0_eq` (`F 0 = psiFrame0·D0`),
  `deepestChain_framed_lastLayer_eq` (`F M = D M·psiFrameLast`) — via `framedParamsPivot_eq_frame_of_front`
  + `reindex_mul`.
- **Block-condition helpers** `psiFrame0_blocks` (`₁₂=0`,`₂₂=1`,unit `₁₁`), `psiFrameLast_blocks`
  (`₂₁=0`,`₂₂=1`,unit `₁₁`) — via `reindexChainSq_fromBlocks`.
- **Lemma 5 (the crux, DLN)** `Kcoup_framed_eq_decode` — `Kcoup(framedChain(split x)) s =
  Kcoup(decodeChain x) s`. Instantiates `Kcoup_frame_endpoints` with `psiFrame0`/`psiFrameLast` +
  the three decompositions. **This is the load-bearing content the controller flagged as bounded-substantial.**
- **Lemma 4** `blockSchur_framed_eq_decode` — per-layer `blockSchur(F s) = blockSchur(D s)` (interior via
  lemma 3; boundary via the frame-invisibility helpers).
- **`blockSchur_reindex_reduced`** — `blockSchur` commutes with a reduced-width relabel (naturality; by
  defeq after unfolding).
- **Claim-C interior** `coreAbsorbConj_reindex_eq_blockSchur_framed_interior` — for interior `s`,
  `reindex(cc,ss)(coreRead_moved + schurCorrectionConj_moved) = blockSchur(F' s)` (F' = moved framed chain).
  Via step-A (`absorbedCoreConj_eq_blockSchur_synthetic`, banked) + `deepestChain_framedParamsPivot_blocks_of_frame_one`
  + interior deepBlk + `blockSchur_reindex_reduced`.

## Remaining to close the keystone's `hC` (the "step-6 wall", scoped-separate)

The keystone `hC` (for `q = split x`) is, per `s : Fin L`:
`reindex(cc,ss)(coreRead_moved s + schurCorrectionConj_moved s) = blockSchur(movedC D (Z0edit0 D L) (s:ℕ))`.

**Assembly reduction (worked out, uniform):** RHS `= blockSchur(movedC D … s) = schurTilde D s
= (1−Kcoup D s)·blockSchur(D s) = (1−Kcoup F s)·blockSchur(F s)` [lemma 5 + lemma 4] `= schurTilde F s
= blockSchur(movedC F … s) = blockSchur(F' s)` [`psiSplitRawGen_deepestChain_hmove` + `blockSchur_movedC`].
So **`hC ⟺ Claim-C` (`LHS = blockSchur(F' s)`) for all `s`.**

**What is left:**
1. **Claim-C boundary** (layers `0`, `L−1`): `reindex(cc,ss)(coreRead_moved + schurCorrectionConj_moved)
   = blockSchur(F' s)`. Route (Codex-confirmed): `deepestChain_framedParamsPivot_firstLayer` gives
   `F' 0 = corM + psiFrame0·(chain reads)`; with `corM = psiFrame0·(chain-reindexed deepest_0)`
   (from `hNF` at `firstLayer` + `reindexChainSq_fromBlocks`) this is `psiFrame0·(reduced-relabel M_0^m)`
   (`deepBlkT_layer0_zero` folds the `(2,2)`); then `blockSchur_lowerFrame_of_blocks` + `blockSchur_reindex_reduced`.
   Symmetric at `L−1` (`_lastLayer`, `psiFrameLast`, `blockSchur_upperFrame_of_blocks`,
   `deepBlkZ_layerLast_zero`). **Interfaces with `psiGhat`/`psiTargetD`/`forcedDecodeLeft` banked machinery.**
   Est. ~120 L (2 cases).
2. **Assembly** (`hC` for all `s`): dispatch interior (Claim-C interior) / boundary (Claim-C boundary),
   then RHS `= blockSchur(F' s)` via the reduction above. Est. ~50 L.

**No wall** — the route is fully worked out and Codex-confirmed; the remainder is bounded reindex-readback
plumbing (the statement card's original "step-6, est. 200–400 L, own focused tide"). NOT laundered into a
sorry.

## Update — boundary corner identity landed + the invertibility-threading finding

- **Delivered (green, axiom-clean):** `psiFrame0_mul_deepestChain_deepestPoint_eq_corM` —
  `psiFrame0 · deepestChain(deepestPoint) 0 = corM`. Via `deepestSplit_mp_basepoint` (`split w0 = 0`) +
  `deepestChain_framed_layer0_eq` at `w0` + `deepestChain_corner_eq_corM` /
  `framedParamsPivot_zero_eq_corner` (banked). (Imports added: `DeepestPsiHraw0Gen`, `DeepestSplitConcrete`.)
  The last-layer analogue mirrors it via `deepestChain_framed_lastLayer_eq`.

- **Boundary Claim-C route (fully de-risked):** for layer 0, `deepestChain_framedParamsPivot_firstLayer`
  gives `F' 0 = corM + psiFrame0 · FBchain`; the corM identity + `fromBlocks_add` + reindex additivity +
  `deepBlkY_layer0_zero`/`deepBlkT_layer0_zero` fold this to `F' 0 = psiFrame0 · N_0`, where
  `N_0 = reduced-relabel(M_0^m)`. Then `blockSchur(F' 0) = blockSchur(psiFrame0·N_0) = blockSchur(N_0)`
  (`blockSchur_lowerFrame_of_blocks`) `= reindex(cc,ss)(blockSchur M_0^m)` (`blockSchur_reindex_reduced`).
  Symmetric at `L−1`.

- **The finding (controller decision):** `blockSchur_lowerFrame_of_blocks` needs
  `IsUnit (N_0.toBlocks₁₁) = IsUnit (deepBlkA_0 + gaugeReadX_moved 0)` — the **moved** synthetic pivot.
  The keystone's `hLayer` is for the **decode** chain (a DIFFERENT gauge read), so it does not directly
  supply it. It IS derivable: `(F' 0)₁₁ = P11·N_0₁₁` (from `F' 0 = psiFrame0·N_0`), and `(F' 0)₁₁ =
  (movedC F 0)₁₁ = (F 0)₁₁ = P11·(D 0)₁₁` (hmove + `deepestChain_framed_layer0_eq`) is a unit; so
  `N_0₁₁ = P11⁻¹·(F' 0)₁₁` is a unit. Either thread a moved-pivot-invertibility hyp (Producer-1
  cutoff-ball-dischargeable) or derive via hmove inside. Both honest.

Remainder after this: boundary Claim-C (2 layers) + the ∀s assembly. ~150 L.
