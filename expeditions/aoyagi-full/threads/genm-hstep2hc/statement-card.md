# Statement card — genm-hstep2hc (#120 `hstep2`, item 3, Piece 2 + Piece 1)

**Branch:** `genm-hstep2hc` (pushed to origin). **Base:** `expedition/aoyagi-full` @ `03a9f690`.

## Piece 2 — the DECODE-chain invertibility germs — DELIVERED, sorry-free, axiom-clean

**Status:** green, `scripts/sorries` = 0, forced `#print axioms` = `[propext, Classical.choice, Quot.sound]`
on all three germs (no `sorryAx`, no `native_decide`, no `monomial_rlct`, no `cited_aoyagi_dln`). Zero lint
warnings. **NOT reviewed yet** (fidelity check pending — leaf executor does not self-review).

**File:** `lean/DLNFibre/DLN/RLCT/Validate/DeepestHsub4coreInvGerm.lean` (new, ~250 L, 0 sorry). STANDALONE;
**NOT yet imported into `DLNFibre.lean`** — the controller wires it (single-writer) and adds the three germs
to `AxCheck.lean`.

### The three germs (match the keystone's `hLayer`/`hPart`/`hMid11inv` shapes exactly)

At the basepoint `x₀ = (paramsEquivFlat H) (deepestPoint H r B hB hr hL)`, delivered as `∀ᶠ x in 𝓝 x₀, IsUnit …`:

> **`eventually_isUnit_deepestChain_decode_toBlocks₁₁`** (for `hLayer`, `k < L`)
> `∀ᶠ x in 𝓝 x₀, IsUnit ((deepestChain H r hr ((paramsEquivFlat H).symm x) k).toBlocks₁₁)`.
> Hyps: `hDA : ∀ s, IsUnit (deepBlkA H r B hB hr hL s)`.

> **`eventually_isUnit_partProd_deepestChain_decode_toBlocks₁₁`** (for `hPart`, `k ≤ L`)
> `∀ᶠ x in 𝓝 x₀, IsUnit ((partProd (deepestChain H r hr ((paramsEquivFlat H).symm x)) k).toBlocks₁₁)`.
> Hyps: `hDA`.

> **`eventually_isUnit_prod_decode_pivot_toBlocks₁₁`** (for `hMid11inv`)
> `∀ᶠ x in 𝓝 x₀, IsUnit ((reindex (rThr 0) (pivotThr J) (prod H ((paramsEquivFlat H).symm x))).toBlocks₁₁)`.
> Hyps: `hDA`, `J`, `hJfront : J = frontEmbed H r hr`.

**Gloss / route.** Continuity in `x` is immediate — `(paramsEquivFlat H).symm` is a continuous linear equiv
(`continuous_paramsEquivFlat_symm`), `deepestChain`/`partProd`/`prod` entries continuous, `toBlocks₁₁.det`
continuous — so `eventually_isUnit_of_continuousAt_det` reduces each germ to a nonzero determinant at `x₀`.
At `x₀`, `(paramsEquivFlat H).symm x₀ = deepestPoint`, and the basepoint values are all `deepBlkA` products
(units by `hDA`):
- `hLayer`: `(deepestChain deepestPoint k).toBlocks₁₁ = deepBlkA k` (`deepestChain_toBlocks₁₁_eq_layer`, the
  new width-relabel bridge, + the `deepBlkA` def).
- `hPart`/`hMid`: `(partProd (deepestChain deepestPoint) k).toBlocks₁₁ = ∏_{j<k} deepBlkA j`
  (`partProd_deepestChain_deepestPoint_toBlocks₁₁_isUnit`, a `.toBlocks₁₂ = 0` telescoping induction resting
  on `deepBlkY = 0` at the non-last deepest layers — layer-0 + interior col-vanishing). `hMid` at `k = L`
  via `J = frontEmbed` (`pivotThresholdSplit_frontEmbed`) + `pivotFront_toBlocks₁₁_eq_chainCol` +
  `reindex_prod_eq_partProd`, and `prod deepestPoint = B`.

**Bundled germs (drop-in for the `filter_upwards` assembly — the `∀ k` form at fixed `x`):**
`eventually_all_isUnit_deepestChain_decode_toBlocks₁₁` (`∀ᶠ x, ∀ k, k < L → IsUnit …`) and
`eventually_all_isUnit_partProd_deepestChain_decode_toBlocks₁₁` (`∀ᶠ x, ∀ k, k ≤ L → IsUnit …`), via
`Finset.eventually_all` over `range L` / `range (L+1)`. (The per-`k` germs remain as the reviewed
building blocks; the bundled forms remove the assembler's finite-intersection step.)

**Supporting new lemmas (same file):** `deepestChain_toBlocks₁₁_eq_layer`,
`deepestChain_toBlocks₁₂_eq_zero_of_cols_vanish`, `continuous_deepestChain_layer`,
`continuous_partProd_deepestChain`, `partProd_deepestChain_deepestPoint_toBlocks₁₂_eq_zero`,
`partProd_deepestChain_deepestPoint_toBlocks₁₁_isUnit`.

**Fidelity review:** PASS on all three per-`k` germs (independent reviewer, line-by-line source match to
the keystone `hLayer`/`hPart`/`hMid11inv`; `IsUnit ↔ Nonempty Invertible` conversion faithful; base,
`hDA`/`J`/`hJfront` honest; non-vacuous). Card confirmed accurate.

## Piece 1 — `hC` (the core-side move readback) — step-A BANKED; remaining grind scoped (bounded)

**Update (controller re-scoped as bounded — build it):** `hC` step-A is DELIVERED, green, 0 warnings:
`absorbedCoreConj_eq_blockSchur_synthetic` in `lean/DLNFibre/DLN/RLCT/Validate/DeepestHsub4coreHCGen.lean`
— the generic reduction `coreRead pc s + schurCorrectionConj pg s = blockSchur(fromBlocks (deepBlkA+X)
(deepBlkY+Y) (deepBlkZ+Z) coreRead)` (pure algebra, `nonsing_inv_eq_ringInverse`). Confirms `M_s`.
**DELIVERED so far (green, 0 warnings, pushed):** step-A `absorbedCoreConj_eq_blockSchur_synthetic`
AND **lemma-1** `deepestChain_toBlocks₁₂_eq_layer` / `…₂₁…` / `…₂₂…` (the off-diagonal/core analogues
of the Piece-2 `…₁₁…` bridge, matching the framed-block reindex convention).

**Remaining (all banked pieces, no new math, ~200-300 L) — precise lemma list + proof sketch:**
2. interior-vanishing helpers `deepBlkZ_interior_zero` / `deepBlkT_interior_zero` (~10 L each; mirror the
   banked `deepBlkY_interior_zero`; `deepBlkZ` via `deepestPoint_interior_eq_corM` + `if_neg` on row `≥ r`,
   `deepBlkT` via `deepestPoint_interior_cols_vanish`).
3. `deepestChain_framed_eq_decode_interior` — for interior `s` (`0<s`, `s+1<L`, `Pf s = Qf s = 1`),
   `deepestChain(framedParamsPivot(split x)) s = deepestChain(decode x) s` (both chain-width, SAME type;
   `← fromBlocks_toBlocks` + 4 block equalities: framed via `deepestChain_framedParamsPivot_blocks_of_frame_one`,
   decode via lemma-1 + `reindex_decode_blocks_split`, matched by interior `deepBlkA=1`/`deepBlkY=Z=T=0`).
4. `blockSchur_deepestChain_framed_eq_decode` (per-`s`): interior via (3); boundary (`s∈{0,L-1}`) via
   `blockSchur_lowerFrame_left`/`_rightUpper_right` (banked) — framed layer = endpoint-frame · decode-layer.
5. `Kcoup_framed_eq_decode` (the crux; `partProd(F) = lowerFrame·partProd(D)` factoring so `P11` cancels,
   + `Kcoup_zero` at k=0, + last-layer pivot). Then `schurTilde F s = schurTilde D s` from (4)+(5).
6. assemble hC = step-A ▸ (4)+(5)-via-`schurTilde`(Invariant B) ▸ `psiSplitRawGen_deepestChain_hmove`
   + the width-cast reconciliation (`blockSchur` naturality under the `finCongr` outer-block relabel).

### The Codex route (verified derivation, kept below)

**Verdict (Codex xhigh, `codex/hc-route-{prompt,answer}.md`):** `hC` is REACHABLE for the chart-specialised
`q = split x`, but its core is a substantial UNBANKED lemma. NOT built (no sorry-scaffold, per discipline).

**Confirmed correct (my analysis, Codex-endorsed):** after the banked readbacks `coreRead_psiSplitRawGen` +
`gaugeReadX/Y/Z_psiSplitRawGen`, the `hC` LHS equals `blockSchur M_s` where
`M_s = fromBlocks (deepBlkA+psiReadBlk₁₁) (deepBlkY+psiReadBlk₁₂) (deepBlkZ+psiReadBlk₂₁) (psiReadBlk₂₂)`
(uses `Matrix.nonsing_inv_eq_ringInverse` to bridge `schurCorrectionConj`'s `⁻¹` to `blockSchur`'s
`Ring.inverse`; rests on `deepBlkT_s = 0` at every layer — banked layer-wise, needs a cheap all-layer
wrapper).

**The route (7 steps, Codex):** (1) apply `absorbedCoreConj_eq_schurCore` to `psiSplitRawGen q` written as
`deepestSplit w0 wψ`, `wψ := split.symm (psiSplitRawGen q)` → LHS `= blockSchur (reindex(decode wψ) s)`;
(2) discharge `hT = deepBlkT_s = 0` layerwise; (3) boundary Schur-invisibility
(`blockSchur_lowerFrame_left`/`blockSchur_rightUpper_right`, BANKED) + `framedParamsPivot_eq_frame_of_front`
→ `blockSchur (deepestChain (framedParamsPivot (psiSplitRawGen q)) s)`; (4) `psiSplitRawGen_deepestChain_hmove`
→ `blockSchur (movedC (deepestChain (framedParamsPivot q)) … s)`; (5) specialise `q = split x`; **(6) the WALL**;
(7) width-cast cleanup (`chainWidth_·_sub`, `deepestChain_toBlocks₁₁_eq_layer`).

**THE SUB-GAP (step 6) — the single missing lemma, NOT banked:**
> `blockSchur_movedC_framedSplit_eq_decode`: for `q = split x`,
> `blockSchur (movedC (deepestChain (framedParamsPivot … (split x))) (Z0edit0 …) s)
>   = blockSchur (movedC (deepestChain ((paramsEquivFlat H).symm x)) (Z0edit0 …) s)`.
> Equivalently (Invariant B `blockSchur (movedC C) = schurTilde C = (1−Kcoup C s)·blockSchur (C s)`):
> `schurTilde (framedChain(split x)) s = schurTilde (decodeChain x) s`.

**Why it is a genuine wall, not plumbing.** Per-layer `blockSchur (framedChain s) = blockSchur (decodeChain s)`
IS reachable (interior frames = id; boundary via the banked one-sided frame-invisibility). But `schurTilde`
carries the GLOBAL `(1 − Kcoup C s)` factor, and `Kcoup C k = (C k)₂₁·(partProd C (k+1))₁₁⁻¹·(partProd C k)₁₂`
reads the PARTIAL PRODUCTS, which differ between the framed-split and decode chains by the endpoint frames
(the base chains are NOT blockwise equal at the boundary — Codex-confirmed via `framedParamsPivot_eq_frame_of_front`,
which gives `Pf·(decode)·Qf`, not `decode`). So `Kcoup` frame-invariance through the boundary frames is the
real new content — a `regBlocks_movedC`-flavoured Schur/Kcoup invariance across two base chains, est. 200-400 L,
its own focused tide. The banked `regBlocks_movedC` (Invariant A) is the reg-residual analogue; step 6 is its
core-side counterpart and is not yet banked.

## Explicitly NOT in scope (Producer-1-gated)

The `hq` cutoff-ball germ and the final `filter_upwards` assembly (need `psiSplitRawGen` continuity-at-base,
Producer 1). Not built here.
