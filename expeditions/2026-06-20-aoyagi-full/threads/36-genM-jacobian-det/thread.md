# Thread 36 — general achiever Jacobian determinant: route adjudication

**Seat:** scout (recon/design). **Date:** 2026-06-26. **Branch:** `expedition/aoyagi-full`.
**Mandate:** adjudicate the route (a / c / hybrid) for the ∀M achiever-chart Jacobian determinant
`|det Dφ_{M,t}| = ∏_j |u_j|^{leafH j}` — the ONE residual gating
`routeMCore_box_diverges_achiever` ∀M (`RouteMLayerCoverGE.lean:130`) — and hand the controller a
broken-down, bounded build plan.

## Deliverable

`design.md` (this thread): route recommendation + the parametric Schur-frame det theorem + the
Mathlib route + the flat-coordinatization plan + the Phase A/B/C bounded build plan + the
(3,3,3,3) cross-check.

## Headline (the reversal vs the wall report `be84b67b`)

The prior wall report scoped the general det as "multi-week parametric Schur-frame/LDU determinant"
and recommended shipping only the 3 anchors. **That estimate predated the structural collapse found
here:** the per-boundary Schur differential is BLOCK-LOWER-TRIANGULAR (TL,TR,BL,BR ↔ dK,dN,dX,dE),
with diagonal blocks `1, K·(−), (−)·K, 1` — so `|det| = |det K|^{r+c}` via `det_pi`, with NO
per-instance SCC `frameB` grading. The det is now a BOUNDED local theorem; the keystone has MOVED to
the flat-coordinate decoder identity `chartParamsFlat = chartParamsGen`.

## Verification (decorrelated, three angles)

- `my_schur_det.py` — independent symbolic check `|det DS| = (det K)^{r+c}` over 10 (t,r,c) profiles. ✓
- `schur_factorization.py` — the differential is block-lower-triangular AND det-correct, all profiles. ✓
- `full_det_check.py` — full-chart (2,2,2) det: u-exp = `minAdm−1`, spectator unit ratio. ✓ (3,3,3,3
  cert-verified upstream, `verify_codex_3333.py`).
- `codex/route-{prompt,answer}.md` — decorrelated xhigh Codex consult. Confirms route (c) + rate
  transfer via `phiGen`; keystone = `chartParamsFlat_eq_chartParamsGen`; det now bounded; injOn
  structural; prefix-fold genuinely needed.
- Standalone Lean elaboration (`/tmp/det_mulleft_check2.lean`, `/tmp/det_conj_check.lean`,
  Mathlib-only) — A1 det-pi route pieces all elaborate clean against the v4.29 pin. The det engine is
  de-risked.

## Recommendation

Route **(c)** for det/cov; rate-transfer via the banked `routeMCore_phiGen`. Keystone =
`chartParamsFlat_eq_chartParamsGen` (C1); riskiest = C1 then the B2 prefix-fold. The det (A1–A3, B3)
is bounded/routine. ≈ 8–10 scoped lemmas across 3 phases — a chargeable sequence of bounded sub-builds,
NOT an open design problem. Full plan in `design.md §4`.

## No Lean edits (recon only). Artefacts: design.md + 3 verify scripts + the codex pair.

---

## UPDATE (formalisation tide, 2026-06-26) — item 2 DONE ∀M; item 3 = an ARCHITECTURAL wall (decoder redefinition), not a tactical induction

Banked sorry-free + axiom-clean `[propext, Classical.choice, Quot.sound]` (force-elaborated
`#print axioms`), on branch `worktree-agent-a3901f84e4049cbfa` (off `expedition/aoyagi-full`):

- **`RouteMConjBlock`** — the generic det-preserving block-conjugation workhorse. `conjBlockMap`/
  `conjBlockDeriv`/`conjBlock_hasFDerivAt`/`conjBlock_abs_det`: conjugate any nonlinear factor
  `g : B → B` (fderiv `gD`), identity on a rest `R`, into a full-ambient `ChartFactor N` via ANY
  `E : (Fin N → ℝ) ≃L B × R`; `|det D| = |det gD|` at the prefix block `(E u).1` (the rest washes
  out via `det_prodMap`+`det_id`, `det_conj` preserves). This REPLACES the heavy `ChartIdx`
  coordinatization for the DET (Codex-confirmed) — the det needs only SOME CLE.
- **`RouteMFactorFDeriv`** — the matrix-valued fderiv plumbing: diamond-free pi-norm
  `NormedAddCommGroup`/`NormedSpace`/`FiniteDimensional` on `Matrix (Fin l)(Fin m) ℝ` (norm topology
  `= rfl` the canonical matrix product topology), the matrix-mult continuous bilinear CLM `matMulBilin`
  (layered `mulLeftCLM` + outer), and the product rule `HasFDerivAt.matMul`.
- **`RouteMFactorMaps`** — item 2 COMPLETE. `schurFrameMap`/`lduCoreMap` (the nonlinear factor maps)
  with `HasFDerivAt` matching the banked Phase-A differentials (`schurFrameDeriv`/`lduCoreDeriv`) —
  Schur by the product rule over the 4 output blocks + entrywise match (`schurFrameDeriv_apply`,
  `noncomm_ring`/`add_mul`+`abel`); LDU by the triple-product rule + linear `matrixSplit` compose
  (matched to `lduDerivMat_apply`); chain via the banked LINEAR `chainUnitMap` (det 1).
  `schurChartFactor`/`lduChartFactor`/`chainChartFactor` (+ `_abs_det`): the three conjugated
  `ChartFactor N`s, parametric in the ambient-split CLE `E`, with their monomial dets.
- **`RouteMPhiFlatDet`** — the item-4 det ASSEMBLY skeleton. `phiFlat_abs_det_of_factored`:
  `|det (fderiv φ_flat u)| = ∏_j |u_j|^{leafH j}` GIVEN (item 3) `composeFold fs = phiFlat` +
  (item 4 bookkeeping) the per-factor det product = the leafH monomial. The det telescope between
  them is closed (`composeFold_abs_det` banked); `phiFlat_hasFDerivAt_of_factored` pins the factored
  fderiv from the map equality. So the DET SIDE is complete modulo item 3 + the leafH summation.

### The precise item-3 wall (re-scoped — INDEPENDENTLY confirmed by xhigh Codex, `codex/item3-wall-*`)

The keystone was thought to be `chartParamsFlat = chartParamsGen` (`rfl`, banked). The GENUINE
keystone is the FLAT map equality `composeFold fs = phiFlat`. It is UNPROVABLE with the current
`genBlkFlat` (`RouteMGenFlatChart.lean:65`): its decoder is an arbitrary MODULAR HASH
(`x ((i*31+j*7+…) % N)`) chosen because the RATE is coordinate-agnostic. Codex's concrete obstruction:
`L=1, M=(1,7)` ⟹ `Rfin 1` reads `x((j*7+17)%7) = x 3` for EVERY `j` — 7 block entries collapse to one
flat coordinate. No honest block-extraction CLE (independent block functionals) can match a hash that
identifies distinct entries; the `%N` overlap breaks injectivity-on-blocks, so it cannot be absorbed
into the `E_s` either.

**The fix (multi-pass, NOT a research wall):** REDEFINE `genBlkFlat` to decode block data via the
`chartIdxEquiv` role-slot coordinatization (disjoint structured slots, one summand per role), and build
the factor CLEs `E_s` from the SAME coordinatization (shared accessors). Then `composeFold fs = phiFlat`
is accessor lemmas + boundary induction, not a late extensional fight.

**Index alignment (confirmed, derived + Codex):** the Schur frame at boundary `s` has size
`(t_s+r_s)(t_s+c_s) = t_{s-1}·M_s = schurDim (s-1)`, NOT `schurDim s`. (3,3,3,3) check: frame `s=1`
size 9 = `schurDim 0`; frame `s=2` size 6 = `schurDim 1`. ✓

**Rate transfer SURVIVES the redefinition:** `routeMCore_phiGen` consumes only `GenBlk`/`hle`/`hC0`,
not the decoder — re-check `hC0` (identity boundary `Bmat 0 = I`, `Rmat 0 = 0`, `t_0 = M_0`) under the
structured decoder; audit downstream a.e.-positivity/unit facts separately if they read the decoder.

**Next-tide plan:** (1) structured `genBlkFlatStruct` via `chartIdxEquiv` role slots + the
`(Fin schurDim → ℝ) ≃L SchurInc`/`LDUParam`/chain flattening CLEs (`finrank SchurInc = (t+r)(t+c)`
verified, so `ofFinrankEq` exists — but must be the STRUCTURED one, sharing accessors with the
decoder, not abstract); (2) the factor list `fs` from those CLEs; (3) `composeFold fs = phiFlat` by
boundary induction; (4) re-check `hC0`; (5) the leafH summation (item 4) via `leafH3333_prod_eq`
pattern; (6) `phiFlat_abs_det` via the banked `phiFlat_abs_det_of_factored`.

---

## UPDATE-2 (same tide, 2026-06-26) — the decoder REDESIGN, dimension accounting RESOLVED, slot foundation banked

The controller authorised the `genBlkFlat` redefinition. Worked it out + decorrelated xhigh Codex
(`codex/decoder-{prompt,answer}.md`). Banked one more sorry-free + axiom-clean module:

- **`RouteMChartSlots`** — the disjoint role-slot reader API (the shared decoder/factor foundation).
  `schurSlotEquiv`/`liftSlotEquiv` (`Fin (schurDim k) ≃ Fin t_k × Fin M_{k+1}` via `finProdFinEquiv`),
  `readSchur`/`readLift` (`chartIdxEquiv`-based scalar readers, disjoint by construction),
  `readSchur_index_injective` / `readSchur_ne_readLift_index` (disjointness).

### THE KEY STRUCTURAL FINDING (resolves the "how to make it disjoint" question)

The raw `GenBlk` role sizes do **NOT** sum to `N` — they OVER-count. For (3,3,3,3): naive all-roles
total = 57, free (minus the fixed `Bmat 0 = I`, `Rmat 0 = 0`) = **39 ≠ N = 27**. THIS is why the old
decoder HAD to collapse coords (a modular hash): you cannot give 39 entries 27 disjoint slots. The
`GenBlk` blocks are NOT independent — `Bmat s`, `Rmat s`, `Rfin L` are DERIVED from the genuine free
coords (`K_s`, `X_s`, `N_s`, `E_s`, lift `W_s`) via the Schur-frame structure. Codex confirms: the true
coordinate space is `radial ⊕ (nonfixed Schur/lift roles) ≃ ChartIdx ≃ Fin (flatDim M)` (size `N`).

**Slot ↔ role alignment (verified vs (3,3,3,3), ∑ = N via `chartDim_eq_flatDim`):**
- `schurDim k = t_k·M_{k+1}` holds the Schur frame at boundary `s = k+1` for `k < L−1`
  (`(t_s+r_s)(t_s+c_s) = t_{s-1}·M_s = schurDim(s-1)`); `schurDim(L−1)` holds the LEAF residual
  `Rfin(L)` (`Text(L)·Wext(L)`).
- `liftDim k = (M_{k+1}−t_{k+1})·M_{k+2}` holds the lift `W_{k+1}`.
- (3,3,3,3): schurDim = 9,6,3 (frame(1), frame(2), leaf); liftDim = 3,6 (W_1, W_2). ∑ = 27 = N. ✓
- The radial pivot `u` is ONE distinguished slot within the boundary-0 frame (Codex: "the fixed
  residual slot repurposed as `u`" — prefer a named `pRad` over forcing flat coord 0).

### The next-tide structured-decoder build (de-risked plan, in order)

1. **`genBlkFlatStruct`** (NEW module, do NOT edit the gated `genBlkFlat` — `routeMCore_phiGen` is
   decoder-AGNOSTIC, so build a NEW `GenBlk` and reuse the rate). Per Codex: `Bmat s = [K_s ; X_s·K_s]`
   (rows `Text(s+1)+r_s = Text s`), `Nblk s = N_s`, `Rmat s` = bottom-right-only `E_s` block (so
   `C_s = B_s·Q(N_s) + u·R_s = [[K, KN],[XK, XKN+uE]]` — the Schur frame), `Wblk s = W_s`,
   `Rfin L = E`-leaf. `K_s` is `Text(s+1)×Text(s+1)` (= `t_s²`), assembled by `lduCoreMap` on LDU slots.
   **NEW HYPOTHESIS NEEDED:** the `Bmat` row-split `Text(s+1) ≤ Text s` (`t` weakly decreasing) —
   beyond the current `hle : Text(s+1) ≤ Wext s`. Achiever path is strictly decreasing, so it holds;
   thread it. Heavy: `Matrix.fromBlocks` / `Fin.append` row-split at dependent `Text` widths (the
   `lean/CLAUDE.md` dependent-`Fin` reassociation kernel applies).
2. **Rate re-check:** `routeMCore_chartParamsFlat` for `genBlkFlatStruct` via `routeMCore_phiGen` —
   only `hC0` (identity boundary `C 0 · suffix = suffix`) needs re-proving under the structured decoder
   (`Bmat 0 = I`, `Rmat 0 = 0`, `chainQ` at `c_0 = 0` is `I`). Audit a.e.-positivity/unit facts.
3. **Factor list `fs`:** the `E_s` CLEs = the role splits from `RouteMChartSlots` (NOT arbitrary
   block-extractions). Build `composeFold fs` from the SAME `readSchur`/`readLift` + the item-2
   `schurChartFactor`/`lduChartFactor`/`chainChartFactor`/`radialFactor`.
4. **Item-3 (Codex's proof shape — avoid the final-flatten battlefield):** prove the `Params`-level
   `(paramsEquivFlat M).symm ∘ composeFold fs = chartParamsFlat` by `funext x; ext s i j` + LOCAL stage
   accessor lemmas (`genBlkFlatStruct_C_s_eq_schurFrame`, `_A_s_eq_chainA`, the `composeFold_after_*`
   read lemmas), then apply `paramsEquivFlat M` to get `composeFold fs = phiFlat`.
5. **Item-4 leafH summation** + the banked `phiFlat_abs_det_of_factored` → **`phiFlat_abs_det`**.

This is ≈4–5 modules of dependent-width block algebra — well-defined, no open design questions, but a
genuine multi-tide sequence (NOT a single tide). The det side (items 2 + 4-skeleton) + the slot
foundation are banked; the structured decoder + item-3 induction are the remaining build.

---

## UPDATE-3 (same tide cont.) — dependent-width decoder FOUNDATIONS banked; the assembly is the next sub-build

Pushed further through the structured-decoder wall. Banked (sorry-free + axiom-clean, in
`RouteMChartSlots`):
- **`bmatStack`** + `bmatStack_top`/`bmatStack_bot` — the derived Schur-frame kept block
  `Bmat s = [K ; X·K]` (`Text s × Text(s+1)`) at dependent widths: `finSumFinEquiv` row split (top `K`
  over `Text(s+1)` rows, bottom `X·K` over `r_s = Text s − Text(s+1)` rows) + a `Text(s+1)+r_s = Text s`
  reindex. The block-extraction laws resolve the `Fin.cast (castAdd/natAdd)` reads. The `t`-arity bridge
  (`Text` wants `Fin(L+1)→ℕ`) is handled.
- **`frameSplitEquiv`** — the Schur-frame slot K/X/N/E sub-split (`Fin (Text s·Wext s) ≃ (((K⊕X)⊕N)⊕E)`
  via the banked `roleSquare_eq` + left-nested `finSumFinEquiv.symm`). The per-frame role accessor base.

### Index alignment NAILED (concrete (3,3,3,3) trace)
GenBlk frame at index `s` has size `Text s · Wext s = schurDim(s−1)` (since `schurDim k =
Text(k+1)·Wext(k+1)`). So: **`schurDim k` (k=0..L−2) → frame at GenBlk `s=k+1`** (the `s−1` shift);
**`schurDim(L−1)` → leaf `Rfin(L)`** (`Text(L)·Wext(L)`); **`liftDim k` → `Wblk` at `s=k+1`**; GenBlk
`s=0` is the fixed identity boundary (consumes NO slots). Radial pivot = ONE designated slot.

### The next sub-build: `genBlkFlatStruct` ASSEMBLY (all components validated, the integration remains)
With `bmatStack` + `frameSplitEquiv` + the readers banked, the decoder assembly is:
1. Per interior `s` (1..L−1): read K/X/N/E matrices via `frameSplitEquiv` (slot `k=s−1`) +
   `finProdFinEquiv` (entry index) + `chartIdxEquiv.symm` + `x`. `Bmat s = bmatStack K X`; `Nblk s = N`;
   `Wblk s = W` (from `liftDim(s−1)`); `Rmat s` = bottom-right-placed `E` (the `u`-carrier; a
   `Matrix.fromBlocks 0 0 0 E`-style placement into `Text s × Wext s` — analogous to `bmatStack` but
   2D-padded). Boundary `s=0`: `Bmat 0 = I`, `Rmat 0 = 0` (identity). Leaf: `Rfin L` from `schurDim(L−1)`.
2. The LDU reparametrization: K is read as `t_s²` coords reparametrized `low/diag/up` (a further
   `finSumFinEquiv` sub-split of the K sub-slot) so the det carries the `∏|q|^{2(t−1−i)}` — OR keep K
   direct and let the LDU FACTOR (item-2 `lduChartFactor`) supply the reparametrization in `composeFold`.
   (Decide at assembly: cleanest is K-direct in the decoder, LDU in the factor — keeps the decoder
   simpler and matches the item-2 factor's job.)
3. Rate: `routeMCore_phiGenStruct` via the decoder-agnostic `routeMCore_phiGen` — re-prove only `hC0`
   (`C 0 · suffix = suffix`; `Bmat 0 = I`, `Rmat 0 = 0`, `chainQ` at `c_0 = 0` is `I` — the
   `RouteMGenChartId3333.genBlk3spec` pattern, now ∀M).
Then item-3 (Params-level stage induction, Codex shape) + item-4 (leafH summation) → `phiFlat_abs_det`.

The `Rmat s` bottom-right E-placement (a 2D padded block) is the one component not yet validated as a
standalone lemma (analogous to `bmatStack` but padding a `c_s`-col `r_s`-row block into `Text s × Wext s`
with zeros elsewhere) — the precise next dependent-width sub-step.

---

## UPDATE-4 (same tide cont.) — the s-1 index friction RESOLVED via k-indexing; rmatPad banked; assembly fully de-risked

Banked **`rmatPad`** (the `u`-carrier `Rmat s = [[0,0],[0,E]]` via `fromBlocks 0 0 0 E` +
`finSumFinEquiv` reindex) — the last decoder constructor. ALL dependent-width bricks are now validated:
`readSchur`/`readLift`, `bmatStack` (+ block laws), `frameSplitEquiv`, `rmatPad`.

### The indexing resolution (sidesteps the assembly's worst friction)
Index the decoder by the GenBlk boundary as `s = k+1` (so chart-slot `k` feeds GenBlk `Bmat (k+1)`),
NOT by `s` with a `s-1` slot read. Then the slot↔frame match is `rfl`-clean:
`schurDim M (fun j => Text M t (j+1)) k = Text(k+1)·Wext(k+1)` by `rfl`, and `frameSplitEquiv M t (k+1)`
gives the K/X/N/E split at exactly that size. The `s-1`-through-`dite`-guarded-`Wext` HEq friction (which
would have plagued every frame read) DISAPPEARS with k-indexing. (The `t`-arity bridge is
`fun j => Text M t (j+1)` — the ℕ→ℕ descent that `schurDim`/`chartIdxEquiv` consume.)

### genBlkFlatStruct assembly — fully de-risked, the remaining integration
Every component + the indexing are validated. The assembly (a `GenBlk M t` with `match`-on-`k`):
- `Bmat (k+1) = bmatStack M t (k+1) hdesc (Kreader k) (Xreader k)`; `Bmat 0 = reindex 1`.
- `Rmat (k+1) = rmatPad M t (k+1) h1 h2 (Ereader k)`; `Rmat 0 = 0`.
- `Nblk k = Nreader k`; `Wblk k = Wreader k` (from `liftDim k`); `Rfin L` from `schurDim(L-1)`.
- K/X/N/E readers: `frameSplitEquiv M t (k+1)`-inject the role index, `finProdFinEquiv` the (i,j),
  `chartIdxEquiv.symm ⟨k, Sum.inl ·⟩`, read `x`. (The `schurDim k`-vs-`Text(k+1)·Wext(k+1)` finCongr
  is `rfl`.)
- Hyps to thread: `hdesc : Text(k+2) ≤ Text(k+1)` (descent, achiever-strict) ∀k; `h2` already in `hle`.
- K kept DIRECT (no LDU in decoder) — the item-2 `lduChartFactor` supplies the LDU reparametrization in
  `composeFold`, matched in item-3.
Then rate (`hC0` re-check, `genBlk3spec` pattern ∀M) + item-3 (Params-level stage induction) + item-4
(leafH summation) → `phiFlat_abs_det`. This is the next pass: a substantial but design-complete module.

---

## UPDATE-5 (same tide cont.) — structured decoder + RATE COMPLETE ∀M; item-3 (map equality) is the last piece

Banked (sorry-free + axiom-clean): **`genBlkFlatStruct`** (the structured disjoint-slot decoder) +
**`routeMCore_phiFlatStruct`** (the UNCONDITIONAL rate `routeMCore (phiFlatStruct u) = u²·V` ∀M). The
delicate `hC0` (`C 0 = 1` at the identity boundary) is CLOSED: `C0_eq_one` via the `chainQ` kept-column
law (`chainQ_apply_castAdd`, every column kept at `c_0=0`) + the `Text 0 = Text 1 = Wext 0` (all `M_0`)
cast collapse. The `0+1`-vs-`1` normalization trap was the snag — fixed with `show`. The rate is
decoder-agnostic (`routeMCore_phiGen` consumes only `GenBlk`/`hle`/`hC0`), so the structured decoder
keeps it ∀M, confirming the design.

### Remaining for `phiFlat_abs_det`: item-3 (map equality) + item-4 (leafH summation)
- **Item-3**: `composeFold fs = phiFlatStruct` where `fs` = the item-2 factors (`radialFactor`,
  `lduChartFactor`, `schurChartFactor`, `chainChartFactor`) with CLEs `E_s` = the role splits matching
  the SAME `readK/X/N/E/W` slots. Codex's proof shape: `(paramsEquivFlat).symm ∘ composeFold fs =
  chartParamsGen u M t genBlkFlatStruct hle` by `funext x; ext s i j` + per-stage accessor lemmas
  (the factored layer-s = `chainA(N_s)(W_s)(C(s+1))` via `chainA/Q_apply_*`). THE deepest remaining
  piece — the factored-flat ↔ chainA-layer entry match over opaque widths.
- **Item-4**: the per-factor monomial dets (`radial |u|^{minAdm-1}`, `schur |K_s|^{r_s+c_s}`,
  `ldu ∏|q|^{2(t-1-i)}`, `chain 1`) summed into `∏|u_j|^{leafH j}` (the `leafH3333_prod_eq` pattern).
- Then the banked `phiFlat_abs_det_of_factored` (RouteMPhiFlatDet) → `phiFlat_abs_det`.

8 modules banked this tide. The det side's RATE + decoder + all det-foundations + the assembly skeleton
are done; item-3's map-equality induction is the final build.

### Item-3 CLE route validated (feasibility de-risked)
`flatToChartIdx : (Fin N → ℝ) ≃L (ChartIdx → ℝ)` via `ContinuousLinearEquiv.piCongrLeft` over
`chartIdxEquiv` elaborates cleanly — the first step of the per-factor CLE route. Remaining for item-3:
(a) per-factor `(Fin N → ℝ) ≃L Block_s × Rest` by composing `flatToChartIdx` + a `ChartIdx ≃ slot_s ⊕
rest` split (`sumPiEquivProdPi`) + the `(Fin schurDim → ℝ) ≃L SchurInc`/`LDUParam` block flattening;
(b) the factor list `fs` from these CLEs + the item-2 factors; (c) the entry-wise stage match
`(paramsEquivFlat).symm ∘ composeFold fs = chartParamsGen ∘ genBlkFlatStruct` (the chainA-layer
induction). This is the one genuinely-deep remaining build; the CLE machinery + all det/rate/decoder
foundations beneath it are banked.

---

## UPDATE-7 (same tide cont.) — PATH B REJECTED (Codex+controller); the bridge (PATH A′) is the irreducible reconciliation

The controller caught the ATOM confound: `NodeAchieverChart` bundles ONE map `phi` needing BOTH
`leaf_integrand` (RATE of phi) AND `cov` (DET of phi). I have RATE on `phiFlatStruct` + DET on
`composeFold fs` — TWO maps. PATH B (rate of composeFold fs directly) is NOT a shortcut (Codex + my
read): `routeMCore` reads via `paramsEquivFlat.symm`, so the rate of `composeFold fs` REQUIRES
identifying `(paramsEquivFlat).symm (composeFold fs u)`'s Params-layers = THE BRIDGE. PATH C (det of
phiFlatStruct directly) rebuilds the per-factor derivative decomposition — MORE work.

**PATH A′ (the cleanest, Codex-confirmed): prove the bridge ONCE at the Params level:**
`(paramsEquivFlat M).symm (composeFold fs u) = chartParamsGen u M t (genBlkFlatStruct u) hle`.
Then ONE map `phi := composeFold fs`: DET via `composeFold_abs_det_leafH` (free); RATE by transporting
the banked `routeMCore_phiFlatStruct` through the bridge. This discharges the atom's both fields.

The bridge IS the deep stage-induction (`funext`/per-layer match of the factored flat product to the
`chainA` layers over opaque widths). It is IRREDUCIBLE (all three paths need a reconciliation of this
depth; A′ is the cheapest + serves both fields). The DESIGN FREEDOM: choose `fs` so the bridge is
near-definitional — represent the factor fold as producing the `chainA` layers SEMANTICALLY (Codex).
This is the last wall; both endpoints (rate of phiFlatStruct; det of composeFold fs) + all
infrastructure are banked.

---

## UPDATE-9 (formalisation tide, 2026-06-27) — RATE ∀M LANDED (no bridge); det bridge-bricks banked + validated; the remaining crux isolated

The headline reframe (decorrelated xhigh Codex `codex/bridge-build-*` confirms it sound):
**the RATE is FREE at a general vector `x` — only the DET needs the bridge.** Banked sorry-free +
axiom-clean `[propext, Classical.choice, Quot.sound]` (force-elaborated `#print axioms`) on branch
`fm-genM-jacobian-det` (off `expedition/aoyagi-full`). New modules (controller: wire into aggregator,
dep order as listed):

1. **`RouteMFlatStructV`** — the VECTOR-parametrized structured chart + its rate ∀M. `phiFlatStructV M t
   ha hN x := phiGen (x p) M t (genBlkFlatStruct M t ha x) (hleStruct …)` (`p = ⟨0,hN⟩`), a genuine
   full chart map. `C0_eq_one_gen`/`hC0_struct_gen` generalize the identity-boundary `C 0 = 1` to an
   ARBITRARY decoder argument `x` + arbitrary scalar `v` (the proof reads only the x-independent
   constants `Bmat 0 = reindex 1`, `Rmat 0 = 0`). **`routeMCore_phiFlatStructV : routeMCore M
   (phiFlatStructV x) = (x p)² · UvalStructV x`** — the `NodeAchieverChart.leaf_integrand` rate factor
   for arbitrary `M`, with NO bridge, straight from the decoder-agnostic `routeMCore_phiGen`. This is
   the half of the chart that was missing; it is now closed ∀M.
2. **`RouteMPhiTargetDet`** — `phiTarget_abs_det_of_factored`: `|det Dφ| = ∏_j |u_j|^{leafH j}` for ANY
   target `φ` given `composeFold fs = φ` + the per-factor det bookkeeping (the det/cov compatibility
   step; `RouteMPhiFlatDet`'s `phiFlat`-specific lemma, freed to arbitrary target).
3. **`RouteMCLEConj`** — whole-space CLE conjugation `cleConjFactor E g gD hg : ChartFactor N` (`E.symm
   ∘ g ∘ E`, det `|det gD (E u)|` via `det_conj`) + **`composeFold_eq_cleConj_foldr`**: a list of
   `cleConjFactor E gᵢ` (same `E`) telescopes to `E.symm ∘ (gs.foldr) ∘ E`. This is the OPTION-1
   collapse — it **reduces the bridge `composeFold fs = phiFlatStructV` to a `Params`-LEVEL equality**
   `(gs.foldr id) = chartParamsGen ∘ genBlkFlatStruct` (the funext-s crux, not a flat induction).
4. **`RouteMLinearFactor`** — `linearFactor T` (a CLM as a `ChartFactor`, det `|det T|`), for the
   reshape/permutation factors.
5. **`RouteM4422Bridge`** (VALIDATE-SMALL-FIRST) — the factor-fold→real-chart route validated end-to-end
   on the cleanest anchor: `phi4422 = composeFold [linearFactor Q4422CLM, radialFactor {0,1,2,3} 0]`
   (`phi4422_eq_composeFold`), and the GENERIC `phiTarget_abs_det_of_factored` delivers `|det Dφ4422| =
   ∏_j |u_j|^{leafH4422 j} = |u 0|³` (`phi4422_abs_det_via_fold`). Confirms the whole det
   infrastructure wires to a real achiever chart. (NB `(4,4,2,2)` is a PURE radial blow-up — it does
   NOT exercise the Schur/LDU layer-ops; it validates the SPINE, not the general layer reconstruction.)
6. **`RouteMChainVar`** — `chainVarMap (N,W,C) = (N, W, C − N·W)` (variable-`N`, the OPTION-1 chain
   correction UPDATE-8 flagged), fderiv `chainVarD` (product rule), `chainVarD_abs_det = 1`
   (block-lower-triangular via `lowerTri`/`det_conj`/`prodAssoc`).

### The remaining crux (precisely isolated; the genuine multi-tide wall)
`composeFold fs = phiFlatStructV` reduces (via `composeFold_eq_cleConj_foldr`, `E = (paramsEquivFlatCLE
M).symm`) to the **`Params`-level layer equality**
`(gs.foldr id) (paramsEquivFlat.symm x) = chartParamsGen (x p) M t (genBlkFlatStruct M t ha x) hle`,
provable `funext s`. The irreducible difficulty is the **coordinate-alignment**: `genBlkFlatStruct`
decodes `x` via `chartIdxEquiv` ROLE SLOTS (K/X/N/E/W), while `paramsEquivFlat.symm x` decodes `x` into
the RAW Params layer layout — the layer-ops `gs` must read the role data from the Params point and match
it to `chartParamsGen`'s `chainA_s = [C_{s+1} − N_s W_s ; W_s]`, `C_s = bmatStack(K,X)·chainQ(N) +
(x p)·rmatPad(E)` recursion, over OPAQUE `Text`/`Wext` widths. The remaining build (UPDATE-8 OPTION-1
steps 1, 4, 6): (a) the structural per-layer `Params`-split CLEs exposing the role slots (dependent
widths — the hardest brick); (b) the layer-ops `gs` from `radialFactor`/`lduChartFactor`/Schur
frame/`chainVarMap` at the Params level; (c) the `funext s` matching (factor order = deepest-first
foldr; prefix states; `chainVarMap`; `Text`/`Wext` casts); (d) the `hdet` leafH summation
(spectator LDU/Schur exponents are GENUINE — leafH must carry them, Codex-confirmed; `leafH p =
minAdm − 1` is the only threshold-relevant entry). Then `phiTarget_abs_det_of_factored` (banked) closes
`cov`, and `nodeChartGeneral M (hpos : 1 ≤ minAdm M) : NodeAchieverChart M` assembles → atom discharged
via `routeMCore_box_diverges_of_nodeChart` (banked).

**Target signature correction (Codex):** `nodeChartGeneral` MUST take `(hpos : 1 ≤ minAdm M)` — an
unconditional ∀M form is FALSE (`NodeAchieverChart` carries `hpos`; `minAdm M = 0` has no achiever
center). The atom `routeMCore_box_diverges_achiever` already has `(hpos : 1 ≤ minAdm M)` in scope.

---

## UPDATE-10 (formalisation tide cont., 2026-06-27) — brick (a) LANDED: the bridgeCLE spine + the per-role Params-split CLE engine (ARCH-1)

Charged the det-bridge crux per the coordinator. Decorrelated xhigh Codex (`codex/brick-a-*`) adjudicated
the architecture: **ARCH-1** — ONE collapse CLE `bridgeCLE M := (paramsEquivFlatCLE M).symm`, all factors
`cleConjFactor (bridgeCLE M) g` with `g : Params M → Params M`. The chartIdxEquiv-slot ↔ paramsEquivFlat
alignment is **ABSORBED by CLE cancellation**, NOT a per-index proof (the key unblock). Banked sorry-free
+ axiom-clean `[propext, Classical.choice, Quot.sound]` (3 new modules + the layered anchor):

- **`RouteM222StructAdm`** — the LAYERED validate-small anchor: `M222=(2,2,2)`, `t222=(2,1,1)`
  (`Text=[2,2,1,1]`, `Wext=[2,2,2]` ⟹ Schur frame K/X/N/E all 1×1 nontrivial + chainA/Cgen recursion
  non-degenerate, unlike the pure-radial `(4,4,2,2)` spine-only anchor). `structAdm222 : StructAdm M222
  t222`.
- **`RouteMBridgeCLE`** (the brick-(a) SPINE) — `bridgeCLE` + `bridgeCLE_apply`/`_symm_apply`
  (= `paramsEquivFlat(.symm)`); `genBlkParamsStruct`/`radialParams`/`phiParamsStruct` + their
  `_bridgeCLE` cancellation lemmas (the alignment absorbed: `genBlkParamsStruct (bridgeCLE x) =
  genBlkFlatStruct x` via `paramsEquivFlat ∘ paramsEquivFlat.symm = id`); **`composeFold_bridge_eq`** —
  ANY layer-op list `gs` whose `cleConjMap (bridgeCLE M)`-factors are `fs` gives `composeFold fs =
  paramsEquivFlat ∘ (gs.foldr) ∘ paramsEquivFlat.symm`, reducing the bridge to the **Params-level**
  `(gs.foldr) ∘ bridgeCLE = phiParamsStruct ∘ bridgeCLE`; **`phiParamsStruct_bridgeCLE`** — the target
  `= chartParamsGen (x p) M t (genBlkFlatStruct x) hle`.
- **`RouteMRoleCLE`** (the brick-(a) per-role CLE ENGINE) — `flatToChartIdxCLE` (`(Fin N→ℝ) ≃L (ChartIdx
  →ℝ)` via `ContinuousLinearEquiv.piCongrLeft chartIdxEquiv`), `roleSplitCLE ρ` (via `sumPiEquivProdPi`),
  `flatBlockSplitCLE`/`paramsBlockSplitCLE ρ` (`Params M ≃L (Block→ℝ)×(Rest→ℝ)` — the `S` the ARCH-1
  factors `conjBlockMap` by, det read at the block via `conjBlock_abs_det`). Parametric in the role
  reindex `ρ : ChartIdx ≃ Block ⊕ Rest`; the `piCongrLeft`/`sumPiEquivProdPi` chain validated to
  elaborate against the v4.29 pin.

### What brick (a) delivered + the precise next sub-step
The two foundational obstacles are CLEARED: (i) the alignment (absorbed by `bridgeCLE` cancellation, no
opaque-bijection composition); (ii) the Params-split CLE construction (the `paramsBlockSplitCLE` engine,
parametric in `ρ`). The bridge `composeFold fs = phiFlatStructV` now reduces (via `composeFold_bridge_eq`
+ `phiParamsStruct_bridgeCLE`) to the **Params-level funext-s** `(gs.foldr id)(P) = phiParamsStruct(P)`.

REMAINING (brick (b)/(c)/(d), the next sub-build, in order):
1. **The role-semantic reindexes** `ρ : ChartIdx ≃ Block ⊕ Rest` per role (the Sigma-of-Sum extraction
   pulling the boundary-`k` Schur `K`/`X`/`N`/`E`, the lift `W`, the radial slot to the front). This is
   the role-specific input `paramsBlockSplitCLE` consumes — the next concrete brick.
2. **The layer-ops `gs`** (deepest-first foldr): `radialOp` (scale active slots, det `|u_p|^{minAdm-1}`),
   `lduOps` (`chainVarMap`/Schur via the role CLEs, spectator dets), `schurOps`, `chainOps` — each a
   `cleConjFactor (bridgeCLE M) (conjBlockMap (paramsBlockSplitCLE ρ) op)`.
3. **The funext-s bridge** `(gs.foldr)(P) = phiParamsStruct(P)` — riskiest sublemma (Codex): the layer
   source/target split (`C_{s+1} ⊕ W_s` = the top/bottom row split of Params layer `s`, via `finSplit`/
   `schurSlotEquiv`/`liftSlotEquiv` + the banked `chainA_apply_castAdd/natAdd`), proven at the
   equivalence level — then `funext s i j` is mechanical.
4. **`hdet` leafH summation** (radial `minAdm−1` on pivot + GENUINE spectator LDU/Schur exponents on
   `k=0` axes; Codex-confirmed) → `phiTarget_abs_det_of_factored` (banked) closes `cov`.
Then `nodeChartGeneral M (hpos : 1 ≤ minAdm M) : NodeAchieverChart M` assembles (rate banked via
`routeMCore_phiFlatStructV` + the bridge for the loss-base; det via the above) → atom discharged.

VALIDATE-SMALL note (Codex): `(2,2,2)` is right for the BRIDGE (chartIdxEquiv, role reads, chainA row
split); for the LDU DET story use a `2×2`-K case (`(3,3,3,3)` — genuine 2×2 LDU core + multi-pivot
spectators) — `(2,2,2)`'s 1×1 blocks hide LDU ordering.

---

## UPDATE-11 (formalisation tide cont., 2026-06-27) — bricks (b)/(c)/(d): a PRECISE DECODER WALL surfaced (the det target is not derivable from the current `genBlkFlatStruct`)

Charged (b)/(c)/(d). The funext-s bridge mechanics (c) are de-risked (Codex `codex/bcd-*` gives the
concrete `(2,2,2)` s=0 proof shape via `chainA_apply_castAdd`; the hardest cast is the row-index
alignment `hrow`). BUT a decorrelated xhigh Codex consult + my independent verification surfaced a
**genuine structural wall at the DECODER level** that blocks (d) — and makes building (c)/(d) against the
current decoder premature.

### THE SHARP SUB-PROBLEM (for the controller to decorrelate — pen-and-paper / Codex on the fix)
**The current `genBlkFlatStruct` does NOT encode the radial blow-up, so `|det Dφ| = |x p|^{minAdm−1}` is
NOT derivable from it.** Verified three ways:
1. **Source:** `genBlkFlatStruct` has `Rfin := fun _ => 0` (`RouteMGenFlatStruct.lean:150`) — the LEAF
   transition `C_L = u • Rfin L = 0`. And `structPivot := ⟨0, hN⟩` (`RouteMFlatStructV.lean:89`) is just
   flat coord 0, used as the radial scalar `u` with NO connection to the slot/role structure — so `x p`
   is simultaneously the radial scalar AND (opaquely, via `chartIdxEquiv`) some role coordinate.
2. **Mechanism (Codex Q1, my independent confirm):** the achiever blow-up needs active normal coords
   `(u, z₁,…,z_{m−1})` ↦ `(u, u z₁,…,u z_{m−1})`, det `|u|^{m−1}`, `m = minAdm` — the pivot `u` a
   DISTINCT slot, scaling a FIXED residual entry `=1` to produce the pivot output. The current decoder
   reads ALL E-entries as free `readE` coords (none fixed to `1`); `u = x p` enters ONLY linearly as
   `u • Rmat` (one scalar across the E-blocks). Its Jacobian scales the `Σ r_k c_k = minAdm` E-coords by
   `x p` giving `|x p|^{minAdm}` (off by one) — OR, since the pivot coord is not cleanly separated, the
   blow-up structure is simply malformed. Either way ≠ the clean `|x p|^{minAdm−1}`.
3. **The two DISCHARGED anchors used HAND-BUILT blow-up charts, NOT `genBlkFlatStruct`:** `(4,4,2,2)`'s
   `chartParams4422 = pack4422 ∘ pivotBlowupOn{0,1,2,3} 0` (`RouteM4422.lean`, 0 uses of
   `genBlkFlatStruct`); `(3,3,4)` likewise (`RouteMLayerCoverGEL2`, 0 uses). The general structured
   decoder was built + validated for the RATE ONLY (`routeMCore_phiFlatStruct = u²·V`), NEVER for the
   det. So this gap was latent.

### What the fix needs (Codex's shape — to be adjudicated)
Redefine the structured decoder to encode the radial blow-up: a designated `pRad`/`fixedSlot` (a residual
direction fixed to `1` that `u` scales to the pivot output) + nonzero leaf `Rfin`, so the `minAdm` active
directions are `(pivot, minAdm−1 free)` and the net radial det is `|u|^{minAdm−1}`. **The banked RATE
survives a decoder fix** — `routeMCore_phiGen` is decoder-agnostic (consumes only `GenBlk`/`hle`/`hC0`);
a revised decoder re-checks only `hC0` + re-derives `V`. But this is a structural decoder change, NOT a
funext-s tactic, and it ripples into `genBlkFlatStruct`/`StructAdm`/`hC0_struct`/`phiFlatStructV` — so it
wants a design adjudication before I build, lest I funext-s against the wrong target.

### What is BANKED + survives the fix (decoder-independent)
The brick-(a) spine (`RouteMBridgeCLE`: `bridgeCLE`, `composeFold_bridge_eq`, the cancellation lemmas)
and the per-role CLE engine (`RouteMRoleCLE`: `paramsBlockSplitCLE` &c.) are decoder-AGNOSTIC — they
operate on `Params M` / `chartIdxEquiv` and transfer to any revised decoder. The factor det bricks
(`schurChartFactor`/`lduChartFactor`/`chainVarMap`/`radialFactor` + their dets), `phiTarget_abs_det_of_
factored`, and the rate `routeMCore_phiFlatStructV` all survive. The Q3 funext-s technique
(`chainA_apply_castAdd` row-alignment) is validated as the (c) method — to be applied once the decoder is
fixed.

### Recommendation
Decorrelate the decoder fix (pen-and-paper / Codex): the precise question is "redefine `genBlkFlatStruct`
+ `structPivot` so the radial blow-up is encoded (fixed-`1` residual slot + nonzero `Rfin`), keeping the
decoder-agnostic rate `routeMCore_phiGen` interface (`hC0` re-checkable) — give the concrete `Rfin`/
`pRad`/E-slot redefinition + the `(2,2,2)` det-cross-check." Then (b)/(c)/(d) build against the fixed
decoder: radial `|u|^{minAdm−1}` + Schur/LDU spectators → `phiTarget_abs_det_of_factored` → `cov` →
`nodeChartGeneral (hpos)` → atom ∀M.

---

## UPDATE-12 (formalisation tide, 2026-06-27) — ∀M checkpoint (b): the (2,2,1) pattern does NOT generalize; the genuine wall sharply re-characterized (decorrelated: sympy + 2× xhigh Codex)

Charged checkpoint (b) (the ∀M `nodeChartGeneral`). The controller's brief assumed the banked
(2,2,1) pure-radial pattern generalizes (multi-boundary = "spectator handling"). **Decorrelated
verification (my sympy + two xhigh Codex consults, `codex/genM-chart-arch-*`, `codex/genM-rate-route-*`)
shows that framing is WRONG, and re-sharpens the wall.** All findings banked sorry-free in the
inventory below; NO speculative Lean written (heeding UPDATE-11's lesson: do not funext-s against the
wrong target).

### FINDING 1 — pure radial FAILS the RATE on split-codim nodes (not just the det)
The (2,2,1)/(4,4,2,2) charts are pure-radial because their achiever path drops rank at ONE boundary.
For a split-codim node (rank dropped at ≥2 boundaries) a pure radial blow-up of the residual blocks
does NOT give `prod = u·H`: the surviving-frame × downstream term `[a;c]·β·S` is **order-0 in u**
(uncancelled), so `F` is not even divisible by `u`. Verified exact (sympy `/tmp`): the naive dense
radial (3,3,4) chart has 12/12 product entries with an O(1) part; the cert-faithful Schur chart has
0/12. Codex Q1 (independent) gives the same obstruction: "the split-incidence condition — the
downstream matrix must vanish on the image frame of the upstream rank part." **The Schur / `b=aβ`
coupling (`T_next = u·Γ − β·S`) is LOAD-BEARING for the rate, uniformly ∀M, not a per-case artifact.**

### FINDING 2 (gating) — the vanishing order is EXACTLY u^1 across multiple Schur boundaries
Settled (Codex Q2 + the BANKED `chain_telescope`): a single global pivot `u` gives order EXACTLY 1
even with rank drops at several boundaries — the cancellations telescope through `D_{k+1}=D_k·B_k`.
The clean prefix invariant is `P_k = D_k·C_k + u·G_k` (NOT "u-divisible after the first drop", which
is false), terminal `C_L = u·R` ⟹ `P_L = u·(D_L·R + G_L)`. **This is the forward form of the
already-banked SUFFIX telescope `RouteMAchieverTelescope.chain_telescope` (`C_s·suffix_s = u·H_s`).**
So the single-global-pivot design HOLDS; per-boundary independent pivots are NOT needed. The achiever
minimizer T* genuinely spreads drops in general — (3,3,3,3)'s UNIQUE minimizer T*=(2,1,0) drops at
ALL 3 boundaries (`/tmp` minimizer scan) — so multi-boundary coupling is unavoidable, but order stays 1.

### FINDING 3 — the RATE ∀M is ALREADY BANKED; the wall is purely the DET-side bridge
`routeMCore_phiFlatStructV M t ha = (x p)²·V` is banked ∀M (consumes only `GenBlk`/`hle`/`hC0`, proven
via `chain_telescope`). The genuine charts (221/4422/334) re-derive the rate per-case (`dlnLoss_chartParams*`,
0 uses of the banked theorem), but the banked theorem covers `phiFlatStructV` ∀M. The DET of
`phiFlatStructV` is identically ZERO (UPDATE-11's D1: dead slots), so the det needs a DIFFERENT,
factored chart `φ_det`. **The wall = relate `φ_det`'s loss to the banked rate** (the
`composeFold fs = φ` map-equality, UPDATE-11's wall), OR re-derive the rate on `φ_det` (Route 2a,
duplicates the telescope + reopens dependent-width casts — Codex ranks it higher-risk).

### FINDING 4 — Codex Q4 DISSOLVES the controller's "hardest brick #1" (the e_M bijection)
The charged brick #1 (build `e_M : Fin N ≃ FlatIdx M` placing the T* blocks) is NOT needed. Keep the
CANONICAL `FlatIdx` order (pack = trivial, det 1 by construction), and put all slot selection into a
DECIDABLE `active : Finset (Fin (routeMAmbient M))` (a `Finset.filter` on the decoded FlatIdx for the
T*-residual slots). `pivotBlowupOn active p` needs only `active.card`, NOT contiguity. So the
dependent-width bijection engineering EVAPORATES — there is no Equiv to build, no left/right_inv over
opaque widths. (This is a strict improvement over the brief's plan.)

### THE SHARP SUB-PROBLEM (for the controller — design adjudication, routes to decoder-fix)
The remaining wall is a DESIGN decision, not a tactic: **on which decoder API do the RATE chart
(`phiFlatStructV`, banked rate, det 0) and the DET chart (`φ_det = Q ∘ radial ∘ Schur/LDU factors`,
genuine det, rate TBD) get UNIFIED, so the bridge `routeMCore(φ_det u) = (u_p)²·U` is a structural
`funext` over SHARED accessors rather than "permutation archaeology" (Codex's phrase)?** Two sub-routes:
- **2b (bridge):** prove `φ_det = phiFlatStructV` (or their GenBlk-decodings agree) over opaque
  Text/Wext widths — the chartIdxEquiv K/X/N/E role-slot ↔ raw Params layer-layout alignment, funext-s.
  This is UPDATE-11's precise wall; the brick-(a) `bridgeCLE`/`paramsBlockSplitCLE` engine (banked)
  was built to absorb exactly this, but the funext-s never landed.
- **2a (re-derive):** define `φ_det` directly, prove `dlnLoss(φ_det) = u²·U` by prefix induction with
  invariant `P_k = D_k·C_k + u·G_k` (FINDING 2) — abstractly via a FORWARD `chain_telescope` variant
  (Codex: "prove this abstractly once, not entrywise"). Sidesteps the bridge entirely but reopens the
  dependent-width Schur-block construction (`chartParamsGeneral`'s per-layer matrices over opaque widths).

**Recommendation:** decorrelate the decoder-API-unification decision (decoder-fix / Codex), exactly as
the cert's option-(C) verdict was reached. The math is fully settled (order-1, uniform Schur, no e_M);
the open part is purely "which Lean decoder API makes the det-chart↔rate bridge a clean funext." This
is above a leaf-executor's scope (it picks the target the whole next tide funext-s against). Banked,
decorrelated, sharp — handed back rather than charged blind (the UPDATE-11 mistake).

### Banked artifacts (this tide)
- `codex/genM-chart-arch-{prompt,answer}.md` — architecture verdict (Q1 pure-radial fails / Q2 order-1
  / Q3 hybrid B+Q4 / Q4 keep-FlatIdx-order). xhigh, decorrelated.
- `codex/genM-rate-route-{prompt,answer}.md` — the rate-route verdict (the `P_k = D_k C_k + u G_k`
  invariant; 2b lower-risk; the sharp bridge sub-lemma). xhigh, decorrelated.
- The (2,2,1) validate-small (`RouteM221.lean`) remains banked + INTEGRATED (controller `6fb2e15d`).
