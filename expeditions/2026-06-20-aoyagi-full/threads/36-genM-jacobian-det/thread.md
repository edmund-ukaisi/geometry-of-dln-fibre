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

## UPDATE-6 (same tide cont.) — Codex REFRAME: the det needs NO map-equality; phiFlat_abs_det = factor-list + leafH summation

Decorrelated xhigh Codex (`codex/item3-form-*`) reframed item-3 decisively. **DEFINE the achiever chart
AS `composeFold fs`.** Then `phiFlat_abs_det` is IMMEDIATE from the banked telescope — the map equality
is needed ONLY to transfer the RATE (which I already have for `phiFlatStruct`), NOT for the determinant.
Route a-prime (direct layer-wise fderiv of `chartParamsGen ∘ genBlkFlatStruct`) REJECTED — it rebuilds
the Schur/LDU/chain det proof in one large derivative, duplicating the factor machinery.

Banked: **`composeFold_abs_det_leafH`** (`RouteMPhiFlatDet`) — `|det (fderiv (composeFold fs) u)| =
∏_j |u_j|^{leafH j}` from `composeFold_hasFDerivAt` + `composeFold_abs_det` + the item-4 det
bookkeeping `hdet`. NO map equality. This is the genuine `phiFlat_abs_det` for `phiFlat := composeFold fs`.

### So `phiFlat_abs_det` now needs ONLY: the factor list `fs` + the leafH summation `hdet`
1. **The factor list `fs`** (outer→inner: chain_s, Schur_s, LDU_s, radial): each from the item-2
   `conjBlockFactor` with a CLE `E_s : (Fin N → ℝ) ≃L Block_s × Rest` built by
   `flatToChartIdx` (DONE) + a `ChartIdx ≃ slot_k ⊕ rest` split (`sumPiEquivProdPi`) + the
   `(Fin schurDim → ℝ) ≃L SchurInc`/`LDUParam` block flattening. The remaining build-complexity: the
   per-boundary `ChartIdx ≃ slot_k ⊕ rest` decomposition (the "rest" subtype + the equiv).
2. **The leafH summation `hdet`**: the per-factor monomials (`radial |u_p|^{minAdm−1}`, Schur
   `|K_s(prefix)|^{r_s+c_s}`, LDU `∏|q(prefix)|^{2(t−1−i)}`, chain `1`) multiply to `∏|u_j|^{leafH j}`.
   The prefix-pullback wrinkle: each factor's det is read at its prefix `composeFold(tail) u`; since the
   factors read DISJOINT slots (the structured decoder's guarantee), the prefix doesn't disturb a
   factor's own block — so `det_s = monomial in u's own slot` (a `prefix_s u`'s block = `u`'s block, by
   slot-disjointness). Then the leafH product is the `leafH3333_prod_eq`-pattern `Finset.prod` over
   `{radial} ∪ {Schur/LDU slots}`.

This is the REMAINING build — substantial (the CLEs + the disjoint-prefix det bookkeeping) but with NO
deep map-equality induction. The det side is otherwise COMPLETE (9 modules banked: workhorse, fderiv
infra, factors, slots, decoder, rate, det-skeleton, map-free det). The rate (for the atom) would later
use the bridge `composeFold fs = phiFlatStruct` — deferred (not needed for `phiFlat_abs_det`).
