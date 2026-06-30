# Statement card — `{eIn + hD}` coupled tide (genm-eihd2 → genm-eihd2-cont): FULLY CLOSED (all 3 J-blocks landed)

**Status (UPDATE 2026-06-30, genm-eihd2-cont):** COMPLETE. All three J-blocks (`eihdT_J00`/`eihdT_J01`/
`eihdT_J11`) are PROVEN sorry-free; `RouteMHDtotEihd.lean` has ZERO sorries; green build (8349 jobs).
`#print axioms` clean-three `[propext, Classical.choice, Quot.sound]` (S2-free) on all five:
`eihdT_J00`, `eihdT_J01`, `eihdT_J11`, `eihd_hD`, `interiorDet_leaf_headline_eihd`. So the gate
discharges `hreg` only (banked) → the ∀M-L2 interior-det `|det Dφ|` headline holds (the R1-LOWER
`cover_ge_div` / NodeAchieverChart-cov dependency). Two new imports added to the module:
`RouteMReaderFDeriv`, `RouteMChainFDerivValue`.

**Branch:** `expedition/genm-eihd2-cont` (off `origin/expedition/genm-eihd2` @ `1e3ef016`). The
controller cone-merges the whole eihd chain.

## The closing route (genm-eihd2-cont — banked, sorry-free)

All three J-blocks reduce via Bridge 1 (`eihdT w = packStair (fderiv BparamsLeaf y₀ (eIn.symm w))`) +
the `rfl` facts `(packStair p).1 = packLayer0 (p 0)`, `(packStair p).2.1 = packLayer1 (p 1)`, +
Bridge 2a (`fderiv BparamsLeaf y₀ w s = fderiv (fun z => BparamsLeaf z s) y₀ w`).

- **J00 / J01 (V0 line):** `fun z => BparamsLeaf ha z 0` reindexes (`reindexL0_BparamsLeaf0`, via the
  banked `BparamsLeaf_layer0_entry`) to the gate `layer0SchurMap`; its fderiv collapses
  (`flatBlockLE_symm_fderiv_flatBlock` + `gate_schurCore_eq`) to `schurFrameDeriv X K N (fderiv
  slotReadV0 ·)`. `slotReadV0` is linear (`slotReadV0_fderiv_apply`, via a prod of `matrixReaderCLM`),
  and `slotReadV0 (eIn.symm w) = w.1` (the inverse of `eIn_projV0`). So J00 reads `v0`, J01 reads `0`
  (`map_zero`).
- **J11 (V1 line):** `fun z => BparamsLeaf ha z 1` reindexes (`reindexL1_BparamsLeaf1`) to
  `chainA(Nblk 1, Wblk 1, Cgen 2)` with `Nblk 1 = readN ⟨0⟩` (a V0-frame slot), `Wblk 1 = readW ⟨0⟩`,
  `Cgen 2 = rfinDirect`. `packLayer1 = prodComm ∘ rowSplitLE ∘ reindexL1`; `rowSplitLE` of a `chainA`
  is `(C − N·W, W)` (`rowSplitLE_chainA`, the `chainA_apply_castAdd/_natAdd` block laws, aligning
  `finSumFinEquiv` with `finSplit`). The chain map fderiv is built from the matrix readers
  (`chainKL_hasFDerivAt`); pushed through `rsL1 = rowSplitLE ∘ reindexL1` (concrete Matrix codomain — has
  topology, unlike the `eihdV M 1`-valued `packLayer1`); the `prodComm` swap is `rfl`-defeq at the end.
  At `d = eIn.symm (0,(v1,()))`: `dN d = (slotReadV0 d).2.1 = 0` (V0 zeroed), `dW d = v1.1`,
  `dC d = v1.2` (the inverse of `(eIn δ).2.1 = (wToMat W-read, leafToMat leaf-read)`). Lands on
  `chainUnitMap (readN ⟨0⟩) v1 = (v1.1, v1.2 − N·v1.1)`.

New reusable in-module infra (all sorry-free): `reindexL0`, `reindexL0_BparamsLeaf0`,
`BparamsLeaf0_hasFDerivAt`, `reindexL0_fderiv`, `packLayer0_layer0_fderiv_eq`,
`layer0SchurMap_fderiv_collapse`, `readK/N/X/E_idx`, `slotReadV0_hasFDerivAt'`, `slotReadV0_fderiv_apply`,
`packLayer0_layer0_fderiv` (V0); `reindexL1`, `packLayer1_eq`, `reindexL1_BparamsLeaf1`,
`readN0/W0_idx`, `leaf_idx`, `Nblk1_eq`, `Wblk1_eq`, `Cgen2_eq`, `rowSplitLE_chainA`,
`BparamsLeaf1_hasFDerivAt`, `Wfun/Lfun/Nfun`, `rsL1`, `rsL1_BparamsLeaf1`, `chainKL_hasFDerivAt`,
`rsL1_fderiv`, `dWdC_eq_eInV1`, `packLayer1_fderiv` (V1).

---

## (original card, genm-eihd2 — architecture + eIn_projV0)

**Branch:** `origin/expedition/genm-eihd2` (off `origin/genm-eihd`). SHA `5d596c4a`.

## `eIn_projV0` LANDED (the faithfulness validation — controller's #1 priority)
`eIn_projV0 : (eIn ha δ).1 = slotReadV0 ha δ` is PROVEN, axiom-clean `[propext, Classical.choice,
Quot.sound]`. The combinator-eval tooling that unblocked it (reusable for the J-blocks):
- `flatMatLE_apply : flatMatLE a b f i j = f (finProdFinEquiv (i,j))` — `unfold flatMatLE; simp only
  [LinearEquiv.trans_apply]; rfl` (NOT `:= rfl`; there is NO `LinearEquiv.curry_apply`).
- `frameToSchurInc_blocks` — the 4 `SchurInc` blocks read `g` at `frameSplitEquiv.symm` role indices
  (K@`inl inl inl`, N@`inl inr`, X@`inl inl inr`, E@`inr`): `have hr : frameToSchurInc ha g = roleReorderLE
  M (…) := rfl`, then per-block `show flatMatLE _ _ _ i j = _; rw [flatMatLE_apply]; simp [trans_apply,
  prodCongr_apply, refl_apply, sumArrow…_apply_fst/_snd, funCongrLeft_apply, funLeft_apply, of_apply]`.
- `eIn_projV0` itself: `(eIn δ).1 = frameToSchurInc ha (fun a => δ (chartIdxEquiv.symm ⟨0, inl a⟩))` is
  `rfl`; then `rw [frameToSchurInc_blocks]; rfl` (the block-tuple matches `slotReadV0 = (readK, readN,
  readX, readE)` index-for-index).

## J-block residual (J00/J01/J11 — the genuine `fderiv-BparamsLeaf` multi-tide)

**Bridge 1 LANDED** (`eihdT_eq_packStair_fderiv`, SHA `d959df9c`, sorry-free): the flatten/unflatten
cancel — `eihdT w = packStair (fderiv BparamsLeaf y₀ (eIn.symm w))`. Collapses `Dtot`/`eihdOut`'s
`paramsEquivFlat` round-trip, reducing ALL THREE J-blocks to facts about the `Params`-valued
`fderiv BparamsLeaf y₀` applied at `eIn.symm w`, then `packStair`-projected:
- J00: `(packStair ha (fderiv BparamsLeaf y₀ (eIn.symm (v0,(0,()))))).1 = schurFrameDeriv X K N v0`.
- J01: `(packStair ha (fderiv BparamsLeaf y₀ (eIn.symm (0,(v1,()))))).1 = 0`.
- J11: `(packStair ha (fderiv BparamsLeaf y₀ (eIn.symm (0,(v1,()))))).2.1 = chainUnitMap (readN ⟨0⟩) v1`.

**Bridge 2a LANDED** (`BparamsLeaf_fderiv_layer`, SHA `4e31b551`, sorry-free): the per-layer component
`(fderiv BparamsLeaf y₀ w) s = fderiv (fun z => BparamsLeaf z s) y₀ w` (eval-at-`s` proj CLM through
`fderiv`). Isolates each chart layer for the per-layer atoms.

**Remaining (NOT yet banked — the work; every sub-piece confirmed TRACTABLE in scratch, no new math):**
- **Bridge 2 (rest)** — the per-layer fderiv VALUE. (a) live-decoder block fderiv VALUES: `readK/N/X/E/W`
  as matrix-valued maps of `y` are differentiable by `differentiableAt_pi.mpr + differentiableAt_apply`
  (CONFIRMED in scratch — same pattern as banked `slotReadV0_hasFDerivAt`); their fderiv is the constant
  read CLM. (b) feed those into banked `hasFDerivAt_Agen_interior`/`hasFDerivAt_Cgen_interior`
  (`RouteMAgenFDerivValue`, GENERIC in `dB/dN/dR/dW/du`) → layer-0/layer-1 `Agen` fderiv value.
  (c) the `chartParamsGen = reindex (Agen …)` outer `reindex` (use `Matrix.reindex` fderiv = reindex of
  fderiv, linear). Combine with Bridge 2a → `fderiv BparamsLeaf y₀` layer-`s` value explicitly.
- **Bridge 3** — `eIn.symm (v0,(0,()))` / `(0,(v1,()))` explicit (the `.symm` direction; reuse the
  combinator-eval recipe — `flatMatLE_apply`-style — on `eInRearrange.symm`/reshape `.symm`s/`funCongrLeft
  chartIdxEquiv.symm |>.symm`; the anonymous-ofLinear `invFun`s unfold via `rfl`/`show` as the forward did);
  `slotReadV0 (eIn.symm (v0,(0,()))) = v0` (the inverse of `eIn_projV0`); `packStair` projects layer-0 → V0
  via `packLayer0 = flatBlockLE.symm` (banked `flatBlockLE_symm_fderiv_flatBlock` normalization).
Then the 3 discharges: J00 (banked Schur core `gate_schurCore_eq` + `schurFrameDeriv`), J01 (=0: layer-0
`Agen` indep of the V1/chain coords after the `eIn.symm` write), J11 (chainUnit via `chainAFDeriv` +
`packLayer1` W/C reorder). Genuine multi-tide (Bridge 2 ≈ one focused build, Bridge 3 + discharges ≈ another).

**Prior SHAs:** `bd9081f2` (skeleton), `f70b8f8c` (eIn_projV0), `d959df9c` (Bridge 1).
**Module:** `lean/DLNFibre/DLN/RLCT/Validate/RouteMHDtotEihd.lean` (546 LoC). Single-writer; NOT wired into
`DLNFibre.lean` (controller cone-merges).

## DONE this tide (sorry-free)

- **`eihd_hD`** — the block identity `eihdOut ∘ Dtot ∘ eIn.symm = stairMap V 2 f c`, assembled (Codex
  option (c)) from the three block facts (`eihdT_J00`/`eihdT_J01`/`eihdT_J11`) with the coupling `eihdc`
  DEFINED from the actual off-diagonal block of `T` (`c.1 = snd ∘ T ∘ inclV0`, a `LinearMap` composite —
  linearity automatic; never separately identified, det-invisible). `LinearMap.ext` over `StairProd V 2 =
  V0 × (V1 × PUnit)` + `map_add` split + the explicit `stairMap`/`lowerTri` reduction. **This is the
  in-Lean faithfulness gate** — a misaligned `eIn` fails the {J00, J01, J11} step. (Reviewer + decorrelated
  Codex confirmed GENUINE, not vacuous: the coupling absorbs ONLY the det-invisible lower-left V0→V1 block;
  the V0-line forces J00 (`= f0 v0`) and J01 (`= 0`), and the V1-line still requires J11 to rewrite
  `(eihdT (0,(v1,()))).2.1` to the fixed `eihdF 1 v1` — all three fail `rfl`, so none is trivially true.)
- **`eihdc`** — the coupling as `(LinearMap.snd …).comp (eihdT … ).comp eihdInclV0`.
- **`eIn`** — a GENUINE `LinearEquiv (Fin (flatDim M) → ℝ) ≃ₗ StairProd (eihdV M) 2`, built (Option A,
  Codex-endorsed) as the composite
  `funCongrLeft chartIdxEquiv.symm ≫ piCurry (Σ→Π) ≫ piFinTwo ≫ slotSplitLE ≫
   ((frameToSchurInc × wToMat) × (leafToMat × leafLiftToPUnit)) ≫ eInRearrange`.
  Supporting reshapes all sorry-free: `roleReorderLE` (the `(((K⊕X)⊕N)⊕E) → (K,N,X,E)` reorder),
  `frameToSchurInc` (V0 via `frameSplitEquiv`), `wToMat` (W lift via `liftSlotEquiv`), `leafToMat` (leaf
  via `flatMatLE`), `leafLiftToPUnit` (empty `liftDim 1 = 0`), `slotSplitLE`, `prodMatLE`, `eInRearrange`.
- **`interiorDet_leaf_headline_eihd`** — the gate; now closes with ONLY `hreg` external (the regauge
  abs-det-`1`, discharged by the banked `hreg_of_measurePreserving_comp`).
- The dimension decomposition (verified): `V0 ← schurDim 0` (boundary-0 frame, `Text1·Wext1`);
  `V1 = (W, leaf)` with `W ← liftDim 0` (boundary-0 lift, `(Wext1−Text2)·Wext2`) and `leaf ← schurDim 1`
  (boundary-1 frame, `Text2·Wext2`); `liftDim 1 = 0` (empty). Sums to `flatDim`.

## RESIDUAL — 4 documented sorries

### (1) `eIn_projV0 : (eIn ha δ).1 = slotReadV0 ha δ` — the single hard reindex-match (Codex-flagged)
`eIn` is built, so this is the lone faithfulness lemma. `(eIn δ).1` reduces (the slot-0 frame factor) to
`frameToSchurInc` applied to `a ↦ δ (chartIdxEquiv.symm ⟨0, Sum.inl a⟩)`. Prove componentwise on the 4
`SchurInc` blocks (K, N, X, E) — each matching `frameToSchurInc`'s `roleReorderLE`+`flatMatLE` against the
reader `readK/N/X/E … ⟨0⟩` (both read `δ (chartIdxEquiv.symm ⟨0, Sum.inl (frameSplitEquiv.symm (…))⟩)`).
**The friction:** the blocks have DIFFERENT widths (K is t2×t2, N is t2×c1, X is r1×t2, E is r1×c1), so a
single `<;>`-shared simp set type-mismatches; handle per-block. The `sumArrowLequivProdArrow_apply_fst /
piCurry_apply (= Sigma.curry) / piFinTwo_apply / funCongrLeft_apply (= LinearMap.funLeft_apply)` chain
fires, but through opaque-Fin-width slot casts (the lean/CLAUDE.md matrix-apply-no-progress quirk). A
useful sub-lemma to land first: `eIn_frameRead` (the slot-0 frame read collapses to
`δ (chartIdxEquiv.symm ⟨0, Sum.inl a⟩)`); the simp set above + `rfl` closes it once the statement
parenthesization is right (the `(sumArrow (...)).1).1 a` nesting + `piFinTwo`'s slot-0 projection).

**WORKING COMBINATOR-EVAL RECIPE (verified in scratch, the unblock):**
- `flatMatLE_apply : flatMatLE a b f i j = f (finProdFinEquiv (i,j))` — proved by
  `unfold flatMatLE; simp only [LinearEquiv.trans_apply]; rfl` (NOT `:= rfl`; and there is NO
  `LinearEquiv.curry_apply` lemma — the `simp [trans_apply]; rfl` route handles `curry`+`ofLinearEquiv`).
- `frameToSchurInc` block-reduction: `simp only [LinearEquiv.trans_apply]` does NOT fire when the goal is
  `(frameToSchurInc ha g).1 i j = …` (the `.1 i j` projections sit between the equiv coercion and the
  entry, blocking the rewrite). Peel with a `show`/`change` of the FULL tuple equality
  `frameToSchurInc ha g = (Matrix.of …, …, …, …)` first (`rw [frameToSchurInc]` then the trans/prodCongr/
  `roleReorderLE.toFun` reduce — `roleReorderLE` is an anonymous `where`-`LinearEquiv`, so `show` its
  `toFun` p-form directly rather than relying on `LinearEquiv.coe_mk`), THEN go entrywise. Same pattern for
  the `eIn` slot-0 reduction (`hg : (eIn δ).1 = frameToSchurInc ha (fun a => δ (chartIdxEquiv.symm ⟨0,inl a⟩))`).
- The J-blocks (2)-(4) are STRICTLY HARDER than `eIn_projV0`: each needs `eIn.symm` reduction (same
  combinator friction) PLUS the `fderiv BparamsLeaf` computation. Build the eval tooling +
  `eIn_projV0` FIRST (validates eIn), then the J-blocks reuse it.

### (2)-(4) `eihdT_J00` / `eihdT_J01` / `eihdT_J11` — the block facts
Each computes `eihdT (v0,(0,())).i` or `(0,(v1,())).i` where `eihdT = eihdOut ∘ Dtot ∘ eIn.symm`. Route
(Codex): `eIn.symm (v0,(0,()))` writes the V0 (frame) data back through `chartIdxEquiv.symm`; `Dtot`
(= `paramsEquivFlatCLE ∘ fderiv BparamsLeaf`) reads it through the SAME `chartIdxEquiv`-based readers, so
reader∘`eIn.symm` collapses by `Equiv.apply_symm_apply`. Then:
- **J00** (`eihdT (v0,(0,())).1 = schurFrameDeriv X K N v0`): the V0→V0 block is the banked
  `layer0SchurMap_hasFDerivAt`/`gate_schurCore_eq` (`RouteMProjV0Gate`) + `flatBlockLE_symm_fderiv_flatBlock`
  (the J00 normalization, banked in-module). **The faithfulness gate.**
- **J01** (`eihdT (0,(v1,())).1 = 0`): the layer-1 (chain) coords don't feed the layer-0 (frame) Schur
  output. Needs that `Agen 0` (the layer-0 chart block) is independent of the V1 coords, after the
  `eIn.symm` write.
- **J11** (`eihdT (0,(v1,())).2.1 = chainUnitMap (readN ⟨0⟩) v1`): the V1→V1 block is the layer-1 chaining
  `(W, C) ↦ (W, C − N·W)` via the banked `hasFDerivAt_chainA` + `packLayer1`'s (W=lift, C=kept) reorder.

**Scale:** the J-blocks need the full `fderiv BparamsLeaf` per-layer assembly matched through `eIn.symm`
and `packStair`; a genuine multi-tide on top of (1). Build (1) first (it validates `eIn`); then J00 (the
gate, banked atoms available); then J01/J11.

## Close criterion
All four filled → `interiorDet_leaf_headline_eihd` discharges `hreg` only (banked) → the ∀M-L2 interior-det
`|det Dφ|` headline holds ∀M at L=2. `#print axioms` must be clean-three (S2-free; feeds the R1-LOWER
`cover_ge_div` leg).
