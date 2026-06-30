# Statement card — `{eIn + hD}` coupled tide (genm-eihd2): architecture + `eIn` + `eIn_projV0` DONE, 3-sorry residual

**Status:** architecture validated end-to-end (green build, 8347 jobs); `eIn` built sorry-free AND
VALIDATED FAITHFUL (`eIn_projV0` PROVEN clean-three — the green-but-wrong tripwire is cleared); the
coupling proof `eihd_hD` and the gate `interiorDet_leaf_headline_eihd` DONE. THREE documented term-level
sorries remain (the J-blocks J00/J01/J11). No `axiom`/`native_decide`/`#exit`.

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

**Remaining bridges (NOT yet banked — the work):**
2. A per-LAYER `HasFDerivAt` VALUE of `BparamsLeaf` (`chartParamsGen = fun s => reindex (Agen 1 … s)`):
   layer 0 `= reindex (fderiv layer0SchurMap)` (banked `layer0SchurMap_hasFDerivAt` → factors through
   `schurFrameDeriv ∘ slotReadV0D`); layer 1 `= reindex (chainAFDeriv …)` (banked `hasFDerivAt_chainA`).
   Extract the layer-`s` component of the single `Params`-valued `fderiv` via `fderiv_pi`/`hasFDerivAt_pi''`.
3. `eIn.symm (v0,(0,()))` / `eIn.symm (0,(v1,()))` explicit (the harder `.symm` direction — reuse the
   combinator recipe on `eInRearrange.symm`/reshape `.symm`s/`funCongrLeft chartIdxEquiv.symm |>.symm`);
   `slotReadV0D ∘ eIn.symm` = the V0-projection; `packStair` projects layer-0 → V0 via
   `packLayer0 = flatBlockLE.symm` (banked `flatBlockLE_symm_fderiv_flatBlock` normalization).
Then J00 (banked Schur core), J01 (=0: layer-0 indep of V1), J11 (chainUnit via `chainAFDeriv` +
`packLayer1` W/C reorder). Genuine multi-tide: build Bridge 2 + Bridge 3, then the three discharges.

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
