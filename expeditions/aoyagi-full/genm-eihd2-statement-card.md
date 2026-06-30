# Statement card — `{eIn + hD}` coupled tide (genm-eihd2): architecture + `eIn` DONE, 4-sorry residual

**Status:** architecture validated end-to-end (green build, 8347 jobs); `eIn` built sorry-free; the
coupling proof `eihd_hD` and the gate `interiorDet_leaf_headline_eihd` DONE. Four documented term-level
sorries remain (the faithfulness gate + the J-blocks). No `axiom`/`native_decide`/`#exit`.

**Branch:** `origin/expedition/genm-eihd2` (off `origin/genm-eihd`). SHA `bd9081f2`.
**Module:** `lean/DLNFibre/DLN/RLCT/Validate/RouteMHDtotEihd.lean` (546 LoC). Single-writer; NOT wired into
`DLNFibre.lean` (controller cone-merges).

## DONE this tide (sorry-free)

- **`eihd_hD`** — the block identity `eihdOut ∘ Dtot ∘ eIn.symm = stairMap V 2 f c`, assembled (Codex
  option (c)) from the three block facts (`eihdT_J00`/`eihdT_J01`/`eihdT_J11`) with the coupling `eihdc`
  DEFINED from the actual off-diagonal block of `T` (`c.1 = snd ∘ T ∘ inclV0`, a `LinearMap` composite —
  linearity automatic; never separately identified, det-invisible). `LinearMap.ext` over `StairProd V 2 =
  V0 × (V1 × PUnit)` + `map_add` split + the explicit `stairMap`/`lowerTri` reduction. **This is the
  in-Lean faithfulness gate** — a misaligned `eIn` fails the J00/J01 step.
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
