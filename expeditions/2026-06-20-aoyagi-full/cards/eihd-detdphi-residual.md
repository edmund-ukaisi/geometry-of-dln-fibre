# Statement card — ∀M-L2 `|det Dφ|` residual: the coupled `{eIn + hD}` tide

**Status:** residual of the ∀M-L2 interior-det headline (the R1-LOWER leg's `|det Dφ|` dependency).
Authored by the controller from genm-eihd's hand-off report (genm-eihd is off-team after compaction;
work banked on `origin/genm-eihd`). The fresh tide builds `{eIn + hD}` off that branch.

## Where the banked bedrock lives
Module: `lean/DLNFibre/DLN/RLCT/Validate/RouteMHDtotEihd.lean` on `origin/genm-eihd` (0-sorry,
clean-three `[propext, Classical.choice, Quot.sound]`, controller-verified via `git show`). NOT wired
into `DLNFibre.lean` (the controller cone-merges once the residual closes).

## BANKED (sorry-free clean-three — reuse, do not rebuild)
- `eihdV` (V0 = `SchurInc(Text2, Text1−Text2, Wext1−Text2)`, V1 = `(W, leaf)` chain pair, `PUnit` else),
  `eihdF` (f0 = `schurFrameDeriv` read@pbo, f1 = `chainUnitMap (readN ⟨0⟩)`), `eihdc`.
- `eihdF0_abs_det` (= `|det K|^(r+c)` via `schurFrameDeriv_det`), `eihdF1_abs_det` (= 1). Both block dets PROVEN.
- **J00 de-risk CLOSED:** `flatBlockLE_symm_fderiv_flatBlock` (`flatBlockLE.symm ∘ fderiv flatBlock = id`)
  + `fderiv_flatBlock_eq` — collapses the gate's `flatBlockD` factor to `schurFrameDeriv`. The flagged
  genuine-risk spot.
- **The ENTIRE OUTPUT LEG:** `eihdOut := packStair ∘ paramsEquivFlatLinear.symm` (a genuine `LinearEquiv`),
  from `packLayer0` (`Matrix(M0,M1) ≃ SchurInc` via `flatBlockLE.symm`) + `packLayer1`
  (`Matrix(M1,M2) ≃ (W,leaf)` via `rowSplitLE + prodComm`). All width facts proven
  (`M0=Text1, M1=Wext1, M2=Wext2`, schur splits). **V1-orientation trap handled STRUCTURALLY: (W=lift, C=kept).**
- **The COHERENCE GATE** `interiorDet_leaf_headline_eihd` (line 247): the ∀M-L2 interior-det headline
  follows from EXACTLY the residual `{eIn, c, hD, hreg}` via the wrapper consuming all the banked pieces.
  Architecture sound end-to-end.

## RESIDUAL — two coupled pieces (build them TOGETHER, one tide)

### (1) `eIn` — the reader-slot-faithful input `LinearEquiv`
Target: a `LinearEquiv` with `(eIn δ).1 = slotReadV0 δ`. It must reproduce, as a provable equiv, the
reindex chain: `chartIdxEquiv` + `frameSplitEquiv` + `finProdFinEquiv` + the `K,X,N,E → K,N,X,E` reorder
+ `liftSlotEquiv` + `leafSlot`. This is the obstruction-#3 slot-zone machinery / the (2,2,2) `slotList`
(1283-LoC literal) generalized to **opaque width**.

### (2) `hD` — `eihdOut ∘ Dtot ∘ eIn.symm = stairMap eihdV 2 eihdF c`
Needs the full `fderiv-BparamsLeaf` per-layer CLM assembly (NOT yet banked — only the generic per-layer
atoms `hasFDerivAt_Agen` / `hasFDerivAt_chainA` + the layer-0 gate exist). The 3 blocks
(J00 = `schurFrameDeriv` via the now-banked normalization, J01 = 0, J11 = `chainUnit`) must be matched
through `eIn.symm` / `packStair`.

## ⚠ Discipline — why eIn cannot be built solo
`eIn` is THE place a green-but-wrong reindex hides. **`hreg` will NOT catch a misaligned `eIn`** (Codex
xhigh, artefact `expeditions/aoyagi-full/codex/eihd-trio-answer.md`). **Only `hD`'s J00/J01=0 match
catches it.** So the J00/J01=0 step IS the in-Lean faithfulness gate for `eIn` — building/banking `eIn`
without `hD` risks a wrong foundation that compiles green. Build the two together; let `hD` validate `eIn`.

## Close criterion
`eIn` + `hD` filled → `interiorDet_leaf_headline_eihd` discharges its `{eIn, hD}` inputs (with `c` from
`eihdc` and `hreg` the regularity hyp) → the ∀M-L2 interior-det `|det Dφ|` headline holds ∀M at L=2.
`#print axioms` clean-three (the leaf headline is S2-free; it feeds the R1-LOWER `cover_ge_div` leg).
Push the branch, report the SHAs + axiom lists, stand down at the clean boundary; controller cone-merges.
