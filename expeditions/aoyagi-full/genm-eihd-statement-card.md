# Statement card — the coupled `eIn`/`eihdOut`/`hD` `hDtot` tide: V/f/c + output leg + coherence (`genm-eihd`)

Off the bedrock tip `origin/genm-eineout`. The load-bearing geometric residual of `hDtot`, scoped and
PARTIALLY built. All landed results sorry-free, clean-three `[propext, Classical.choice, Quot.sound]`
(forced `#print axioms` per result), pushed `origin/genm-eihd`. NOT wired into `DLNFibre.lean`
(controller single-writer); additive, 0 sibling name clashes.

Module: `lean/DLNFibre/DLN/RLCT/Validate/RouteMHDtotEihd.lean`.

These convert the `hDtot` two-sided-staircase residual (`eIn`, `eihdOut`, `hD`, `hreg` feeding
`RouteMHDtotConj.hDtot_of_twoStairConj`) into a SHARPER residual: the boundary spaces `V`, the
diagonal blocks `f` (with both dets), and the ENTIRE OUTPUT equiv `eihdOut` are now banked; the
coherence gate proves the headline follows from EXACTLY `{eIn, c, hD, hreg}`.

## The design (numeric partition certificate, 6 random seeds at (3,3,4), EXACT)

* `V 0 = SchurInc (Text2) (Text1−Text2) (Wext1−Text2)` — the boundary-0 Schur frame increment
  (dim `schurDim 0 = Text1·Wext1`).
* `V 1 = Matrix(Wext1−Text2, Wext2) × Matrix(Text2, Wext2)` — the `(W, leaf)` chain layer.
* `f 0 = schurFrameDeriv X K N` (det `|det K|^(r+c)`), `f 1 = chainUnitMap (readN ⟨0⟩)` (det `1`).
* The shared `readN ⟨0⟩` couples the layer-0 frame to the layer-1 kept row `−N·W` (strictly
  head→tail, the det-invisible `c.1`).

## Banked (sorry-free, clean-three)

### Brick 1 — V/f/c + the two diagonal-block dets

* `eihdV` / `eihdF` — the boundary spaces and diagonal blocks (concrete, with their `AddCommGroup`/
  `Module`/`FiniteDimensional` instances).
* `eihdF0_abs_det` — `|det (eihdF … 0)| = |det K|^(r+c)` via the banked `schurFrame_abs_det`
  (`K = readK ⟨0⟩` at the blow-up point `= leafKcore`; the headline exponent
  `(Text1−Text2)+(Wext1−Text2)`).
* `eihdF1_abs_det` — `|det (eihdF … 1)| = 1` via the banked `chainUnit_det`.

### Brick 2 — the J00 de-risk (the lone flagged genuine-risk spot, CLOSED)

* `fderiv_flatBlock_eq` — `fderiv (flatBlock hr hc) z₀ = flatBlockLin hr hc` (the flatten is linear).
* `flatBlockLE_symm_fderiv_flatBlock` — `flatBlockLE.symm ∘ (fderiv flatBlock z₀) = id` on `SchurInc`.
  Collapses the gate's `flatBlockD` factor, so the gate's `layer0SchurMap` fderiv-core reduces to
  `schurFrameDeriv` (the J00 Schur core). Codex (xhigh) flagged J00 as the lone genuine-risk spot; the
  normalization closes cleanly (no new-math gap), confirming the bounded-plumbing verdict in practice.

### Brick 3 — the ENTIRE output leg `eihdOut`

* `flatMatLE a b` — `(Fin (a*b) → ℝ) ≃ₗ Matrix (Fin a) (Fin b) ℝ` (flat-slot ↔ matrix reshape).
* width facts: `eihd_M0_eq_Text1`, `eihd_M1_eq_Wext1`, `eihd_M2_eq_Wext2`, `eihd_schurR_split`
  (`schurT1+schurR1=Text1`), `eihd_schurC_split` (`schurT1+schurC1=Wext1`).
* `packLayer0` — `Matrix(M0,M1) ≃ₗ SchurInc` (dim-recast then `flatBlockLE.symm`).
* `rowSplitLE` / `packLayer1` — `Matrix(M1,M2) ≃ₗ (W, leaf)`. The ROW split `(kept, lift)` then SWAP to
  `(W=lift, C=kept)` — Codex's flagged V1-orientation trap (`chainUnitMap (W,C)` vs `chainA`
  kept-then-lift), handled STRUCTURALLY via `LinearEquiv.prodComm`.
* `packStair` — `Params M ≃ₗ StairProd (eihdV M) 2` (`piFinTwo` + the two layer reshapes + `prodUnique`).
* `eihdOut := packStair ∘ₗ paramsEquivFlatLinear.symm` — the output layer-collecting equiv. Absorbs the
  `paramsEquivFlat` flattening: `eihdOut ∘ paramsEquivFlatCLE = packStair`, so `hD` reduces to
  `packStair ∘ (fderiv BparamsLeaf) ∘ eIn.symm = stairMap`.

### Brick 4 — the coherence gate

* `interiorDet_leaf_headline_eihd` — the ∀M-L2 headline `|det Dφ| = |u p₀|^(minAdm−1) · ∏ engineFreeK`
  follows from EXACTLY the residual `{eIn, c, hD, hreg}` (the wrapper
  `interiorDet_leaf_headline_of_DtotConj` consuming the banked `eihdV`/`eihdF`/`eihdOut` + both block
  dets). Proves the architecture is sound end-to-end and pins precisely what the remaining tide needs.

## The precise residual (for the controller / next tide)

Two pieces, both genuine multi-tide-scale (NOT a 3-4-attempt fill — surfaced, not ground):

1. **`eIn`** : `(Fin (flatDim M) → ℝ) ≃ₗ StairProd (eihdV M) 2`, the reader-slot-FAITHFUL input equiv
   with the input invariant `(eIn δ).1 = slotReadV0 ha δ` (and V1 `= (readW ⟨0⟩, rfinDirect)`). It must
   reproduce the readers' slot allocation (`chartIdxEquiv` + `frameSplitEquiv` + `finProdFinEquiv` + the
   K,X,N,E→K,N,X,E reorder for `SchurInc`'s field order + `liftSlotEquiv` + `leafSlot`) as a PROVABLE
   equiv. This is the scoping's "obstruction #3" slot-zone machinery (the (2,2,2) `slotList`/
   `bdataSlotEquiv`, 1283 LoC literal) generalized to opaque width — where a green-but-wrong reindex
   hides (Codex: `hreg` will NOT catch it; only `hD`'s `J00`/`J01=0` will). Recommended construction:
   build through `funCongrLeft (chartIdxEquiv …).symm` + a structured `(ChartIdx → ℝ) ≃ StairProd`
   reshape (round-trips free from `chartIdxEquiv`'s bijectivity), then prove the input invariant
   SEPARATELY as the green-but-wrong check.

2. **`hD`** : `eihdOut ∘ Dtot ∘ eIn.symm = stairMap (eihdV M) 2 (eihdF …) c`. By Codex's verdict prove
   via `LinearMap.ext` over `StairProd`, `rcases (v0,(v1,()))`, `Prod.ext` — three real blocks
   `projV0∘T∘inclV0 = f0`, `projV0∘T∘inclV1 = 0`, `projV1∘T∘inclV1 = f1` (define `c.1` FROM the actual
   off-diagonal block so the det-invisible `V0→V1` block matches automatically). The J00 block uses the
   banked `flatBlockLE_symm_fderiv_flatBlock` + `gate_schurCore_eq`. The remaining FOUNDATION GAP: the
   full `fderiv BparamsLeaf` per-layer CLM assembly is NOT yet banked (only the generic per-layer atoms
   `hasFDerivAt_Agen_interior`/`hasFDerivAt_chainA` + the layer-0 gate `layer0SchurMap_hasFDerivAt`
   exist) — it must be assembled as an explicit CLM before the three blocks can be matched.

## Level caveat

This is the boundary-factor staircase det `hDtot` ONLY (the interior-det headline, chart-Jacobian
level). Does NOT transfer to `rlct = ½·codim` (cited Aoyagi) nor the lower-leg `rlctAtOn`. When the
residual lands, the ∀M-L2 interior-det `|det Dφ|` is CLOSED — feeding both the ∀M-L2 interior-det
headline AND R1's `cover_ge_div` (the lower leg's `NodeAchieverChart`).
