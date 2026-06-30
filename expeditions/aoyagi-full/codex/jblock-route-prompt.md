# Codex consult: cleanest Lean route for 3 fderiv-CLM "J-block" lemmas (Lean 4 / Mathlib v4.29)

## Context
I'm closing 3 `sorry`s in a Lean module. They are projections of a flat-Jacobian conjugate.
All the hard analysis atoms are ALREADY BANKED (sorry-free). I need the cleanest assembly route.

### Banked facts (all sorry-free, reusable):
- `eihdT_eq_packStair_fderiv` (Bridge 1): `eihdT ... w = packStair ha (fderiv ℝ (fun z => BparamsLeaf ha z) y₀ ((eIn ha).symm w))` where `y₀ = pivotBlowupOn ... u`.
- `BparamsLeaf_fderiv_layer` (Bridge 2a): `(fderiv ℝ (fun z => BparamsLeaf ha z) y₀ w) s = fderiv ℝ (fun z => BparamsLeaf ha z s) y₀ w` for `s : Fin 2`.
- Probe (rfl): `(packStair ha p).1 = packLayer0 ha (p 0)` and `(packStair ha p).2.1 = packLayer1 ha (p 1)`.
- Probe (rfl): `BparamsLeaf ha z 0 = reindex_M (Agen 1 M (tach M) (genBlkFlatLive ... (rfinDirect ha z) z) hle 0)` (chartParamsGen unfolds to reindex of Agen layer).
- Probe (proven): `slotReadV0 ha ((eIn ha).symm w) = w.1` (the inverse of `eIn_projV0 : (eIn ha δ).1 = slotReadV0 ha δ`).
- `layer0SchurMap_hasFDerivAt`: `HasFDerivAt (layer0SchurMap ha hr hc) ((fderiv (flatBlock) _).comp ((schurFrameD (slotReadV0 ha y₀)).comp (fderiv (slotReadV0) y₀))) y₀` where `layer0SchurMap ha hr hc y := flatBlock hr hc (schurFrameMap (slotReadV0 ha y))`.
- `gate_schurCore_eq`: `(schurFrameD (slotReadV0 ha y₀)).toLinearMap = schurFrameDeriv (readX ⟨0⟩) (readK ⟨0⟩) (readN ⟨0⟩)`.
- `BparamsLeaf_layer0_entry`: `Agen 1 ... 0 (Fin.cast (genWidthEq) (Fin.castAdd (Wext M 0 - Text M 1) i')) j = layer0SchurMap ha hr hc z i' j` (entrywise; lift block empty since `c0 = Wext M 0 - Text M 1 = 0`).
- `flatBlockLE_symm_fderiv_flatBlock`: `(flatBlockLE hr hc).symm ∘ₗ (fderiv flatBlock z₀).toLinearMap = id`.
- `slotReadV0_hasFDerivAt`, `flatBlock_differentiableAt` (both banked).
- `chainUnitMap N : (W,C) ↦ (W, C − N·W)` (lowerTri, det 1) — banked.
- `hasFDerivAt_Agen_interior` / `hasFDerivAt_chainA` / `chainAFDeriv` — GENERIC per-layer fderiv atoms (take block-reader fderivs as hyps).

### packLayer0 / packLayer1 (the V0/V1 reshapes):
- `packLayer0 ha A = (flatBlockLE hr hc).symm (reindexLinearEquiv (finCongr (M0=Text1)) (finCongr (M1=Wext1)) A)` (rfl).
- `packLayer1 ha A = (rowSplitLE ha).trans prodComm` of `reindex(M1,M2 → Wext1,Wext2) A` — a ROW split of `Matrix(Wext1,Wext2)` into `(kept=leaf:Text2×Wext2, lift=W:(Wext1-Text2)×Wext2)` then SWAP to `(W, leaf)`.

### The 3 sorries (after Bridge1 + Bridge2a + packStair projection):
- **J00**: `packLayer0 ha (fderiv ℝ (fun z => BparamsLeaf ha z 0) y₀ ((eIn ha).symm (v0,(0,())))) = schurFrameDeriv X K N v0`  (X,K,N = readX/K/N ⟨0⟩).
- **J01**: `packLayer0 ha (fderiv ℝ (fun z => BparamsLeaf ha z 0) y₀ ((eIn ha).symm (0,(v1,())))) = 0`.
- **J11**: `packLayer1 ha (fderiv ℝ (fun z => BparamsLeaf ha z 1) y₀ ((eIn ha).symm (0,(v1,())))) = chainUnitMap (readN ⟨0⟩) v1`.

`v0 : SchurInc t r c` (the V0 space); `v1 : Matrix(schurC1,Wext2) × Matrix(schurT1,Wext2)` (the V1 = (W,leaf) space).

## Questions

**Q1.** For J00 + J01: the function `fun z => BparamsLeaf ha z 0` equals `reindexLE.symm ∘ layer0SchurMap ha hr hc` (entrywise via `BparamsLeaf_layer0_entry`). So `fderiv (fun z => BparamsLeaf ha z 0) y₀ = reindexLE.symm ∘L fderiv(layer0SchurMap) y₀`. Then `packLayer0 ha (...) = flatBlockLE.symm (reindexLE (reindexLE.symm (fderiv layer0SchurMap ...)))= flatBlockLE.symm (fderiv layer0SchurMap ...)`, and `flatBlockLE.symm ∘ fderiv(flatBlock) = id` collapses to `schurFrameD ∘ slotReadV0D` = (via gate_schurCore_eq) `schurFrameDeriv X K N ∘ (fderiv slotReadV0)`. Applied at `eIn.symm (v0,(0,()))`: `fderiv slotReadV0 y₀ (eIn.symm (v0,(0,())))` — since slotReadV0 is LINEAR, `fderiv slotReadV0 y₀ = slotReadV0` (as a map), so this `= slotReadV0 (eIn.symm (v0,(0,())))`. And `slotReadV0 (eIn.symm (v0,(0,()))) = (v0,(0,())).1 = v0` (the proven inverse). So J00 `= schurFrameDeriv X K N v0`. **Is this the cleanest route, and is the "fderiv of a linear map = the map applied, evaluated at a point through eIn.symm" step right (i.e. `fderiv slotReadV0 y₀ (eIn.symm w) = slotReadV0 (eIn.symm w)` — NO, fderiv is a LINEAR map applied to the DIRECTION eIn.symm w, and slotReadV0 linear means `fderiv slotReadV0 y₀ = slotReadV0.toCLM` as a constant; but slotReadV0 is affine-linear (a coordinate read with no constant term, so genuinely linear), so `fderiv slotReadV0 y₀ d = slotReadV0 d`). Confirm that the direction `d = eIn.symm w` is fed to the linear fderiv, giving `slotReadV0 (eIn.symm w) = w.1`. For J01 `w.1 = 0` so result is `schurFrameDeriv X K N 0 = 0`. Right?**

**Q2.** The cleanest Lean idiom to get `fderiv (fun z => BparamsLeaf ha z 0) y₀ = reindexLE.symm.toCLM ∘L fderiv(layer0SchurMap) y₀`: should I (a) prove the FUNCTION equality `(fun z => BparamsLeaf ha z 0) = reindexLE.symm ∘ layer0SchurMap` then `congrArg fderiv` + `fderiv_comp` with reindexLE.symm linear; or (b) prove `HasFDerivAt (fun z => BparamsLeaf ha z 0) (reindexLE.symm.toCLM.comp (fderiv layer0SchurMap y₀)) y₀` directly via `HasFDerivAt.comp` of `reindexLE.symm` (linear, `LinearMap.hasFDerivAt`) after `layer0SchurMap_hasFDerivAt`, using the function equality only to rewrite the base function? Which avoids the most Fin-cast pain? Give the exact tactic skeleton.

**Q3.** For J11 (the chain layer): `fun z => BparamsLeaf ha z 1 = reindex_M (Agen 1 ... 1)`, and `Agen 1 ... 1 = chainA(Nblk 1, Wblk 1, Cgen 2)` — but at the LEAF boundary, `Agen 1 ... 1` should be the chain map. What is the cleanest way to compute `packLayer1 (fderiv (fun z => BparamsLeaf ha z 1) y₀ d)` and match it to `chainUnitMap (readN ⟨0⟩) v1`? Note packLayer1 ROW-splits + SWAPs to `(W, leaf)`. The chainUnitMap is `(W,C) ↦ (W, C − N·W)`. Is the route: function-equality `Agen 1 ... 1`-reindexed = `chainA(...)`, then its fderiv via `hasFDerivAt_chainA`, then packLayer1's row-split/swap turns `chainAFDeriv` into `chainUnitMap`? Or is `Agen 1 ... 1` for L=2 actually `chainA(Nblk 1, Wblk 1, Cgen 2)` with `Wblk 1, Cgen 2` reading leaf coords — and the V1-input `d = eIn.symm (0,(v1,()))` zeroes the frame coords so only the chain structure survives? Sketch the cleanest decomposition.

Be concrete about Lean tactics (this is v4.29 Mathlib). Flag any step where my route is WRONG or has a hidden Fin-cast/defeq trap.
