# Codex consult: cleanest Lean route for J11 (the chain-block fderiv), Lean 4 / Mathlib v4.29

## Setting
J00 + J01 are DONE (sorry-free). Only J11 remains. I have all the structural facts confirmed by `rfl`/probes.

### J11 TARGET
```
(eihdT ha h0r h0c u (0, (v1, PUnit.unit))).2.1 = eihdF ha (pbo u) 1 v1
```
where `eihdF ha y₀ 1 = chainUnitMap (readN ⟨0⟩)` and `chainUnitMap N : (W,C) ↦ (W, C − N·W)`.
`v1 : eihdV M 1 = Matrix(schurC1, Wext2) × Matrix(schurT1, Wext2)` = `(W, leaf)`.

### Confirmed by rfl / probes:
- Bridge 1: `eihdT w = packStair ha (fderiv (fun z => BparamsLeaf ha z) y₀ (eIn.symm w))`, `y₀ = pbo u`.
- `(packStair p).2.1 = packLayer1 ha (p 1)` (rfl).
- Bridge 2a: `fderiv (fun z=>BparamsLeaf z) y₀ w 1 = fderiv (fun z => BparamsLeaf ha z 1) y₀ w`.
- `packLayer1 ha A = prodComm (rowSplitLE ha (reindexL1 ha A))` (rfl), reindexL1 = reindex Matrix(M1,M2)→Matrix(Wext1,Wext2).
- `rowSplitLE ha : Matrix(Wext1,Wext2) ≃ₗ Matrix(schurT1,Wext2) × Matrix(schurC1,Wext2)` — splits ROWS Fin(Wext1) by `(finSumFinEquiv ∘ finCongr(schurT1+schurC1=Wext1)).symm` into (kept=Fin schurT1, lift=Fin schurC1), via sumArrowLequivProdArrow + ofLinearEquiv.
- `BparamsLeaf ha z 1 = reindex_M (Agen 1 ... 1)` (rfl).
- `Agen 1 ... 1 = chainA (genWidthEq ... 1 (1<2)) (Nblk 1) (Wblk 1) (Cgen 2)` (rfl, dif_pos).
- At boundary 1: chainA has `M'=Wext1`, `t=Text2=schurT1`, `c=Wext1−Text2=schurC1`, `m'=Wext2`.
  chainA splits rows Fin(Wext1) by `finSplit (Text2 ≤ Wext1)` into kept (Fin t = `Cgen2 − Nblk1·Wblk1`) + lift (Fin(M'−t) = `Wblk1` reindexed).
- `Nblk 1 = readN ⟨0⟩` (boundary-0 frame N, = the V0 frame N!), `Wblk 1 = readW ⟨0⟩`, `Cgen 2 = rfinDirect ha z` (the leaf).
- `(eIn ha δ).2.1 = (wToMat ha (read lift slot ⟨0,inr⟩), leafToMat ha (read leaf slot ⟨1,inl⟩))`.

### Banked fderiv atoms:
- `hasFDerivAt_chainA (h) Nf Wf Cf dN dW dC u hN hW hC : HasFDerivAt (fun x => chainA h (Nf x)(Wf x)(Cf x)) (chainAFDeriv h Nf Wf dN dW dC u) u`.
- `chainAFDeriv h Nf Wf dN dW dC u` = the CLM: kept-block `dC − (N(u)·dW + dN·W(u))`, lift-block `dW` (reindexed onto rows via finSplit).
- `hasFDerivAt_matrixRead idx y₀ : HasFDerivAt (fun y => Matrix.of fun i j => y (idx i j)) (matrixReaderCLM idx) y₀`.
- `eIn_projV0 : (eIn ha δ).1 = slotReadV0 ha δ` (V0 read inverse: `slotReadV0 (eIn.symm w) = w.1`).
- For J00 I built `slotReadV0_fderiv_apply : fderiv slotReadV0 y₀ d = slotReadV0 d` (slotReadV0 linear, prod of matrixReaderCLM).

## Questions

**Q1.** The cleanest skeleton: I want to compute `packLayer1 (fderiv (BparamsLeaf·1) y₀ d)` at `d = eIn.symm (0,(v1,()))` and show `= chainUnitMap (readN⟨0⟩) v1 = (v1.1, v1.2 − readN·v1.1)`. My plan, mirroring J00:
  (a) function eq `(fun z => reindexL1 ha (BparamsLeaf ha z 1)) = (fun z => chainA (...) (Nf z)(Wf z)(Cf z))` where Nf/Wf/Cf = readN⟨0⟩/readW⟨0⟩/rfinDirect as functions (via the reindex-vs-Agen entrywise match);
  (b) `HasFDerivAt (fun z => reindexL1 (BparamsLeaf·1)) (chainAFDeriv ...)` via hasFDerivAt_chainA + congr;
  (c) push reindexL1 through fderiv (reindexL1 a CLM, uniqueness) → `reindexL1 (fderiv (BparamsLeaf·1) y₀ d) = chainAFDeriv ... d`;
  (d) `rowSplitLE` + `prodComm` applied to `chainAFDeriv ... d` (a Matrix(Wext1,Wext2)) → must yield `(lift-block, kept-block) = (dW d, dC d − N·dW d − dN d·W)`. The risk: does `rowSplitLE`'s row split (finSumFinEquiv ∘ finCongr) align with chainAFDeriv's `finSplit` block structure? Is `rowSplitLE (chainA-shaped matrix) = (kept, lift)` provable cleanly (both split Fin(Wext1) into Fin schurT1 ⊕ Fin schurC1 — but via finSumFinEquiv vs finSplit, which differ by a reindex)?
  Then (e) evaluate dN d = 0 (V0-frame zeroed by eIn.symm(0,...)), dW d = v1.1 (W), dC d = v1.2 (leaf). Is this the right plan, and what's the cleanest way to handle step (d) (the rowSplit-vs-finSplit alignment) — prove a lemma `rowSplitLE M = (M.submatrix castAdd id, M.submatrix natAdd id)` style, or match entrywise?

**Q2.** For step (e): I need `dN(d) = 0`, `dW(d) = v1.1`, `dC(d) = v1.2` where d = eIn.symm(0,(v1,())). dN = matrixReaderCLM(readN⟨0⟩-idx), so `dN d = Matrix.of fun i j => d (readN_idx i j)`. Since readN⟨0⟩ is a V0-frame slot and `eIn.symm(0,(v1,()))` has V0 = 0: is the cleanest `dN d = slotReadV0(d).2.1`-style (reuse the V0 read = 0), or build a direct `readN_idx`-read-of-eIn.symm = 0? Note dW reads lift slot ⟨0,inr⟩ and dC reads leaf slot ⟨1,inl⟩ — these are the V1 components. Is there a clean `eIn.symm` evaluation: the readW/leaf reads of `eIn.symm (0,(v1,()))` recover `v1.1`/`v1.2` (the inverse of the P11d `(eIn δ).2.1 = (wToMat W-read, leafToMat leaf-read)`)? How to invert wToMat/leafToMat to get the raw matrix reads = v1 components?

**Q3.** Is there a trap where `Nblk1 · Wblk1` at the BASE point y₀=pbo u is nonzero and contaminates? No — the kept block at the DIRECTION d is `dC(d) − N(y₀)·dW(d) − dN(d)·W(y₀)`; with dN(d)=0 it's `dC(d) − N(y₀)·dW(d) = v1.leaf − readN(y₀)·v1.W`. And readN(y₀) = readN at pbo... but eihdF uses `readN ⟨0⟩` at y₀=pbo too. So they match (both readN at the same y₀). Confirm readN(pbo u)⟨0⟩ is the N in `chainUnitMap (readN⟨0⟩)` in eihdF ha (pbo u) 1 — i.e. the base-point N is consistent. Right?

Be concrete about Lean tactics. Flag any WRONG step or hidden finSplit/Fin.cast trap. This is the last block; I want a clean route, not thrash.
