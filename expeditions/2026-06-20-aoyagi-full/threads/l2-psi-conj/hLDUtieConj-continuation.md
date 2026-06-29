# hLDUtieConj — precise continuation recipe (the last L2-Ψ_conj follow-on)

**State (branch `genm-l2psi` @7e9a2d66).** The Step Ψ_conj apparatus is complete and banked:
`deepest_diffeo_bridge_L2_conj_impl` (the bridge, parametric in `hsub3reg`/`hsub4core`/`hDA`),
`deepestCoreF_coreAbsorbConj_psiSplitRawL2CoreConj_eq_score` (the in-file hsub4core discharge **modulo
the single readback-tie `hLDUtieConj`**), and the chart-point block-decomposition foundation
`reindex_decode_split_blocks`. This note closes the last gap: `hLDUtieConj`.

## The target

`hLDUtieConj : frobSq (prod (deepestM H r) C) = Score x`, where
`C = Function.update (fun s => decode(split x).core_s + schurCorrectionConj(split x)_s) (lastLayer hL)
((1 − l2KConj q) * l2S1Conj q)` (`q = split x = deepestSplit w0 x`), and `Score x` is the wire's Score
(the `(1,1)`-Schur integrand of the framed product `endpointP0·(prod(decode x) − B)·endpointQL`).

The banked `prod_deepestM_eq_schur_ldu_readback` (Fin 3, `DeepestLDUReadback:207`) gives exactly
`prod (deepestM H r) C = Score-integrand x` GIVEN: a tuple `C` with `hC0`/`hC1`, the corner-split `hS3b`,
`hPtri`/`hQtri`/`hP22`/`hQ22`, and 5 invertibilities. So `hLDUtieConj` = `frobSq`-of-that.

## The recipe (genm-l2thread-confirmed, controller-attributed)

**Step A — the block-read identities at `q = split x`** (from `reindex_decode_split_blocks`, mirroring
the `h11/h12/h21/h22` extraction in `absorbedCoreConj_eq_schurCore`'s proof, `DeepestLDUReadback:429-446`):
- `(reindex(decode x)_s).toBlocks₁₁ = deepBlkA_s + readX(q)_s` (= `l2A0Conj q` at s=0, `l2A1Conj q` at s=last).
- `.toBlocks₂₁ = deepBlkZ_s + readZ(q)_s` (= `l2Z1Conj q` at s=last).
- `.toBlocks₁₂ = deepBlkY_s + readY(q)_s` (= `l2Y0Conj q` at s=0 **with the midWidth_eq_of_L2 col-cast**;
  `l2Y1Conj q` at s=last).
- `.toBlocks₂₂ = decode(q).core_s` (= `l2T1Conj q = coreLast q` at s=last; uses `deepBlkT_last = 0`).
Build these as ~6-8 standalone lemmas (one per (block, layer) the readback reads). Each is a `funext` +
`reindex_decode_split_blocks` + `fromBlocks_apply··` (verbatim the `absorbedCoreConj_eq_schurCore` body).

**Step B — `P00c = Mid₁₁`** (`l2P00Conj q = (reindex(prod(decode x)).toBlocks₁₁`). `P00c = A0c·A1c +
Y0c·Z1c`. `reindex(prod x)_{(0,last)}.toBlocks₁₁` via `reindex_mul_fromBlocks` (the 2-layer product, with
the mid-interface cast `midWidth_eq_of_L2`) `= L0₁₁·L1₁₁ + L0₁₂·L1₂₁`. Match using Step A's block reads
(`A0c=L0₁₁`, `A1c=L1₁₁`, `Y0c=L0₁₂` cast, `Z1c=L1₂₁`). [`prodDecode_eq_two_of_L2` + `reindex_mul_fromBlocks`.]

**Step C — `hC0`/`hC1`:**
- `hC0`: `C 0 = decode(q).core_0 + corrConj(q)_0`. By `absorbedCoreConj_eq_schurCore` at `w=x`, `s=0`,
  `hT = deepBlkT_layer0_zero` ⟹ `= (reindex(decode x)_0).toBlocks₂₂ − ₂₁·₁₁⁻¹·₁₂` — EXACTLY the readback's
  `hC0` RHS. (Direct, no Step-A needed — the keystone already extracts it.)
- `hC1`: `C 1 = (1 − l2KConj q)·l2S1Conj q`. The readback's `hC1` RHS `= (1 − Z1·Mid₁₁⁻¹·Y0)·(layer-1
  Schur)`. Match factor-by-factor via Step A + Step B: `l2KConj q = Z1·P00c⁻¹·Y0 = Z1·Mid₁₁⁻¹·Y0` (Step B
  + Step A), and `l2S1Conj q = l2T1c − l2Z1c·l2A1c⁻¹·l2Y1c = ₂₂ − ₂₁·₁₁⁻¹·₁₂` = layer-1 Schur (Step A,
  with `l2T1c = ₂₂`). NOTE: the readback's `hC1` `(1−Kc)` uses `Mid₁₁` (the product (1,1)), NOT `P00c` —
  Step B identifies them.

**Step D — the 5 invertibilities + `hS3b`/triangularity** (producer-side, available near the basepoint):
- `hP11inv`/`hQ11inv`: the endpoint frames' (1,1) blocks invertible — from the triangular bundle
  (`hPtri`/`hQtri` + `hP22`/`hQ22 = 1`); the wire has these.
- `hMid11inv`: `reindex(prod(decode x)).toBlocks₁₁` invertible — `= P00c` (Step B), `P00c(0) = deepBlkA_0·
  deepBlkA_last` (units, `l2P00Conj_det_ne_zero`), invertible on a nbhd (the cutoff support / `hW`-style).
- `hA0inv`/`hA1inv`: `reindex(decode x)_{0,last}.toBlocks₁₁` invertible — `= l2A0Conj/l2A1Conj` (Step A),
  units at `0` via `hDA0`/`hDA1`, invertible near the basepoint.
- `hS3b`: the framed `B`-corner `= fromBlocks 1 0 0 0` — the wire's `hS3b` (producer pattern, the bare
  wire builds it at `DeepestL2Wiring:533`).

**Step E — `subst hL2eq` LATE + LOCAL.** Do the subst at the FINAL `prod(deepestM) C = Score-integrand`
step only (so the cast resolves definitionally — precedent `midWidth_eq_of_L2`). Then
`prod_deepestM_eq_schur_ldu_readback` (Fin 3) applies. Wrap in `frobSq` for `hLDUtieConj`.

## Estimate
~15-20 lemmas (Step A ≈ 8, Step B ≈ 2, Step C ≈ 2, Step D ≈ 4, Step E ≈ 1 assembly). All MECHANICAL
(block-read extraction + matrix-product blocks + the subst); the MATH is done (the keystones prove the
`(1−Kc)·S1c` identity; this is the readback plumbing). NOT a margin grind — a focused fresh-hand pass.

## Why this matters
The bare route's hsub4core is a PERMANENT W-a-FALSE sorry (`DeepestL2Wiring:679`) — the bare-pivot
dictionary is numerically false (A11 ≠ 1). The conjugated route is the FIRST to make
`prod_deepestM_eq_schur_ldu_readback` applicable (it was banked but unused). Closing `hLDUtieConj` makes
the L2 RLCT bridge atom-free AND sorry-free on the core leg — what the bare never could.
