**1. MISMATCH CHECK**

Verdict: the `read := absolute moved block − deepBlk` convention is correct, provided the readback lemma is in the same block coordinates as `deepestChain`.

Forced by your definitions:

- Pivot: `X` unchanged gives `deepBlkA_s + Xread_s` unchanged, so `A'_s = A_s`, matching `movedC`.
- Up: writing `Yread_s := Y'_s - deepBlkY_s` gives framed block `deepBlkY_s + Yread_s = Y'_s`.
- Down: writing only `Zread_0 := Z0edit0 - deepBlkZ_0` gives `Z'_0`; leaving other `Zread_s` fixed gives `Z'_s = Z_s`.
- Core: writing core slot `T'_s` is correct only because the core slot stores the raw `T` block, not a `deepBlkT + read` deviation. Do not write `S̃_s`; `movedC` needs raw `T'_s = S̃_s + Z'_s A_s⁻¹ Y'_s`.

The real kill-condition is coordinate mismatch, not the additive offset.

- If `framedParamsPivot`’s layer readback is literally in the `deepestChain` `rThresholdSplit` coordinates, then this is bounded plumbing.
- If the last layer is written in `pivotThresholdSplit J` coordinates while `deepestChain` reads with `rThresholdSplit`, then for non-front `J` this is a genuine mismatch. Minimal sketch: `r=1`, output width `2`, `J` selects column `1`; a matrix written with pivot-left column `1` and reread with threshold-left column `0` swaps the semantic block roles, so the threshold `toBlocks₁₂` does not read the written pivot-`Y`.
- If `Pf/Qf` are still applied as `P * fromBlocks(...) * Q` before the abstract read, then arbitrary off-diagonal frame blocks also break direct read-edit. You need a proved per-layer block readback after framing. Triangular hypotheses may prevent leakage but still may introduce block-unit factors unless the reads are already pre-normalized.

So: no hidden inconsistency in `Y'_s - deepBlkY_s`; possible genuine wall at `pivotThr J` vs `rThr`, and at frame mixing if no exact readback lemma exists.

**2. psiSplitRawGen DEFINITION SHAPE**

Define moved data from the abstract chain, then pull it back to split coordinates. Do not recompute the move in DLN coordinates.

Shape:

```lean
let Cq := deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)
let Z0' := Z0edit0 Cq L
let Y' s := movedY Cq s.val
let T' s := movedT Cq Z0' s.val
let g := regGaugeSlotEquiv H r hr hL (q.1, q.2.2)

let g' : RegGaugeIdx H r → ℝ :=
  fun idx =>
    match idx with
    | ⟨s, Sum.inl (Sum.inl ij)⟩ => g idx
    | ⟨s, Sum.inl (Sum.inr (i,j))⟩ =>
        (Y'_s_pulled_to_FinL - deepBlkY_s) i j
    | ⟨s, Sum.inr (i,j)⟩ =>
        if h : s = firstLayer hL then
          (Z0'_pulled - deepBlkZ_first) (h ▸ i) j
        else g idx

let core' :=
  paramsEquivFlat (deepestM H r) (fun s => T'_s_pulled_to_FinL)

let regspec' := (regGaugeSlotEquiv H r hr hL).symm g'
(regspec'.1, (core', regspec'.2))
```

The “pulled” helpers should absorb all `Fin L ↔ ℕ`, `deepestM`, and `deepestChainWidth` casts once. If the last layer is pivot-coordinate, the pullback must include the pivot/threshold reindex, not just `finCongr`.

**3. MOVE-IDENTITY PROOF STRATEGY**

Prove the chain identity layer-by-layer:

```lean
funext s
by_cases hs : s < L
```

For `hs : s < L`, set `sf : Fin L := ⟨s, hs⟩` and compare the four blocks.

- `₁₁`: readback gives `deepBlkA + old Xread`; unchanged, equals `Cq s.toBlocks₁₁`, hence moved pivot.
- `₁₂`: readback gives `deepBlkY + (Y' - deepBlkY) = Y' = movedY Cq s`.
- `₂₁`: split `s=0` versus successor. At `0`, get `Z0edit0`; otherwise unchanged, hence `movedZ`.
- `₂₂`: core readback gives `T' = movedT Cq Z0edit0 s`.

Then reassemble with `fromBlocks_toBlocks`.

For `¬ s < L`, use the tail default: both `deepestChain` sides are the block-normal corner, and `movedC` of the tail corner is again the corner.

L2 carryover: the same `regGaugeSlotEquiv.symm` readback pattern, `coreDecode_paramsEquivFlat`, `reindex_decode_split_toBlocks` or its framed analogue, and the `fromBlocks` reassembly. New work is all-layer `Y`, first-layer-only `Z`, full core tuple update, and the `Fin L`/`Nat` cast layer.

**4. RISK/SIZE**

If the coordinate readback is already aligned: about `1200–2200` Lean lines, mostly casts and readback lemmas, no new algebra.

Most likely wall: non-front `J` with a threshold-based `deepestChain`. That is not cosmetic; it changes which physical columns are the abstract pivot columns. Either restrict/prove `J = frontEmbed`, define a pivot-aware abstract chain, or explicitly transport moved blocks between threshold and pivot coordinates before writing reads.