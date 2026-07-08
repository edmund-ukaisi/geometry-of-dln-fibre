1. **VERDICT:** use **B′: boundary forced-decode of the effective target `movedC - corM`**. **OBSTRUCTION:** none, assuming the boundary forced-decode lemmas apply to the reindexed/pivot-reindexed frames.

2. Define, in the block coordinates used by `deepestChain`, the effective target
   `D_s := movedC C Z0e s - corM_s`, so if `movedC C Z0e s = fromBlocks A Y Z T`, then
   `D_s = fromBlocks (A - 1) Y Z T`.

   Then pack `fromBlocks X' Y' Z' T'` as:
   - interior layers: `fromBlocks X' Y' Z' T' := D_s`;
   - first layer: `fromBlocks X' Y' Z' T' := leftForcedDecode(Pf_0, D_0)`;
   - last layer: `fromBlocks X' Y' Z' T' := rightForcedDecode(Qf_last, D_last)`, using the last-layer pivot-aligned reindex on the successor side.

   This is the same mathematical content as A on the boundary, but stated in the form your banked lemmas prove directly. I would avoid full-matrix `Ring.inverse` in the definition unless you already have excellent simp support for reindexed matrix inverses.

3. **CorM consistency.** Derivable from the block algebra: subtracting `corM` is exactly correct. At layer `0`, with lower frame `P = fromBlocks P11 0 P21 1` and raw block `B = fromBlocks X Y Z T`,
   `C_11 = 1 + P11 X`. Since `movedC` keeps the `11` block, `D_11 = C_11 - 1 = P11 X`. The forced decode gives `X' = Pinv · (P11 X)`, hence `X' = X` provided `Pinv · P11 = 1`.

   The forced-decode lemma as you stated only needs `P11 · Pinv = 1`; the equality `X' = X` additionally needs the other inverse direction. I infer this is available if `Pinv` is the inverse of a unit. It is not needed to prove `hmove`; it is only needed to state “X is unchanged” literally.

4. Riskiest proof steps, cheapest first:
   - Show `movedC - corM` has `11` block `A - 1` and other blocks unchanged. This is routine but cast/reindex sensitive.
   - Apply the boundary forced-decode lemmas after the exact same reindex/pivot-reindex normalization as `framedParamsPivot`.
   - If you want the extra statement `X'_0 = Xq_0`, prove or import the two-sided inverse fact `Pinv · P11 = 1`; otherwise avoid making that equality part of `hmove`.