**1. Claim-C**

Yes, Claim-C is the right per-layer target, but only as a **Schur equality**, not a boundary blockwise equality.

Interior proof: use Step-A, then `deepestChain_framedParamsPivot_blocks_of_frame_one` plus `deepBlkA_interior_eq_one`, `deepBlkY_interior_zero`, `deepBlkZ_interior_zero`, and the needed `deepBlkT_interior_zero`/core-block fact. Then prove once that `blockSchur` commutes with the reduced `finCongr` relabel in this special form.

Boundary proof: do **not** identify `M_s^m` with `F' s` blockwise. The clean route is:
`F'_0 = P0chain * M_0^m` and `F'_{L-1} = M_{L-1}^m * QLchain`, using the boundary decode plus the normalization identities
`P0chain * deepBlk_0 = corM` and `deepBlk_last * QLchain = corM`.
Then apply `blockSchur_lowerFrame_left` / `blockSchur_rightUpper_right`.

Hidden gap: if your boundary fact 9 is used only as “`frame * forcedDecode`”, that is insufficient. The correct object is `frame * (deepBlk + forcedDecode)`, equivalently `corM + frame * forcedDecode`. The deepBlk boundary term does not break the proof, but it must be included.

**2. Lemma 5 Cancellation**

Your cancellation algebra is correct, with one correction: the prefix formula is not true at `k = 0`. Use it only for `1 ≤ k ≤ L-1`; handle `k = 0` by `Kcoup_zero`.

Load-bearing step:
`(P11 * B * Q11)⁻¹ = Q11⁻¹ * B⁻¹ * P11⁻¹`, requiring units/invertibles for `P11`, `B = (partProd D L).toBlocks₁₁`, and `Q11`.

Clean induction hypotheses:

```lean
∀ k, 1 ≤ k → k ≤ L - 1 →
  partProd F k = P0chain * partProd D k

partProd F L = P0chain * partProd D L * QLchain
```

Key rewrites:
1. `F 0 = P0chain * D 0`, interior `F k = D k`, last `F (L-1) = D (L-1) * QLchain`.
2. Prefix induction from `k=1`; step uses `partProd _ (k+1) = partProd _ k * _` and `Matrix.mul_assoc`.
3. Read blocks with `toBlocks₁₁_mul`, `toBlocks₁₂_mul`, `toBlocks₂₁_mul`; simplify by `P12=0`, `P22=1`, `Q21=0`, `Q22=1`.
4. Unfold `Kcoup`; split `k=0`, interior, last; cancel `P11`/`Q11` using the pivot-unit hypotheses.

**3. Formalisation Risks**

`Ring.inverse` will bite only if you mix it casually with `⁻¹`. Stay in `Ring.inverse` where possible; when using `[Invertible X]`, rewrite with the existing pattern `Ring.inverse_invertible` / local `ring_inverse_eq_nonsing_inv`. For product inverses, make small local cancellation lemmas with exact `letI` instances for `Invertible (P11 * B)` and `Invertible (P11 * B * Q11)`.

For reindexing, define chain-width endpoint frames once:
`P0chain`, `QLchain`. Prove `F0`, `Flast`, and interior layer equalities at the `deepestChainSplit`/`reindex_mul` level, then forget the H-width matrices. Do not go entrywise except for already-isolated block/readback lemmas.

Use the banked block multiplication lemmas: `toBlocks₁₁_mul`, `toBlocks₁₂_mul`, `toBlocks₂₁_mul`. They are exactly the right surface for the partial-product block formulas.

**4. Simpler Route**

I do not see a simpler route already banked. `Kcoup_movedC` is about invariance under `movedC`, not endpoint frame invariance `F` versus `D`. The clean improvement is to package Lemma 5 as a reusable abstract lemma: “one lower frame at layer 0 and one upper frame at layer `L-1` preserve `Kcoup`.” That is still the same partial-product telescope, just isolated from DLN/reindex bookkeeping.