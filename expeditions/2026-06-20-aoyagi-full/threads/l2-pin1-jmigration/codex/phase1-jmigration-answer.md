**Q1(a).** Fact from the given setup: no, not in general. The pivot-column reindex of `fromBlocks 1 0 0 0` is not still literally `fromBlocks 1 0 0 0` unless the pivot split sends the original first-`r` column block to the new first block.

With arbitrary `J`, the column reindex can move some original first-`r` columns into the new `₂` block and some non-pivot columns into the new `₁` block. Then `P.toBlocks₁₁ = 1` and `P.toBlocks₂₁ = 0` are not automatic. They hold only under an extra alignment fact, e.g. `J` is the first-`r` inclusion or `pivotThresholdSplit` is known to preserve the base corner’s support.

So `deepestEPivot_base` genuinely risks breaking if the codomain split changes now.

**Q1(b).** Yes, Phase 1 can stay green-bankable by threading `J/hQf22` as unused parameters while leaving the codomain split unchanged. But plainly: this is mostly plumbing. It de-risks call signatures and the final call site, not the mathematical reindexing issue. It does not prove that the pivot split works.

**Q2 ranking.**

1. **B**: best minimal Phase 1. It threads the new data through the API and call site while preserving existing proofs and the two sorries. It is not a full mathematical advance, but it isolates signature churn.
2. **A**: most meaningful, but not minimal and not guaranteed green. It forces the real pivot-split problem now, especially `_base` and probably `_sq_sum`.
3. **C**: safest short-term but worst for risk. It leaves all signature churn plus the real proof breakage to Phase 2.

So if the goal is “Phase 1 green with PIN1/PIN2 unchanged,” choose **B**. It buys interface preparation, not proof of the pivot geometry.

**Q3.** Cheapest honest fix for **A** is not a lemma saying the whole reindexed matrix is `fromBlocks 1 0 0 0`; that is false for arbitrary `J`.

The right lemma shape would be block-level, but it needs an assumption about how `J` interacts with the base corner. For example:

```lean
-- schematic only
(toBlocks₁₁ (reindex eR eC (fromBlocks 1 0 0 0)) - 1 = 0) ∧
(toBlocks₁₂ (reindex eR eC (fromBlocks 1 0 0 0)) = 0) ∧
(toBlocks₂₁ (reindex eR eC (fromBlocks 1 0 0 0)) = 0)
```

with `eC = pivotThresholdSplit ... J`.

But for arbitrary `J`, this statement is not derivable from the snippets. It requires a pivot-support/alignment hypothesis. The banked `pivotThresholdSplit_castLE` confirms the special case `J = first r columns`; it does not justify arbitrary pivot columns.