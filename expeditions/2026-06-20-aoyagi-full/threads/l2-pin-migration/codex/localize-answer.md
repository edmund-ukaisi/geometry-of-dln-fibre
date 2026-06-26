**1. Verdict**

L2 is unsound in general; use L1. Known algebra: if `eT = rThresholdSplit ...` and `eJ = pivotThresholdSplit ...`, then a last-layer deviation inserted with threshold columns gives

```lean
toBlocks₁₂ (reindex eR eJ ((reindex eR.symm eT.symm (fromBlocks 0 Y 0 0)) * Q))
= Y * (reindex eT eJ Q).toBlocks₂₂
```

not `Y * (reindex eJ eJ Q).toBlocks₂₂`. The outer pivot read only changes which output columns are selected; it does not change the summation rows of `Q` selected by where the inner `Y` block was inserted. So your reasoning is right: L2 produces the mixed threshold/pivot block. Inference for this repo: that mixed block is exactly the earlier failure mode and is not certified invertible by the pivot frame hypothesis.

**2. L1 Shape**

Use a **single last-layer column split/equiv**, not a uniform per-layer family. Internally, make the `.succ`-side split be:

```text
rThresholdSplit r (H s.succ)        for first/interior layers
eLast = pivotThresholdSplit ... J    only for the last layer’s .succ side
```

The last layer’s `.castSucc` row side should remain `rThresholdSplit`, matching the previous layer and the frame fact of shape:

```lean
reindex (rThresholdSplit r (H last.castSucc)) eLast (...)
= fromBlocks 1 0 0 0
```

Banked lemma impact:

- `readX/Y/Z_regSlice_*`: survive unchanged. They read packed parameters; `regResidualPack` stays frozen.

- `framedParamsReg_regSlice_first`: algebra survives unchanged because its `.succ`-side reindex is still `rThresholdSplit r (H s.succ)`.

- `framedParamsReg_regSlice_interior`: same; unchanged algebra and same `.succ`-side threshold split.

- `framedParamsReg_regSlice_last`: needs the real pivot variant. Its RHS must use the last-layer `.succ` split `eLast`, so the `Y` block is inserted into pivot-complement columns.

If you introduce a new `framedParamsRegLastPivot`, first/interior may need thin wrapper lemmas saying the new family agrees with the old one away from the last layer, but they should not need new pivot proofs.

**3. One-Tide Scope**

Yes: target **API migration + PIN1 green + PIN2 statement updated to the pivot split with an honest `sorry`**. Do not try to make both PIN1 and PIN2 green in the same tide.

The valuable stopping point is: final-read split and last-layer `.succ` split use the same `eLast`; PIN1’s derivative uses the clean `(reindex eLast eLast Q).toBlocks₂₂`; PIN2 states the correct pivot frame/invertibility hypotheses but leaves the longer product/reg-slice proof as future work.