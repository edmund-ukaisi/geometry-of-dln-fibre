**Architecture Verdict**
Use **A′: full pivot-split migration with frozen `regResidualPack`**. B is unsound. The pivot twist must reach both the final product read and the last layer’s `.succ`-side split inside `framedLayer`/`framedParamsReg`; merely adding `hB22` while keeping threshold reads does not change the actual derivative block. I would parameterize by `J` or an `eLast`, keep `regResidualPack := regPivotFinEquiv`, and use a local frame family at construction rather than globally rewriting `deepestPoint_frame`.

**Separability**
Yes, the matrix codomain split and the `Fin nReg` enumeration are separable. The banked `readX/Y/Z_regSlice_*` lemmas read the **domain slot** via `regGaugeIdxSplit` and `regPivotFinEquiv`; they do not depend on which raw output columns `toBlocks₁₂` later sees. So they survive if `regResidualPack` stays fixed.

What will not survive literally unchanged are lemmas whose RHS mentions `framedLayer`/`framedParamsReg` with hard-coded `rThresholdSplit`, especially the last-layer reg-slice and product/base lemmas. Those need pivot-split variants. The cancellation lemmas survive; the framed-product lemmas get retargeted.

**F-Invertibility**
With the last-layer `.succ` side also pivot-twisted, yes: `B` in the formula becomes `reindex eJ eJ (Qf (lastLayer hL))`, where `eJ := pivotThresholdSplit r (H (lastLayer hL).succ) _ J`. Then the linear part is still

`F(X,Y,Z) = (A11*X + A12*Z + Y*B21, Y*B22, A21*X + A22*Z)`,

with `A := reindex threshold threshold (Pf first)` and `B := reindex eJ eJ (Qf last)`. The banked frame fact certifies exactly this `B22`.

Important caveat: if only the final `deepestEPivot` product read is pivoted but `framedLayer` still inserts the last-layer `Y` using threshold columns, the block becomes mixed, essentially `reindex threshold eJ Qf`, not the certified `reindex eJ eJ Qf`. That is the concrete failure mode of B.

**Scoping**
Highest risk: PIN2 frame bridge. The `readX/Y/Z → raw deviation → framedLayer = P_s * raw * Q_s → endpoint telescoping → target normalization` chain is genuinely new geometry in Lean, even though the pivot-frame algebra is banked. Expect 500-900 LoC.

High risk: PIN1 full value-fold derivative. The formula is mathematically settled and reachable from banked Leibniz/cross-term lemmas, but the full product derivative assembly is still several hundred lines. Expect 350-700 LoC.

Medium risk: split/frame API migration. Add `J`/`eLast`, pivot variants of `framedLayer`/`framedParamsReg`, `_base`, `_contdiff`, `_sq_sum_eq_blocks`, and derivative callers. Reachable on existing patterns. Expect 200-400 LoC.

Medium-low risk: explicit invertible `F`. Needs local block-triangular inverse or equivalent construction from `A` unit and `B22` unit. No new geometry. Expect 100-250 LoC.

Low risk: consuming `exists_deepest_lastLayer_pivotFrame` at `deepest_gauge_construction`. The theorem is banked; wire the same `J,Q,hB22` into PIN1 and PIN2. Expect 50-120 LoC after interfaces exist.

I would plan for **PIN1 green + PIN2 honest-sorry** in one tide. Both green is possible only if the raw-frame bridge is already much closer than the comments indicate.

**Cheapest Discriminating Check**
Before the migration, prove one tiny local example: for arbitrary `Y`, `Q`, row split `eR`, and pivot column split `eJ`, the top-right block of

`reindex eR eJ ((reindex eR.symm eJ.symm (fromBlocks 0 Y 0 0)) * Q)`

is exactly

`Y * (reindex eJ eJ Q).toBlocks₂₂`.

If that elaborates cleanly, the pivot architecture is sound. If you instead leave the inner deviation split threshold, Lean will expose the wrong mixed reindex block, which is the obstruction you want to avoid.