1. **Verdict: (C).** Use **full-product Schur** `R` as the intermediate residual, then reduce modulo the regular generators to a **core-only Schur-reduced chain** `G`; (A) as stated is false as a germ, not just at one exceptional point.

2. **B is not fed directly to `rlct_additive_smooth_block`.** Correct route is **(b3), justified by (b1)-style control**:
   `loss ≍ ΣE² + ‖R‖²`, then write
   `R = G(core) + Σ E_i H_i`
   with bounded analytic `H_i`, so
   `ΣE² + ‖R‖² ≍ ΣE² + ‖G(core)‖²`.
   The additive split applies only to `G(core)`, not to literal `R`.

3. **Reconciliation: A still differs on `{E=0}`.**
   Counterexample: `R|_{E=0} = -ε⁴`, while `∏ T̃_s = ε·0·ε·unit = 0`.
   Generic scalar `L=3` slice:
   ```
   C1 = [[1,0],[z1,t1]]
   C2 = [[1,y ],[z ,t2]]
   C3 = [[1,y3],[0 ,t3]]
   ```
   `E=0` gives `y3 = -t3 y`, `z1 = -t1 z`, hence
   ```
   R|_{E=0} = t1 (t2 - z y) t3
   ```
   but raw/per-layer-unit A gives `t1 t2 t3 · unit`. They differ generically. The salvaged per-layer object is the **layer Schur complement** `S2 = t2 - zy`, not `t2·unit`.

4. **Lean `deepestCoreF` should be**
   ```
   deepestCoreF(core) = ‖ S1 S2 ... SL ‖_F²
   ```
   on independent reduced layer matrices, i.e. `dlnLoss (H-r) 0`, where the chart supplies `S_s` as the Schur-reduced layer factors, with internal units absorbed by an analytic/unit-Jacobian core change. Not literal `R(full vars)`, and not raw `T_s·unit` unless `T_s` already means Schur-reduced.

5. **Most likely way your A could be “not wrong”:** notation drift. If your `T_s` has already been redefined to mean `T_s - Z_s(I+X_s)⁻¹Y_s` plus internal unit absorption, then A is really C. If `T_s` is the raw lower-right block, A is unsound.