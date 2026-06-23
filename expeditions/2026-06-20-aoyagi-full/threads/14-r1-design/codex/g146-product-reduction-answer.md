**Proof Structure**

FACT: the clean route should factor one new L2 normal-form lemma. After that, `product_reduction` is short.

1. Set `M := fun s => H s - r` and `nReg := r * (H 0 + H (Fin.last L) - r)`.
   Handle `r = 0` separately: `B = 0`, `deepestPoint = 0` morally, `nReg = 0`, so the theorem reduces to the core result for `M = H`. Verify exact existing lemmas for `rank = 0 -> B = 0`.

2. Prove/factor a lemma like:

```lean
deepest_regular_core_normal_form :
  rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL)
    = (nReg : ENNReal) / 2
      + rlctAtOn (dlnLoss M 0) (0 : Params M)
```

or the slightly lower-level version with
`G := fun C => Real.sqrt (dlnLoss M 0 C)` and RHS first as
`rlctAtOn (fun p : (Fin nReg → ℝ) × Params M =>
  (∑ i, p.1 i ^ 2) + G p.2 ^ 2) (0, 0)`.

3. Coordinates: first use the constructed deepest-point/block data to put layers in identity-corner perturbation form

```text
C_s = [[I_r + X_s, Y_s],
       [Z_s,       T_s]]
```

with reduced blocks of sizes `M s × M s.succ`. Then replace the regular coordinates by the output residual blocks

```text
P_11 - I_r,  P_12,  P_21
```

where `P = C_1 ... C_L`. The triangular pivots are `X_1`, `Y_L`, `Z_1`; the remaining variables are Schur-adjusted reduced blocks `C'_s`, whose residual core is `‖∏ C'_s‖² = dlnLoss M 0`.

4. Discharge chain:
   FACT: `block_elimination` supplies the endpoint normal form for `B`; `paramsEquivFlat` plus explicit coordinate reindexing supplies the product-measure/flat bridge; `rlctAtOn_eq_rlctAt` moves between `Params` and `rlctAtOn`.
   FACT: `rlct_additive_smooth_block` gives the `nReg / 2` shift once the form is literally `∑ xᵢ² + G²`.
   FACT: `routeM_rlctAtOn_eq_lambdaCore` gives the core value.
   VERIFY names: use `dlnLoss_nonneg` plus `Real.sq_sqrt` to rewrite `G² = dlnLoss M 0`.

**Hardest Sub-Step**

INFERENCE: the hard part is the regular/core normal form, not the Fubini/core composition. It is a clean explicit unit-pivot change of variables, not a new resolution/blow-up. But it is not just `rlctAtOn_comp_homeomorph`: the nonlinear triangular solve generally has unit Jacobian factor, not measure-preserving determinant `±1`. Use/factor through `rlctAtOn_unit_invariant_aux` plus germ locality; do not force the chart into the MP homeomorphism lemma.

**nReg Count**

FACT: the regular generators are

```text
P_11 - I_r : r²
P_12       : r(H_last - r)
P_21       : (H_0 - r)r
```

so

```text
nReg = r² + r(H_last-r) + (H_0-r)r
     = r(H_0 + H_last) - r²
     = r(H_0 + H_last - r).
```

The `r²` overlap is counted once, not twice.

**Shortcut**

No real shortcut past the r>0 normal form. Once that lemma exists, `product_reduction` is “core + regular shift + arithmetic.” The normal form should be named and proved independently.

Scope estimate: theorem shell after the lemma: 30-80 lines. Normal-form lemma: likely 600-1500 lines depending on block-matrix APIs/cast friction. A second-pass/pp-hall consult is warranted on the lemma statement and chart interface before grinding.