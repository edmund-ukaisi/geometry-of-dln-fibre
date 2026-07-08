**1. VERDICT**

**yes-with-new-lemma**, for the chart-specialized goal `q = deepestSplit … w0 x`. For completely free unrelated `q` and `x`, `hC` is not reachable and should not be true.

Load-bearing reason: the banked `psiSplitRawGen_deepestChain_hmove` moves the **framed** chain
`deepestChain (framedParamsPivot q)`, while the keystone’s `hC` wants the moved Schur core of the **raw decode** chain `deepestChain ((paramsEquivFlat H).symm x)`. The missing bridge is Schur-level endpoint-frame invariance, not a full blockwise chain equality.

**2. LHS = `blockSchur M_s`**

Yes, your generic reduction is correct, modulo casts: after `coreRead_psiSplitRawGen` and `gaugeReadX/Y/Z_psiSplitRawGen`, the LHS is the Schur complement of

```lean
fromBlocks
  (deepBlkA s + psiReadBlk₁₁)
  (deepBlkY s + psiReadBlk₁₂)
  (deepBlkZ s + psiReadBlk₂₁)
  (psiReadBlk₂₂)
```

provided `deepBlkT_s = 0`.

The `deepBlkT_s = 0` claim is mathematically correct for every layer: boundary by `deepBlkT_layer0_zero` / `deepBlkT_layerLast_zero`, interior from `deepestPoint_interior_eq_corM`. I did not find a named all-layer `deepBlkT_zero_gen`; if absent, it is a cheap wrapper, not the wall.

**3. THE LINCHPIN**

Your proposed full framed-chain/decode-chain reconciliation is **not true in that blockwise form** at the boundary. Banked repo fact `framedParamsPivot_eq_frame_of_front` gives, for `q = split x`,

```lean
framedParamsPivot ... q s = Pf s * ((paramsEquivFlat H).symm x) s * Qf s
```

not equality with `decode x`. Thus at layer `0` the `₁₁` block is generally `P11 * A11`, and at the last layer generally `A11 * Q11`; it is not
`A11 - deepBlkA + 1` unless the endpoint frame corner is identity. Strict interiors are fine because the frames are identity and `deepBlkA = 1`.

Cheapest route should **avoid** that linchpin. A direct “hmove on the decode chain” as full matrix equality is also the wrong target; boundary forced decodes only give Schur-level agreement after triangular frame cancellation.

Single new lemma to build:

```lean
theorem blockSchur_movedC_framedSplit_eq_decode
  ... (x : Fin (flatDim H) → ℝ) :
  ∀ s : Fin L,
    blockSchur
      (movedC
        (deepestChain H r hr
          (framedParamsPivot H r hr hL J Pf Qf
            (deepestSplit H r hr hL
              ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) x)))
        (Z0edit0
          (deepestChain H r hr
            (framedParamsPivot H r hr hL J Pf Qf
              (deepestSplit H r hr hL
                ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) x))) L)
        (s : ℕ))
    =
    blockSchur
      (movedC
        (deepestChain H r hr ((paramsEquivFlat H).symm x))
        (Z0edit0 (deepestChain H r hr ((paramsEquivFlat H).symm x)) L)
        (s : ℕ))
```

with the front-pivot, triangular endpoint-frame, frame-normal-form, and needed chain/partial-product invertibility hypotheses.

**4. CHEAPEST ROUTE**

1. Apply `absorbedCoreConj_eq_schurCore` to the moved split point `psiSplitRawGen … q`, using `wψ := (deepestSplit … w0).symm (psiSplitRawGen … q)`.

2. Discharge `hT` layerwise: boundary by `deepBlkT_layer0_zero` / `deepBlkT_layerLast_zero`, interior from `deepestPoint_interior_eq_corM`.

3. Rewrite the resulting plain Schur layer through `framedParamsPivot_eq_frame_of_front` and boundary Schur-invisibility (`blockSchur_lowerFrame_left`, `blockSchur_rightUpper_right`) to get:
   `LHS = blockSchur (deepestChain (framedParamsPivot (psiSplitRawGen q)) s)`.

4. Use `psiSplitRawGen_deepestChain_hmove`:
   this becomes `blockSchur (movedC (deepestChain (framedParamsPivot q)) ... s)`.

5. Specialize `q = deepestSplit … w0 x`.

6. Apply the new lemma `blockSchur_movedC_framedSplit_eq_decode`.

7. Clean the remaining width casts with `chainWidth_castSucc_sub`, `chainWidth_succ_sub`, and your `deepestChain_toBlocks₁₁_eq_layer`-style bridges.

So: reachable, but not from the listed banked pieces alone. The missing fact is the Schur-level endpoint-frame invariance of `movedC`, not the blockwise framed-chain/decode-chain identity.