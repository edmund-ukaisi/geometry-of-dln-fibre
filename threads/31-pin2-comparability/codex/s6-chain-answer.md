Short answer: do not try to close `comp_identity_L2` as one proof. The clean proof wants named bridge lemmas. Also, as currently shaped, the frame hypotheses are the danger point.

**For (A)**

The clean statement is a reg-invariance lemma, but not frame-free:

```lean
deepestEFull H r hr hL J Pf Qf (psiSplitRawL2 H r hr hL q)
  = deepestEFull H r hr hL J Pf Qf q
```

or, easier for S6:

```lean
(∑ i, (deepestEFull ... (psiSplitRawL2 ... q) i)^2)
  = ∑ i, (deepestEFull ... q i)^2
```

`framedParamsPivot` is not already in the gauge-aligned frame. It contains the endpoint/frame data, so the raw identity `P01 = A0 * Y1 + Y0 * T1` only applies after the L=2 frame dictionary reduces the framed product to the raw two-layer block product. The hypotheses `hPtri/hQtri` are needed to stop the moved `(2,2)` block from leaking into the framed regular blocks.

In Lean, prove raw block facts first:

```lean
P00' = P00
P10' = P10
P01' = P01    -- by e2_regPreserve
```

Then lift to `deepestEFull` through the block packing used by `deepestEFull_sq_sum_eq_blocks` / the pivot residual read. Use `hregval` only at the end to return to `(regStraighten _).1`.

**For (B)**

The algebraic chain should be:

```lean
deepestCoreF H r (coreAbsorb qψ).2.1
= deepestCoreF H r (deepestCoreAbsorb H r hr hL qψ).2.1
= frobSq (prod (deepestM H r)
    (fun s => coreRead qψ s + schurCorrection H r hr hL (qψ.1, qψ.2.2) s))
= frobSq (S0 * S1')
= frobSq Rcore
= Score x
```

with `q := split x`, `qψ := psiSplitRawL2 H r hr hL q`.

Lemma ownership:

1. `hcoreabs` rewrites `coreAbsorb`.
2. `deepestCoreF_coreAbsorb_eq_prodSchur` gives the `frobSq(prod ...)` expression, on the inner ball.
3. A new `psiSplitRawL2Core_absorbed_reads` should prove:
   ```lean
   first absorbed core = T0 - Z0 * A0⁻¹ * Y0
   last absorbed core  = (1 - K) * (T1 - Z1 * A1⁻¹ * Y1)
   ```
   The last-layer proof uses `l2Y1p_sub_Y1`, `l2T1p_eq`, `W * W⁻¹ = 1`, and associativity.
4. `prod_absorbed_eq_schur_ldu` turns `S0 * S1'` into the two-layer Schur complement.
5. `hScoreDef` identifies the public `Score`, but only after the framed-product/corner-split dictionary.

The likely bite: `prod_absorbed_eq_schur_ldu` is frame-free, while `Score` is built from `endpointP0 * (prod - B) * endpointQL`. Use `rcore_eq_schur_of_corner_split` / `rcore_schur_factor_of_corner_split` from `DeepestBlockDecomp`, or a specialized L2 dictionary. Triangularity alone is not enough for exact `frobSq` if endpoint bottom-right blocks are arbitrary; exact equality needs bottom-right identity/unitriangular normalizers or the core diffeo must absorb those units.

**Recommended Split**

1. `psiRawL2_split`:
   ```lean
   split (psiRawL2 ... x) = psiSplitRawL2 ... (split x)
   ```
   from `hsplit`, `psiRawL2`, and `Homeomorph.apply_symm_apply`.

2. `psiSplitRawL2Core_readbacks`:
   A0/A1/Y0/Z0/Z1/T0 fixed, `Y1 ↦ l2Y1p`, `T1 ↦ l2T1p`. Use `DeepestPsiLens`.

3. `deepestEFull_psiSplitRawL2_eq`:
   reg residual invariant. This is where `hPtri/hQtri` and frame bookkeeping belong.

4. `deepestCoreF_coreAbsorb_psiSplitRawL2_eq_score`:
   the E1/LDU chain above, plus the framed `Score` dictionary.

5. `comp_identity_L2`:
   pure germ assembly:
   `psiL2_eventuallyEq_psiRawL2`, inner-ball/unit eventually facts, `hΦscore`, `hregval`, `hcoreabs`.

Riskiest step: the public `Score` dictionary, not the `W⁻¹` algebra. Also watch the `A⁻¹` vs `⅟A` mismatch: most landed algebra lemmas use `⅟`; the Ψ definitions and `Score` use nonsingular inverse `⁻¹`, so locally instantiate `Invertible` from `det ≠ 0` and rewrite with `invOf_eq_nonsing_inv`.