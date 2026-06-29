**Verdict:** if you must use `deepestEFull_sq_sum_psiSplitRawL2_eq`, prove one private triple lemma and project hm11/hm12/hm21 from it. But the cleaner conjugated route is to avoid standalone raw hm entirely and discharge the regular term at the framed/conjugated level with `e2_regPreserve`.

**Skeleton For Raw hm Triple**

Let:

```lean
q   := split x
qψ  := psiSplitRawL2CoreConj … q
Aψ  := (paramsEquivFlat H).symm (split.symm qψ)
Aq  := (paramsEquivFlat H).symm x

G0   := reindex eR eMid (Aq 0)
G1ψ' := reindex eMid eC (Aψ 1)
G1q' := reindex eMid eC (Aq 1)
```

Prove one helper:

```lean
have hreg :
  (reindex eR eC (prod H Aψ)).toBlocks₁₁ =
    (reindex eR eC (prod H Aq)).toBlocks₁₁ ∧
  (reindex eR eC (prod H Aψ)).toBlocks₁₂ =
    (reindex eR eC (prod H Aq)).toBlocks₁₂ ∧
  (reindex eR eC (prod H Aψ)).toBlocks₂₁ =
    (reindex eR eC (prod H Aq)).toBlocks₂₁ := by
```

Inside it:

1. Product unfold:

```lean
have hprodψ :
  reindex eR eC (prod H Aψ) =
    (reindex eR eMid (Aψ 0)) * G1ψ' := …
have hprodq :
  reindex eR eC (prod H Aq) =
    G0 * G1q' := …
```

Discharged by `prod_eq_prodAux_mul_last` / `prodDecode_eq_two_of_L2`.

2. Shared first factor:

```lean
have h0 :
  reindex eR eMid (Aψ 0) = reindex eR eMid (Aq 0) := …
```

Best discharge: use `reindex_decode_split_blocks` at layer `0`, then `readX_…`, `readZ_…`, `readY_…_of_ne_eq`, `coreRead_…_of_ne`. Avoid frame cancellation here unless forced.

3. Last-factor `{11}` agreement:

```lean
have h11G :
  G1ψ'.toBlocks₁₁ = G1q'.toBlocks₁₁ := …
```

Discharged by `reindex_decode_split_blocks` at last layer plus `readX_psiSplitRawL2CoreConj_eq`.

4. Last-factor `{21}` agreement:

```lean
have h21G :
  G1ψ'.toBlocks₂₁ = G1q'.toBlocks₂₁ := …
```

Discharged by `reindex_decode_split_blocks` at last layer plus `readZ_psiSplitRawL2CoreConj_eq`.

5. Moved-Y bridge:

```lean
have hYmove :
  G1ψ'.toBlocks₁₂ =
    G1q'.toBlocks₁₂
      + (G0.toBlocks₁₁)⁻¹ * G0.toBlocks₁₂ *
          (G1q'.toBlocks₂₂ - G1ψ'.toBlocks₂₂) := …
```

Discharged from `readY_psiSplitRawL2CoreConj_last_eq`, `coreRead_psiSplitRawL2CoreConj_last`, and the definitional shape of `l2Y1pReadConj` / `l2T1pConj`, after translating decoded blocks with `reindex_decode_split_blocks`.

6. Exact `he2` shape:

```lean
have he2 :
  G0.toBlocks₁₁ * G1ψ'.toBlocks₁₂
    + G0.toBlocks₁₂ * G1ψ'.toBlocks₂₂
  =
  G0.toBlocks₁₁ * G1q'.toBlocks₁₂
    + G0.toBlocks₁₂ * G1q'.toBlocks₂₂ := …
```

Close this by rewriting with `hYmove` and applying:

```lean
e2_regPreserve
  G0.toBlocks₁₁
  G0.toBlocks₁₂
  G1q'.toBlocks₁₂
  G1q'.toBlocks₂₂
  G1ψ'.toBlocks₂₂
```

So the e2 keystone is `e2_regPreserve`, not `l2T1pConj_sub_Z1A1invY1pConj_eq`. The latter is for the core/Schur tie, unless your definitions of `l2Y1pReadConj` force it indirectly.

7. Apply the engine once:

```lean
have hregFactors := by
  exact reindex_prod_regBlocks_eq_of_e2
    eR eMid eC G0 (Aψ 1) (Aq 1) G1ψ' G1q'
    h11G h21G he2
```

Then `simpa [hprodψ, hprodq, h0, G0, G1ψ', G1q'] using hregFactors`.

**Biggest Risk**

The largest cast/friction point is the decoded-layer-to-read bridge, especially for `{12}` and `{22}` at the last layer. Sidestep it by proving tiny local “block readback” haves first:

```lean
G1ψ'.toBlocks₁₂ = l2Y1pReadConj q
G1ψ'.toBlocks₂₂ = l2T1pConj q
G1q'.toBlocks₁₂ = …
G1q'.toBlocks₂₂ = …
G0.toBlocks₁₁ = …
G0.toBlocks₁₂ = …
```

all via `reindex_decode_split_blocks`. Then do the algebra only in these dictionary variables. Do not try to cancel `Pf/Qf` frames to prove raw layer equality unless the consumer forces it.

**One Lemma Or Three**

Prove one private conjunction/triple lemma using one `reindex_prod_regBlocks_eq_of_e2` call. Define `hm11`, `hm12`, `hm21` as projections. Three separate lemmas will duplicate the hard cast work and invite divergence.

**Cheaper Alternative**

Yes: if you can avoid the #147 raw-hm API, prove the regular block agreement directly for `framedParamsPivot` products and feed the lower residual block criterion. That route sidesteps most `paramsEquivFlat.symm` decode friction.

But if #147 is the fixed consumer and it literally requires raw `prod H Aψ` / `prod H Aq` hm facts, then you still need the raw triple above. In that case, keep the proof raw but block-dictionary-driven; do not detour through framed cancellation.