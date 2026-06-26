1. **VERDICT:** Sound and sufficient **only if “frame in reading” means the decoder reconstructs the raw layer from the frameless split and then applies `P_s · _ · Q_s`; pure `readX/Y/Z` as framed block reads is not sufficient.**

2. **THE ROUND-TRIP:** the needed identity is, for `q = split w` and `A = paramsSymm w`,

```lean
framedParams H r hr hL q s =
  P_s.1.val * A s * Q_s.1.val
```

with `P_s, Q_s = deepestPoint_frame ... s`.

This holds by construction only if `framedParams` does something equivalent to:

```lean
let Araw : Params H := paramsSymm ((split.symm q) + deepestFlat?) -- exact affine form to verify
fun s => P_s * Araw s * Q_s
```

or, blockwise,

```lean
framedLayer q s :=
  reindex (toBlocks⁻¹ (toBlocks (P_s * rawLayerFromSplit q s * Q_s)))
```

Not by merely interpreting pure coordinate reads `readX/Y/Z q s` as the blocks of the framed layer. Those reads are raw split coordinates unless the read functions themselves apply the fixed linear map induced by `M ↦ P_s M Q_s`.

So the frame does **not** need to be inside the measure-preserving `split`; it must be inside the **decode/read map after `split`**. That preserves MP for L2, because the GL frame is not part of the change-of-variables equivalence.

3. **THE CLOSING LEMMA:** introduce/pin one lemma, e.g.

```lean
lemma framedParams_split_eq_frame_raw
  (w : Fin (flatDim H) → ℝ) :
  framedParams H r hr hL (split w) s =
    (deepestPoint_frame H r B ... s).1.val *
      (paramsSymm w s) *
    (deepestPoint_frame H r B ... s).2.val
```

Load-bearing requirements:

- `split`/`split.symm` round-trip with `paramsEquivFlat`;
- the translation sends `deepestPoint` to `0`;
- `rawLayerFromSplit (split w) s = paramsSymm w s`;
- `framedParams` applies the fixed frame after reconstructing that raw layer.

If current `framedParams` is only

```lean
fromBlocks (1 + readX q s) (readY q s) (readZ q s) T
```

with `readX/Y/Z` pure projections, this lemma is false in general.

4. **Impact on `deepestEPivot_regSlice_fderiv_id`:** it changes unless the regular coordinates are redefined after the frame. A constant GL pre/post-composition is a constant linear map, but its derivative is that linear map, not automatically `id`. The derivative remains `id` only if `deepestEPivot` reads coordinates **after** the framed decoder and the reg slots are defined as those framed coordinates. Otherwise expect a fixed invertible linear factor.

5. **Cheapest Discriminating Check:** evaluate at `w = deepestFlat`. If revised `framedParams (split deepestFlat) s` is not definitionally/provably

```lean
P_s * deepestPoint s * Q_s = corM
```

then the frame is in the wrong place. Next check one symbolic endpoint perturbation: a single raw coordinate should be mixed by `P_0 · _` or `_ · Q_{L-1}`. If `readX/Y/Z` still returns that coordinate unchanged as a framed block, the cert cannot close as stated.