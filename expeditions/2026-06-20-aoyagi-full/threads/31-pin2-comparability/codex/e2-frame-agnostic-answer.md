**Adjudication:** preservation is **frame-agnostic**, given the stated facts, but the proof cannot identify the framed reg blocks with the raw un-conjugated blocks unless the endpoint frames are trivial or suitably block-compatible.

**Facts from the setup:**

1. `deepestEFull q` reads blocks of  
   `reindex(rThr, pivotThr J)(prod(framedParamsPivot q))`, not blocks of the raw two-factor product.

2. For a FRONT pivot and `q = split w`, the banked relation says
   ```lean
   prod(framedParamsPivot(split w))
     = endpointP0(Pf) · prod(A(w)) · endpointQL(Qf)
   ```
   with `Pf_first` and `Qf_last` generally nontrivial units.

So the framed product’s reindexed `(1,1)/(1,2)/(2,1)` blocks are, in general, blocks of the **endpoint-conjugated** product. They are not literally the raw un-conjugated `P00 - 1`, `P01`, `P10` unless the surviving boundary frames are trivial, or unless extra block-compatibility facts make the conjugation invisible on those blocks.

**Inference for Ψ:**

If Ψ changes only `Y1` and `T1`, while keeping

```text
P01 = A0 · Y1 + Y0 · T1
```

fixed, and `P00`, `P10` do not involve `Y1,T1`, then the raw two-factor product’s relevant blocks `P00`, `P01`, `P10` are unchanged.

Because the endpoint frames `Pf/Qf` are fixed data and not functions of `q`, applying the same fixed left/right multiplication to two equal raw products gives equal framed products. More weakly, if the raw products agree in all entries that can affect the framed reg blocks under this fixed conjugation, then the framed reg blocks agree.

But from the facts as stated, the cleanest frame-agnostic route is:

```text
raw product unchanged on the needed product data
⇒ fixed endpoint-conjugated product unchanged on the corresponding framed data
⇒ reindexed framed reg blocks unchanged
⇒ deepestEFull squared energy unchanged.
```

This does **not** require `Pf_first = 1` or `Qf_last = 1`. It only requires that the frames are fixed with respect to Ψ.

**Answer by question:**

1. The framed reg blocks are generally **conjugated endpoint-frame blocks**, not literally the raw `P00 - 1`, `P01`, `P10`.

2. Preservation does **not** require trivial frames. Since the framing is fixed, unchanged raw product data remains unchanged after the same fixed framing. The argument is frame-agnostic, but it must track the fixed conjugation rather than erase it.

3. Yes: the important subtlety is that Ψ acts in split coordinates while `Pf/Qf` are fixed. Therefore the only Ψ-dependence enters through `readX/readY/readZ/T`. Under your stated assumptions, `X1`, `Z1`, hence `A1 = 1 + X1`, are untouched; only `Y1,T1` move, with `P01` held fixed.