<task>
Lean4/Mathlib formalisation, DLN-fibre RLCT project (v4.29 pin). I must prove the hypothesis `hC`
of a banked general-`L` keystone. I need a decorrelated verdict on whether `hC` is REACHABLE from the
banked pieces below, the CHEAPEST route, and — if it walls — the single precise missing lemma.

## The exact goal `hC` (verbatim shape the keystone consumes)

All over `ℝ`, `H : Fin (L+1) → ℕ`, rank `r`, `hr : ∀ s, r ≤ H s`, `hL : 1 ≤ L`.
`q : DeepestSplit H r (deepestNGauge H r)` and `x : Fin (flatDim H) → ℝ` are BOTH free; in the eventual
germ assembly `q = split x = deepestSplit H r hr hL w0 x` where `w0 = paramsEquivFlat H (deepestPoint H r B)`.

```
hC : ∀ s : Fin L,
  reindex (finCongr (chainWidth_castSucc_sub H r s)) (finCongr (chainWidth_succ_sub H r s))
      ( (paramsEquivFlat (deepestM H r)).symm (psiSplitRawGen … q).2.1 s
        + schurCorrectionConj H r B hB hr hL ((psiSplitRawGen … q).1, (psiSplitRawGen … q).2.2) s )
    = blockSchur (movedC (deepestChain H r hr ((paramsEquivFlat H).symm x))
                        (Z0edit0 (deepestChain H r hr ((paramsEquivFlat H).symm x)) L) (s : ℕ))
```

## Definitions (all banked, sorry-free)

- `decode w := (paramsEquivFlat H).symm w : Params H`. `Params H = (s:Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ`.
- `deepestChain H r hr A s = reindex (deepestChainSplit s) (deepestChainSplit (s+1)) (deepestChainLayer A s)`,
  where for `s<L`, `deepestChainLayer A s = reindex (finCongr …) (finCongr …) (A ⟨s,_⟩)` (a pure width-relabel of the layer),
  and `deepestChainSplit s = rThresholdSplit r (deepestChainWidth H s) _` (the `r ⊕ (·−r)` threshold split).
- `blockSchur P = P.toBlocks₂₂ − P.toBlocks₂₁ · Ring.inverse P.toBlocks₁₁ · P.toBlocks₁₂`.
- `movedC C Z0e s = fromBlocks (C s).toBlocks₁₁ (movedY C s) (movedZ C Z0e s) (movedT C Z0e s)`, and by construction
  `movedT = schurTilde + movedZ · Ring.inverse (C s).₁₁ · movedY`, so `blockSchur (movedC C Z0e s) = schurTilde C s = (1 − Kcoup C s) · blockSchur (C s)`. (Invariant B is banked.)
- `deepBlkA s := (reindex (rThr (H s.castSucc)) (rThr (H s.succ)) (deepestPoint H r B s)).toBlocks₁₁`; deepBlkY/Z are its ₁₂/₂₁.
- `schurCorrectionConj (p.1,p.2.2) s = −(deepBlkZ s + gaugeReadZ p s)·(deepBlkA s + gaugeReadX p s)⁻¹·(deepBlkY s + gaugeReadY p s)` (a matrix `⁻¹`, nonsing_inv).
- `psiSplitRawGen … q` packs, via `regGaugeSlotEquiv.symm` (gauge) + `paramsEquivFlat(deepestM)` (core), the four blocks of `psiReadBlk q s`.

## Banked readback lemmas (all sorry-free, verified present)

1. `coreRead_psiSplitRawGen`: `(paramsEquivFlat(deepestM)).symm (psiSplitRawGen q).2.1 s = (psiReadBlk q s).toBlocks₂₂`.
2. `gaugeReadX_psiSplitRawGen`: `gaugeReadX ((psiSplitRawGen q).1,(psiSplitRawGen q).2.2) s = (psiReadBlk q s).toBlocks₁₁` (and Y→₁₂, Z→₂₁).
3. `psiSplitRawGen_deepestChain_hmove` (needs `hL2:2≤L`, frame-triviality of interior layers, `Qf firstLayer=1`, `Pf lastLayer=1`, front pivot):
   `deepestChain H r hr (framedParamsPivot … (psiSplitRawGen q)) = movedC (deepestChain H r hr (framedParamsPivot … q)) (Z0edit0 …)`.
   NOTE: this is the FRAMED chain (`framedParamsPivot q`), NOT `decode x`.
4. `absorbedCoreConj_eq_schurCore` (for the UNMOVED point `p = deepestSplit w0 w`, needs `deepBlkT_s=0`):
   `coreRead(p) s + schurCorrectionConj(p.gauge) s = (reindex(decode w) s).₂₂ − (reindex(decode w) s).₂₁·((reindex(decode w) s).₁₁)⁻¹·(reindex(decode w) s).₁₂`
   i.e. `= blockSchur (reindex(decode w) layer s)`. Its proof uses `reindex(decode w) s = MD + FB`, MD=reindex(deepest_s), FB=fromBlocks of the gauge/core reads of `p`.
5. `deepBlkT_s = 0` (the deepest `.toBlocks₂₂`) holds at EVERY layer at the deepest point (layer0 cols vanish, last-layer rows vanish, interior = corner diag(I,0)); needs `hL2:2≤L` for the boundary lemmas.
6. `reindex_prod_eq_partProd`, `pivotFront_toBlocks··_eq_chainCol`, and the width bridge `(deepestChain A s).toBlocks₁₁ = (reindex (rThr (H s.castSucc)) (rThr (H s.succ)) (A ⟨s,_⟩)).toBlocks₁₁` for `s<L` (I just proved this last one, call it `deepestChain_toBlocks₁₁_eq_layer`).

## My analysis of the route (verify / correct)

Using (1)+(2), the LHS is `reindex(finCongr) ( (psiReadBlk q s).₂₂ − (deepBlkZ+(psiReadBlk q s).₂₁)·(deepBlkA+(psiReadBlk q s).₁₁)⁻¹·(deepBlkY+(psiReadBlk q s).₁₂) )`.
Define the synthetic layer `M_s := fromBlocks (deepBlkA+psiReadBlk₁₁) (deepBlkY+psiReadBlk₁₂) (deepBlkZ+psiReadBlk₂₁) (psiReadBlk₂₂)`.
Since `deepBlkT_s=0` at every layer, `M_s.₂₂ = psiReadBlk₂₂`, so the LHS = `blockSchur M_s` (a GENERIC algebraic fact analogous to (4) but for the moved point; provable without `p=deepestSplit w0 w`).
So the goal reduces to `blockSchur M_s = blockSchur (movedC (deepestChain (decode x)) (Z0edit0) s)`.

For interior layers, `psiReadBlk q s = psiGhat q s (relabel) = movedC(deepestChain(framedParamsPivot q)) s − corM`, so
`M_s = fromBlocks (deepBlkA + ((movedC framed) s).₁₁ − I) … (…₂₂)`. Meanwhile `movedC(deepestChain(decode x)) s` has ₁₁ = `(deepestChain(decode x) s).₁₁`.
So matching requires the LINCHPIN identity relating `(deepestChain (framedParamsPivot (split x)) s).₁₁` to `(deepestChain (decode x) s).₁₁ − deepBlkA + I`, i.e. reconciling the FRAMED chain of `split x` with the DECODE chain of `x` plus the deepest constants. At the basepoint (x=w0, q=0) both sides check out (framed chain = corner I, decode chain ₁₁ = deepBlkA), but for general x I have found NO banked reconciliation `deepestChain(framedParamsPivot(deepestSplit w0 x)) ↔ deepestChain(decode x)`.

## The L=2 template does NOT match

The L=2 keystone reads the UNMOVED point's core as the PLAIN (unmoved) Schur (via lemma 4) and feeds the L=2 telescope which takes PLAIN Schur reads — no `movedC`. My general keystone/telescope take MOVED `movedC(deepestChain(decode x))` reads. So the L=2 route is not directly transferable.
</task>

<output_contract>
Four terse sections:
1. VERDICT: is `hC` REACHABLE from the banked pieces? (yes / yes-with-new-lemma / genuine-wall). One load-bearing reason.
2. Is my "LHS = blockSchur M_s (generic)" reduction correct? Is the deepBlkT_s=0-everywhere claim it rests on correct?
3. The LINCHPIN: is the framed-chain(split x) ↔ decode-chain(x) reconciliation a TRUE identity in the needed form, and is it banked or new? If new, state the single lemma precisely (both sides). If the route should AVOID this linchpin, give the alternative (e.g. does `hmove` on the DECODE chain — `deepestChain(decode(psiSplitRawGen-image)) = movedC(deepestChain(decode x))` — make sense and is it cheaper?).
4. CHEAPEST ROUTE or WALL: either a concrete lemma-by-lemma route (≤8 steps, name the banked lemma at each), or a precise statement of the single missing fact that walls it (what to hand back to the controller).
</output_contract>

<grounding_rules>
Distinguish what you DERIVE from the definitions/lemmas I gave vs. what you INFER about the repo you cannot see. Flag any guessed lemma. Do not invent Mathlib lemma names. If a step needs a fact I did not list as banked, say so explicitly — that is exactly the value I want.
</grounding_rules>
