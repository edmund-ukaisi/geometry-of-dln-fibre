<task>
Lean4/Mathlib v4.29. Give me the TACTIC-LEVEL proof skeleton for ONE lemma. I have all the
pieces banked; I need the assembly sequence to avoid thrash on the L=2 reindex casts.

## Lemma to prove (`framedReindexProd_blocks_eq_psiSplitRawL2Core`)
For H : Fin 3 → ℕ (L=2), the reindexed framed products of `psiSplitRawL2Core q` and `q` agree on
toBlocks₁₁, toBlocks₁₂, toBlocks₂₁:
  reindex (rThr (H 0)) (pivotThr (H last) J) (prod H (framedParamsPivot J Pf Qf (psiSplitRawL2Core q)))
  agrees with the same for `q`, on {11,12,21}.
(reindex outer = (rThresholdSplit r (H 0), pivotThresholdSplit r (H last) J).)

## What is banked (consume verbatim)
- `framedParamsPivot_psiSplitRawL2Core_of_ne (s) (hs : s ≠ lastLayer)`:
    framedParamsPivot (psiSplitRawL2Core q) s = framedParamsPivot q s   (layer 0 = identical)
- `prod_eq_prodAux_mul_last (m:=1) H A rfl rfl`:
    prod H A = prodAux H A 1 _ * reindex (finCongr e1.symm) (finCongr e2.symm) (A ⟨1,_⟩)
  and prodAux H A 1 = 1 * reindex(A 0) (= reindex(A 0)), via prodAux_succ + prodAux 0 = 1.
  (cf. the banked `prod_deepestM_eq_two_of_L2` which does EXACTLY this peel for the core tuple.)
- `reindex_mul_fromBlocks (eR eMid eC) (G0 G1)`: reindex eR eC (G0·G1) = fromBlocks of the 4
  block-multiply combos of (reindex eR eMid G0).toBlocksᵢⱼ and (reindex eMid eC G1).toBlocksᵢⱼ:
    {11}=A0·A1+Y0·Z1, {12}=A0·Y1+Y0·T1, {21}=Z0·A1+T0·Z1, {22}=Z0·Y1+T0·T1.
- `reindex_mul_split (eR eMid eC) G0 G1`: reindex eR eC (G0·G1) = reindex eR eMid G0 · reindex eMid eC G1.
- `framedParamsPivot_last`: framedParamsPivot q last = reindex⁻¹(fromBlocks 1 0 0 0) + Pf last ·
    reindex⁻¹(fromBlocks (readX) (readY) (readZ) (coreT)) · Qf last.   (the only changing factor)
- The move readbacks: readX/readZ FIXED (readX_psiSplitRawL2Core_eq, readZ_psiSplitRawL2Core_eq),
    readY last → l2Y1p (readY_psiSplitRawL2Core_last_eq), coreT last → l2T1p (coreRead_psiSplitRawL2Core_last).
- `e2_regPreserve [Invertible A0] : A0·(Y1+⅟A0·Y0·(T1−T1')) + Y0·T1' = A0·Y1 + Y0·T1`
    (the {12}=P01 leak-kill; A0,Y0 are RAW per-layer blocks, NOT framed).
- `Matrix.toBlocks_fromBlocks₁₁/₁₂/₂₁/₂₂`, `fromBlocks_multiply`, `fromBlocks_toBlocks`.

## The math
The L=2 product = (factor0) · (reindex factor1). factor0 identical for ψq vs q. factor1 differs only
in its middle fromBlocks {12}=Y(→Y1') and {22}=T(→T1'); {11}=X and {21}=Z fixed. The reindexed full
product's {11,12,21} via reindex_mul_fromBlocks read factor0's blocks (fixed) and factor1's {11},{21}
(fixed since X,Z fixed) — EXCEPT {12} which reads factor1's {12}=Y and {22}=T. But here is the SUBTLETY
(flagged by a prior consult): factor1 is FRAMED (Pf·mid·Qf + corner), so its reindexed toBlocks are NOT
the raw X/Y/Z/T — the per-layer frame Pf(last)/Qf(last) MIXES blocks. So I CANNOT directly say factor1's
reindexed {11},{21} are fixed.

## My question
What is the cleanest Lean route that handles the per-layer frame WITHOUT a frame-block case analysis?
Two candidate routes:

ROUTE A (telescope/de-frame): rewrite prod(fpp p) = endpointP0·prod(rawTuple p)·endpointQL via the
  intrinsic telescope, where rawTuple p s = reindex⁻¹(fromBlocks (1+X) Y Z T) (so the RAW product has
  clean {11},{21} = Y,T-free, and {12} = e2_regPreserve). BUT framedLayer = corner + Pf·mid·Qf is NOT
  Pf·(·)·Qf (additive corner outside the frame) — so does an intrinsic de-framing telescope EXIST for
  framedParamsPivot, or does it require invertible Pf/Qf (which I do NOT have here)?

ROUTE B (difference is {22}-supported): prove
  reindex(prod(fpp ψq)) − reindex(prod(fpp q)) = factor0 · [factor1_ψ − factor1_q] reindexed, where
  factor1_ψ − factor1_q = Pf(last)·reindex⁻¹(fromBlocks 0 ΔY 0 ΔT)·Qf(last). Then show this difference
  has zero {11,12,21}. Does this need hPtri/hQtri (endpoint frame triangularity) on Pf(last)/Qf(last),
  or does the {11},{21}=0 of the inner fromBlocks(0 ΔY 0 ΔT) survive the per-layer frame + reindex?

Tell me: (1) which route is sound + cleanest; (2) does it need hPtri/hQtri threaded into THIS lemma
(currently it does not take them); (3) the exact step sequence (which banked lemma at each step).
If NEITHER route is clean and the lemma genuinely needs a framed-block {12} computation with frame
mixing, say so and give that computation's shape (it may need [Invertible (Pf last)] etc — flag it as
a NEW HYPOTHESIS requirement = a signature change the controller must know about).
</task>

<output_contract>
1. Route choice (A or B or "neither — needs X"), with the soundness reason in 2 sentences.
2. Whether hPtri/hQtri (or Pf/Qf invertibility) must be threaded into THIS agreement lemma. YES/NO.
3. The exact ordered step sequence (≤ 12 steps), each naming the banked lemma/tactic.
4. The single biggest cast risk + how to sidestep it (the doc notes finCongr_refl + reindex_refl_refl
   via erw, and prefix-induction reusing prodAux_succ — say which applies).
Under 450 words. Mark certainty vs inference.
</output_contract>

<grounding_rules>
No repo. If you cannot tell whether framedLayer de-frames without invertible Pf/Qf, say which fact to
check. The KEY decision I need: does this lemma need MORE hypotheses (hPtri/hQtri/invertibility) than
its current signature (which takes only H,r,hr,hL,hL2eq,J,Pf,Qf,q)? That is a signature change.
</grounding_rules>
