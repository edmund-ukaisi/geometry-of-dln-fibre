Lean 4 / Mathlib v4.29. I'm filling the LAST sorry (S6, `comp_identity_L2`) of an L=2 diffeo-bridge. This is the genuine geometric content. GOAL (=ᶠ[nhds wstar], at L=2):

  (fun x => (∑ i, (regStraighten (split x)).1 i ^ 2) + deepestCoreF H r (coreAbsorb (split x)).2.1) ∘ psiL2
    =ᶠ[nhds wstar] Φscore

where Φscore x = (∑ i, (regStraighten (split x)).1 i ^ 2) + Score x. So I must show, near wstar:
  (A) reg term:  ∑ i, (regStraighten (split (psiL2 x))).1 i ^ 2  =  ∑ i, (regStraighten (split x)).1 i ^ 2
  (B) core term: deepestCoreF H r (coreAbsorb (split (psiL2 x))).2.1  =  Score x

LANDED facts I can use:
- `psiL2 =ᶠ[nhds wstar] psiRawL2` (S5 germ; χ=1 near wstar).
- `psiRawL2 x = (deepestSplit … wstar).symm (psiSplitRawL2 (deepestSplit … wstar x))` (def). And `hsplit : ∀ w, split w = deepestSplit … wstar w`. So `split (psiRawL2 x) = psiSplitRawL2 (split x)`.
- `psiSplitRawL2 = (L=2) psiSplitRawL2Core` (the REAL W⁻¹ joint (T1,Y1) action; edits last-layer core T1↦T1' and last-layer reg-read Y1↦Y1').
- `hregval : (regStraighten q).1 = deepestEFull H r hr hL J Pf Qf q` (the reg read = framed-product residual blocks (P00-1, P01, P10), via `framedParamsPivot`).
- `e2_regPreserve : A0*(Y1 + ⅟A0*Y0*(T1-T1')) + Y0*T1' = A0*Y1 + Y0*T1` (P01 fixed under the joint move).
- `hcoreabs : coreAbsorb = deepestCoreAbsorb` (= coreShearHomeo (schurCutoffShift); `(coreAbsorb q).2.1 = q.2.1 + schurCutoffShift (q.1,q.2.2)`).
- `deepestCoreF_coreAbsorb_eq_prodSchur` (on inner ball): `deepestCoreF (deepestCoreAbsorb q).2.1 = frobSq (prod (deepestM) (fun s => (paramsEquivFlat).symm q.2.1 s + schurCorrection (q.1,q.2.2) s))`.
- `prod_absorbed_eq_schur_ldu` (DeepestCompositionE1): the 2-layer LDU `(T0 - Z0⅟A0 Y0)*S1' = global Schur Rcore` where `S1' = (1-K)*S1`.
- `hScoreDef`: Score x = ∑∑ ((reindex (P0·(prod(symm x)-B)·QL)).toBlocks₂₂ - toBlocks₂₁ * (toBlocks₁₁+1)⁻¹ * toBlocks₁₂)² — i.e. the SCHUR COMPLEMENT of the framed loss matrix's (1,1)-corner.
- `hPtri/hQtri`: endpoint frames are block-triangular (P0 block-lower toBlocks₁₂=0, QL block-upper toBlocks₂₁=0).

KEY QUESTIONS:
1. For (A): the reg term equality. `regStraighten (split (psiRawL2 x)).1 = deepestEFull (psiSplitRawL2 (split x))`. The joint move edits (T1,Y1); `deepestEFull` reads (P00-1, P01, P10) of the framed pivot product. P00, P10 are T1,Y1-free (fixed); P01 fixed by e2_regPreserve. So `deepestEFull (psiSplitRawL2 q) = deepestEFull q`? Is that the clean statement (reg residual invariant under the joint move)? What's the cleanest Lean route — does it need the triangularity hPtri/hQtri to read P01 = A0*Y1+Y0*T1 from the FRAMED product (P0·∏·QL), or is the framed pivot product `framedParamsPivot` already in the gauge-aligned frame where P01 is directly A0*Y1+Y0*T1?
2. For (B): `deepestCoreF (deepestCoreAbsorb (psiSplitRawL2 q)).2.1 = Score x`. After psiSplitRawL2 the core slot is T1' (and the schurCorrection re-reads off the moved reg). Via `deepestCoreF_coreAbsorb_eq_prodSchur` this is `frobSq(prod(core' + schurCorrection'))`. The claim: this equals the Schur complement `Score`. Is the bridge: `prod(T1' + schurCorr') = the Schur-complement Rcore = P22 - P21(P11+1)⁻¹P12` (the `Score` summand), via `prod_absorbed_eq_schur_ldu`? Lay out the exact algebraic chain from `frobSq(prod(core'+schurCorr'))` to `Score x`, naming which landed lemma does each step.
3. Is this realistically ONE tide or should it be decomposed into 3-4 named sub-lemmas (reg-invariance; core = LDU Schur; the germ assembly)? Give the sub-lemma breakdown + the riskiest step.

Be concrete about the Lean lemma sequence and flag where the framed-product/triangularity bookkeeping or the `prod` (2-layer) vs `framedParamsPivot` mismatch will bite.
