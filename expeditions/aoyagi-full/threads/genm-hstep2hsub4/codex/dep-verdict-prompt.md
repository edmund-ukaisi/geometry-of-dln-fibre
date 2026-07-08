<task>
Lean4/Mathlib formalisation, DLN-fibre RLCT project. I must build the general-L `hsub4core`
germ for #120 `hstep2`, mirroring a landed L=2 template. I've concluded the FULL germ needs an
UN-BUILT dependency; I need an independent decorrelated check of that verdict + a route read on
the parallel-buildable piece.

BACKGROUND OBJECTS (all `H : Fin (L+1) → ℕ`, rank r, `hr : ∀ s, r ≤ H s`, `hL : 1 ≤ L`):
- `deepestCoreF H r y := dlnLoss (deepestM H r) 0 (decode y) = frobSqMat (prod (deepestM H r) (decode y))`
  where decode = `(paramsEquivFlat (deepestM H r)).symm`. (‖ reduced-core product ‖².)
- `deepestCoreAbsorbConj H r B … hDA : DeepestSplit ≃ₜ DeepestSplit` — a homeomorphism whose CORE slot
  `.2.1` adds a CUTOFF shift: `(deepestCoreAbsorbConj q).2.1 = q.2.1 + schurCutoffShiftConj (q.1,q.2.2)`.
  The cutoff `schurCutoffShiftConj` equals the RAW Schur shift `schurShiftRawConj` (decodes to
  `schurCorrectionConj`, the actual `−Z·A⁻¹·Y` Schur correction) ONLY on an inner ball
  `closedBall 0 (cutoffBumpConj …).rIn`; off the ball a bump smoothly turns it off (so the map is a
  GLOBAL homeo despite the inverses `A⁻¹` blowing up at singular points).
- `psiSplitRawGen H r hr hL J Pf Qf : DeepestSplit → DeepestSplit` — the concrete general-L joint move
  (Producer 1's map). Its core slot decodes to `(psiReadBlk … q s).toBlocks₂₂`.
- `split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit`, with `split basepoint = 0`.
- `Score x := frobSqMat (<framed (1,1)-Schur integrand over reindex(endpointP0·(prod(decode x)−B)·endpointQL)>)`.

THE GERM TARGET (fully-closed, mirroring the L=2 landed `hsub4core_conj_germ`):
  `∀ᶠ x in 𝓝 basepoint, deepestCoreF H r (deepestCoreAbsorbConj H r B … (psiSplitRawGen … (split x))).2.1 = Score x`

BANKED (sorry-free, general-L):
- `deepestCoreF_coreAbsorbConj_eq_prodSchur` : GIVEN `hq : q ∈ closedBall 0 (cutoffBumpConj).rIn`,
  `deepestCoreF (deepestCoreAbsorbConj q).2.1 = frobSqMat (prod (deepestM) (fun s => decode(q.2.1) s + schurCorrectionConj (q.1,q.2.2) s))`.
  (STRIPS the cutoff to the raw correction — this is WHY it needs `hq` the ball membership.)
- `prod_deepestM_eq_schur_ldu_readback_gen` : GIVEN a reduced-core tuple `C` with per-layer readback
  `hC : reindex (C s) = blockSchur (movedC (deepestChain (decode x)) (Z0edit0 …) s)`, plus chain-invertibility
  `hLayer`/`hPart` (about `deepestChain (decode x)`) and frame hyps, `prod (deepestM) C = <Score integrand matrix>`.
- `absorbedCoreConj_eq_schurCore` (general-L but BOUNDARY-only, needs `deepBlkT_s = 0`): the UNMOVED core readback.
- `psiSplitRawGen_deepestChain_hmove` : `deepestChain (framedParamsPivot (psiSplitRawGen q)) = movedC (deepestChain (framedParamsPivot q)) (Z0edit0 …)`. (FRAMEDPARAMSPIVOT chain, not raw decode.)
- `DeepestChainUnitGerm`: eventual-IsUnit germs `∀ᶠ x, IsUnit (deepestChain (framedParamsPivot (split x)) k).toBlocks₁₁)` etc. — for the FRAMED chain. Producer-1-FREE (continuous in x via split + framedParamsPivot).
- The landed sibling `hsub3reg_gen_germ` (reg side): its identity `∑ deepestEFull(psiSplitRawGen(split x))² = ∑ deepestEFull(split x)²` is POINTWISE-algebraic (via `deepestEFull_sq_sum_eq_of_chain_movedC` + hmove); it has NO cutoff, so it needs NO ball, hence NO `psiSplitRawGen` continuity — only the eventual unit germs.

NOT banked anywhere (I grepped the whole tree): `psiSplitRawGen 0 = 0` (only building blocks toward it exist
in `DeepestPsiTripleGen`: `movedC_eq_self_of_toBlocks₂₁_zero`, `framedLayer_zero`); ANY continuity / ContDiff /
Tendsto / HasFDerivAt of `psiSplitRawGen`. These are "Producer 1" (the un-built diffeo triple).

THE L=2 TEMPLATE (`hsub4core_conj_germ`) discharged its cutoff-ball germ `hqgerm`
(`psiSplitRawL2CoreConj (split x) ∈ ball` for x near basepoint) via `htend_psi` = Tendsto of
`psiSplitRawL2CoreConj ∘ split` at basepoint, which came from the L=2 producer's `HasStrictFDerivAt …
psiSplitDeltaL2CoreConj … 0` (continuity at 0) + `psiSplitRawL2CoreConj 0 = 0`. Its OTHER germs
(`hA0/hA1/hMid` invertibility) came from decode continuity (Producer-1-free).

MY VERDICT (check this):
(V1) The FULL germ requires the `hq` cutoff-ball peel over a nbhd of basepoint, which needs
     continuity of `x ↦ psiSplitRawGen (split x)` at basepoint + `psiSplitRawGen 0 = 0`. Both are
     Producer-1 pieces, un-built. So the FULL germ SEQUENCES AFTER Producer 1 — it is NOT parallel.
(V2) The Producer-1-FREE parallel content is the per-x KEYSTONE (general analog of the landed
     `deepestCoreF_coreAbsorbConj_psiSplitRawL2CoreConj_eq_score_at_chart`): take `hq` + `hLayer`/`hPart`/
     `hMid11inv` + frame hyps as HYPOTHESES, prove `= Score x`. Its new content is the general `hC`
     core-readback: `reindex(C s) = blockSchur (movedC (deepestChain (decode x)) …)` where
     `C s = (psiReadBlk (split x) s).toBlocks₂₂ + schurCorrectionConj(moved reads) s`.
(V3) That `hC` readback is NOT the banked `absorbedCoreConj_eq_schurCore` (which is unmoved + boundary-only)
     and NOT directly the banked hmove (which uses the FRAMEDPARAMSPIVOT chain, not raw `decode x`). It
     needs either a framed-vs-decode chain reconciliation OR a direct `psiReadBlk → movedC(deepestChain(decode x))`
     derivation. I judge this a substantial (~300-600 line) new construction, not bounded plumbing.
</task>

<output_contract>
Four short sections, terse:
1. VERDICT on V1 (agree/disagree + the single load-bearing reason). Is there ANY way to discharge the
   `hq` cutoff-ball germ over a neighbourhood WITHOUT `psiSplitRawGen` continuity-at-basepoint? (e.g. a
   cutoff-free variant of `deepestCoreF_coreAbsorbConj_eq_prodSchur`, or making `Score` absorb the cutoff.)
   If none, confirm the FULL germ sequences after Producer 1.
2. VERDICT on V2: is the per-x KEYSTONE genuinely Producer-1-free and the right parallel deliverable?
3. VERDICT on V3: is the `hC` readback reachable from banked pieces, or genuinely new math? Cheapest route.
4. RECOMMENDATION: given a parallel formalisation thread that must not idle — build the keystone now, or
   report the Producer-1 sequencing blocker and stand down? One-paragraph justification.
</output_contract>

<grounding_rules>
Distinguish what you can DERIVE from the objects/signatures I gave vs. what you're INFERRING about the
repo you cannot see. Flag any step where you're guessing a lemma exists. Do not invent Mathlib lemma names.
</grounding_rules>
