<task>
Lean 4 + Mathlib (v4.29). I must prove the CONJUGATED "hm" mid-block agreement (the long-pole sub-proof
of a deep-linear-network RLCT formalisation). The BARE analogue was route-mapped but NEVER completed, so
I want the cleanest route before investing. All named lemmas below EXIST and are GREEN (banked).

SETTING. L=2 (a 2-layer product). `prod H A` is a 2-factor matrix product of the per-layer matrices
`A 0`, `A 1` (each square-ish, reindexed into r ⊕ (·−r) block shape). `reindex eR eC M` = M.submatrix
eR.symm eC.symm; `.toBlocks₁₁/₁₂/₂₁/₂₂` are the four blocks. `eR = rThresholdSplit r (H 0)`,
`eC = pivotThresholdSplit r (H 2) J`, middle split `eMid = rThr/pivot on H 1`.

GOAL (three lemmas, the conj "hm"):
For `Aψ := (paramsEquivFlat H).symm (split.symm (psiSplitRawL2CoreConj … (split x)))` and
`Aq := (paramsEquivFlat H).symm x`, prove:
  (reindex eR eC (prod H Aψ)).toBlocks₁₁ = (reindex eR eC (prod H Aq)).toBlocks₁₁   -- hm11
  …₁₂ = …₁₂   -- hm12
  …₂₁ = …₂₁   -- hm21
Then `deepestEFull_sq_sum_psiSplitRawL2CoreConj_eq` follows by calling the EXISTING #147
`deepestEFull_sq_sum_psiSplitRawL2_eq` (it is psi-AGNOSTIC: it takes Aψ Aq + frame identities + hm11/12/21).

BANKED TOOLS (all GREEN):
1. `reindex_prod_regBlocks_eq_of_e2 eR eMid eC G0 G1ψ G1q G1ψ' G1q' (h11G) (h21G) (he2)` : for a SHARED
   first factor G0, if reindexed last factors agree on toBlocks₁₁ (h11G) and toBlocks₂₁ (h21G), AND satisfy
   the e2 relation `G0₁₁·G1ψ'₁₂ + G0₁₂·G1ψ'₂₂ = G0₁₁·G1q'₁₂ + G0₁₂·G1q'₂₂` (he2), then reindex(G0·G1ψ') and
   reindex(G0·G1q') agree on {11,12,21}. [This is EXACTLY the engine for the goal once the product is a 2-factor G0·G1.]
2. `prod_eq_prodAux_mul_last`/`prodDecode_eq_two_of_L2`: `prod H A = reindex(A 0) · reindex(A 1)` at L=2.
3. Conj read-transport (the move ψ_conj fixes everything except last-layer Y-tag + last-layer core):
   - `readX_psiSplitRawL2CoreConj_eq`, `readZ_psiSplitRawL2CoreConj_eq` : readX/readZ(ψq) = readX/readZ(q) ALL layers.
   - `readY_psiSplitRawL2CoreConj_of_ne_eq` : readY(ψq)_s = readY(q)_s for s ≠ last.
   - `readY_psiSplitRawL2CoreConj_last_eq` : readY(ψq)_last = l2Y1pReadConj q (the MOVED last-Y).
   - `coreRead_psiSplitRawL2CoreConj_of_ne` : core(ψq)_s = core(q)_s for s ≠ last.
   - `coreRead_psiSplitRawL2CoreConj_last` : core(ψq)_last = l2T1pConj q (the MOVED last-core).
   - `framedParamsPivot_psiSplitRawL2CoreConj_of_ne` : framedParamsPivot(ψq)_s = framedParamsPivot(q)_s for s≠last.
4. `framedParamsPivot_eq_frame_of_front … w s : framedParamsPivot (deepestSplit w0 w) s = Pf s · (decode w) s · Qf s`
   (the §iii frame identity — gives, for any flat point w, the framed layer = Pf·(decoded raw layer)·Qf).
5. The conj keystone `l2T1pConj_sub_Z1A1invY1pConj_eq` : `T1'c − Z1c·A1c⁻¹·Y1'c = (1−Kc)·S1c`, and
   `e2_regPreserve A0 Y0 Y1 T1 T1' : A0·(Y1 + ⅟A0·Y0·(T1−T1')) + Y0·T1' = A0·Y1 + Y0·T1` (the {12}-leak-kill).
6. `reindex_decode_split_blocks`: `reindex(decode x)_s = reindex(deepest)_s + fromBlocks(readX,readY,readZ,core)(split x)_s`.
   `reindex_mul_fromBlocks` reads a 2-factor reindexed product's blocks off the two factors' blocks.

THE CRUX (where I want the route pinned). The bare route map says:
  step1: layer-0 SHARED (Aψ 0 = Aq 0) — via framedParamsPivot_…_of_ne + frame ids + cancel unit frames.
  step2: 2-factor unfold both products; G0 = reindex(Aψ 0) = reindex(Aq 0).
  step3: layer-1 X/Z fixed (readX/readZ-fixed ⟹ A1,Z1 agree = h11G/h21G); {12}-leak via e2 (the moved Y1/T1
         satisfy the e2 relation by e2_regPreserve + the conj Y1p/T1p reads). Feed reindex_prod_regBlocks_eq_of_e2.
The friction I anticipate: (a) connecting the DECODED raw layers `Aψ s`/`Aq s` (via paramsEquivFlat.symm)
to the read-transport lemmas (which are about ψ_conj's gauge/core slots, NOT decode), and (b) the e2 input
`he2` is about the FRAMED reindexed blocks but the reads/keystone are about the deepest-block dictionary
(deepBlkA+readX etc.) — there's a layer of "reindex(decode)_s blocks = deepBlk·+read·" (reindex_decode_split_blocks)
to bridge. The widths/casts (H 1 middle, pivotJSucc J vs J) are a known cast-friction source.

<output_contract>
Give, concisely:
1. The CLEANEST proof skeleton for the three hm lemmas — as a numbered sequence of Lean `have` steps
   (state each have's goal precisely), identifying which banked lemma discharges each. Prefer reusing
   `reindex_prod_regBlocks_eq_of_e2` over re-deriving block algebra.
2. The SINGLE biggest risk/friction point and how to sidestep it (e.g. should I work with DECODED layers
   `Aψ s` directly, or pivot to the FRAMED `framedParamsPivot` and use a framed-block lemma? Which avoids
   the most cast pain?).
3. Whether to prove hm11/hm12/hm21 as a SINGLE conjunction (one reindex_prod_regBlocks_eq_of_e2 call
   yielding all three) or three separate lemmas.
4. Any cheaper alternative route I'm missing that sidesteps the decode↔read bridge entirely
   (e.g. proving the framed products `prod(framedParamsPivot(ψq))` vs `prod(framedParamsPivot q)` agree on
   reg blocks DIRECTLY, since #147 actually consumes the frame identities — could the hm be stated/proved
   at the framedParamsPivot level instead of the raw decode level?).
</output_contract>

<grounding_rules>
You may assume the named lemmas exist with the signatures described (I verified them). Flag any step where
your suggested lemma name/shape is an INFERENCE (you're guessing it exists) vs grounded in what I gave you.
Do NOT emit long tactic blocks — I want the DIAGNOSIS and the step skeleton, not code I'd paste blindly.
Be explicit about the e2 `he2` obligation's exact matrix shape and which keystone lemma closes it.
</grounding_rules>
