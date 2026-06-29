<task>
Lean4/Mathlib v4.29. Give me the cast-correct TACTIC skeleton for sub-4's STEP 3-4 (the LDU +
frame-transform tail). I have STEP 1-2 banked + all helpers; I need the assembly to avoid thrash.

## Goal (after STEP 1-2, inside `deepestCoreF_coreAbsorb_psiSplitRawL2_eq_score`)
After `rw [hstepA]` the goal is:
  frobSq (prod (deepestM H r) c) = Score x
where `c s = decode(ψq).2.1 s + schurCorrection(ψq) s` (the per-layer absorbed Schur cores), and:
- hclast : c (lastLayer hL) = (1 − l2K q) * l2S1 q     [BANKED]
- hc0    : ∀ s ≠ lastLayer, c s = decode(q).2.1 s + schurCorr(q) s   [BANKED]
- hWdet  : (l2W q).det ≠ 0    [threaded input]
- hL2 : L = 2.  frobSq M = ∑ᵢⱼ (M i j)².

## Score (hScoreDef, the target)
Score x = ∑ᵢ∑ⱼ ( (reindex(rThr,pivotThr J)(Mw)).toBlocks₂₂
   − (reindex Mw).toBlocks₂₁ · ((reindex Mw).toBlocks₁₁ + 1)⁻¹ · (reindex Mw).toBlocks₁₂ )ᵢⱼ ²
where Mw := endpointP0·(prod ((paramsEquivFlat H).symm x) − B)·endpointQL.
NOTE Score = frobSq( the (1,1)-Schur of reindex(Mw) with the `+1` pivot ) — EXACTLY the LHS of the
banked `rcore_schur_factor_of_corner_split` (below).

## Banked helpers
- `prod_deepestM_eq_two_of_L2 (H : Fin 3) (C : Params (L:=2) (deepestM H r)) :
    prod (deepestM H r) C = reindex(finCongr rfl)(finCongr rfl)(C 0) * reindex(…)(…)(C 1)`  (L=2 peel).
- `rcore_schur_factor_of_corner_split (Mw Mhat eR eMid eC G0 G1) (hGG : Mhat = G0*G1)
    (hsplit : reindex eR eC Mhat = fromBlocks 1 0 0 0 + reindex eR eC Mw)
    [Inv (reindex eR eMid G0).₁₁] [Inv (reindex eMid eC G1).₁₁] [Inv (reindex eR eC (G0*G1)).₁₁] :
    (reindex eR eC Mw).₂₂ − (reindex Mw).₂₁·((reindex Mw).₁₁+1)⁻¹·(reindex Mw).₁₂
      = (Ŝ0)·(1 − K̂)·(Ŝ1)`
  where Ŝ0 = (reindex eR eMid G0).₂₂ − .₂₁·(.₁₁)⁻¹·.₁₂, similarly Ŝ1 from G1, K̂ = (reindex eMid eC G1).₂₁·((reindex(G0*G1)).₁₁)⁻¹·(reindex eR eMid G0).₁₂.
  i.e. Score's integrand (LHS) = the two-layer LDU `Ŝ0·(1−K̂)·Ŝ1`.
- `schur_frame_transform` (block-lower P, block-upper Q): Schur₂₂(P·M·Q) = DP·Schur₂₂(M)·DQ; with DP=DQ=1 (hPbr/hQbr) = Schur₂₂(M).
- The decode-x readback ties (THREADED inputs, controller discharges): the per-factor Schur cores Ŝ0/Ŝ1/K̂
  read off Mhat = endpointP0·prod(decode x)·endpointQL's two framed layers EQUAL the l2-named blocks, and
  in particular Ŝ0·(1−K̂)·Ŝ1 = c0·c1 = (decode(q) layer-0 core S0)·((1−l2K q)·l2S1 q) = prod(deepestM) c.

## The math (CONFIRM + give the Lean)
Score x = frobSq(Schur₂₂(reindex Mw))                         [hScoreDef + frobSq def: Score = frobSq(that integrand)]
        = frobSq(Ŝ0·(1−K̂)·Ŝ1)                                [rcore_schur_factor_of_corner_split, with the corner-split hsplit (hS3b-derived) + grouping Mhat=G0·G1 (prod_eq peel of decode x) + 3 pivot Invs]
        = frobSq(prod(deepestM) c)                            [the readback-tie: Ŝ0·(1−K̂)·Ŝ1 = c0·c1 = prod(deepestM) c via prod_deepestM_eq_two_of_L2 + hclast/hc0]
So the goal `frobSq(prod(deepestM) c) = Score x` closes by chaining these (reversed).

## Questions
1. Confirm the chain + the exact `rw`/`exact` sequence to close `frobSq(prod(deepestM) c) = Score x`.
   Specifically: do I (a) `rw [hScoreDef]` then `rw [frobSq]`/unfold to expose Score = frobSq(integrand),
   (b) rewrite the integrand via `rcore_schur_factor_of_corner_split` to `Ŝ0·(1−K̂)·Ŝ1`, (c) rewrite that
   to `prod(deepestM) c` via the readback-tie + `prod_deepestM_eq_two_of_L2` + hclast/hc0? Or cleaner to
   go forward from the LHS?
2. The frobSq is `∑∑(·)²` not a matrix eq — so I need the MATRICES equal, then `frobSq` congr. Is
   `frobSq` a plain function (so `congrArg frobSq hMatEq` works), or do I `rw` the matrix eq under the ∑∑?
3. The 3 pivot Invertible instances for rcore_schur_factor — these are det≠0 facts (hWdet gives one;
   the others = decode-x layer pivots). Thread as `[Invertible …]` instance args or as `det ≠ 0` hyps
   + `Ne.isUnit`/`invertibleOfIsUnit`? Which is cleaner for a threaded-input contract?
4. Biggest cast risk: prod_deepestM_eq_two_of_L2's finCongr layer reindexes (deepestM widths) vs
   rcore_schur_factor's eR/eMid/eC. How to make `prod(deepestM) c = G0·G1` line up with the helper's
   `Mhat = G0·G1` grouping? (doc: finCongr_refl + reindex_refl_refl via erw.)
</task>

<output_contract>
1. CONFIRM the chain (or correct it) + the exact ordered tactic sequence (≤ 15 lines) to close the goal,
   naming each banked lemma.
2. Answer Q2 (frobSq congr), Q3 (Invertible threading), Q4 (the finCongr/eMid alignment) concretely.
3. Flag any step that is NOT covered by the listed banked helpers (i.e. genuinely missing) — esp. whether
   `schur_frame_transform` is even needed (I suspect rcore_schur_factor already bridges Score's integrand
   to the LDU, making schur_frame_transform redundant here — confirm).
Under 500 words. Mark certainty vs inference.
</output_contract>

<grounding_rules>
No repo. If a step needs a fact not in the listed helpers, name it. Distinguish "mechanical given the
helpers" from "needs a new lemma". The threaded readback-tie + hPbr/hQbr/hS3b/hWdet are INPUTS (the
controller discharges) — so "thread it as a hyp" is the answer for anything producer-internal.
</grounding_rules>
