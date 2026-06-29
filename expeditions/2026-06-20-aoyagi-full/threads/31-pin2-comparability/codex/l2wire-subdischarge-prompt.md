<task>
Lean 4 / Mathlib, DLN RLCT formalisation. I need the precise DISCHARGE construction for two per-`x`
hypotheses (`hsub3reg`, `hsub4core`) at a final wiring point. The two discharge LEMMAS already exist
(sorry-free); I must supply their hypotheses. Give me the construction recipe per hypothesis, flagging
which are one-liners vs which need a real sub-proof.

## Context
At a point in `deepest_gauge_construction` (L=2 branch), I have in scope (all concrete, from a bundle):
- `J : Fin r ↪ Fin (H (Fin.last L))` with `hJfront' : J = frontEmbed H r hr`
- `Pf`/`Qf` : the per-layer gauge frames (block-triangular at the boundary), with the bundle facts:
  `hPunit, hQunit, hQf0 (Qf firstLayer = 1), hPfL (Pf lastLayer = 1), hNF (Pf s · deepest s · Qf s =
  corM for s+1≠L), hcorner, hPtri/hQtri (endpoint block-triangularity), hinterface (interior frames
  trivial)`.
- `split := deepestSplit H r hr hL w0` (an Equiv; `w0 := paramsEquivFlat (deepestPoint …)`), `hsplit : ∀
  w, split w = deepestSplit … w0 w`.
- A LANDED §iii lemma `framedParamsPivot_eq_frame_of_front`:
    `framedParamsPivot H r hr hL J Pf Qf (deepestSplit … w0 w) s = Pf s * ((paramsEquivFlat H).symm w) s
     * Qf s`  (given hJfront/hNF/hcorner/hPfL).
- `e2_regPreserve` (abstract): `A0*(Y1 + ⅟A0*Y0*(T1−T1')) + Y0*T1' = A0*Y1 + Y0*T1`.
- `psiSplitRawL2 H r hr hL : DeepestSplit → DeepestSplit` (the joint (T1,Y1) move; at L=2 = the cutoff
  joint action).

## DISCHARGE 1 — hsub3reg (∀ x, ∑ deepestEFull(psiSplitRawL2(split x))² = ∑ deepestEFull(split x)²)
via lemma `deepestEFull_sq_sum_psiSplitRawL2_eq` whose hyps (for a fixed `q := split x`) are:
- hPtri/hQtri (have them, modulo a bounded endpoint cast)
- `q`, `B`
- `Aψ Aq : Params H`
- `hframeψ : ∀ s, framedParamsPivot … (psiSplitRawL2 … q) s = Pf s * Aψ s * Qf s`
- `hframeq  : ∀ s, framedParamsPivot … q s = Pf s * Aq s * Qf s`
- `hinterface` (have it)
- `hS3b : reindex(rThr, pivotThr J)(endpointP0·B·endpointQL) = fromBlocks 1 0 0 0`
- `hm11/hm12/hm21 : (reindex(prod H Aψ)).toBlocksᵢⱼ = (reindex(prod H Aq)).toBlocksᵢⱼ` for ij∈{11,12,21}

Q for DISCHARGE 1: 
(a) What are the right `Aψ`/`Aq`? (I believe `Aq := (paramsEquivFlat H).symm x` since `split x =
    deepestSplit w0 x`; and `Aψ := (paramsEquivFlat H).symm ((split).symm (psiSplitRawL2 (split x)))`
    since `split` is an Equiv — so `psiSplitRawL2 (split x) = deepestSplit w0 ((split).symm (psiSplitRawL2
    (split x)))`.) Confirm or correct.
(b) Then `hframeψ`/`hframeq` are DIRECT applications of §iii `framedParamsPivot_eq_frame_of_front` at
    `w := (split).symm (psiSplitRawL2 (split x))` resp. `w := x`. Confirm.
(c) `hS3b`: `reindex(endpointP0·B·endpointQL) = fromBlocks 1 0 0 0`. Is this derivable from `hcorner`
    (the bundle's last-layer corner `reindex(deepest_last · Qf_last) = fromBlocks 1 0 0 0`) + the
    endpoint-telescoping / `hframe`? Sketch the cheapest route.
(d) `hm11/hm12/hm21` (the raw-middle block agreement of `prod Aψ` vs `prod Aq`): this is where
    `e2_regPreserve` enters. How does the abstract e2_regPreserve give the three block equalities for the
    L=2 joint move (Aψ = the (T1,Y1)-moved Aq)? Is there a per-layer route?

## DISCHARGE 2 — hsub4core (∀ x, deepestCoreF (deepestCoreAbsorb (psiSplitRawL2 (split x))).2.1 = Score x)
via lemma `deepestCoreF_coreAbsorb_psiSplitRawL2_eq_score` (Option-2 form) whose hyps (q := split x):
- hPtri/hQtri, hScoreDef, `hq : q = deepestSplit … x`, `hball : psiSplitRawL2 q ∈ closedBall 0 rIn`
- `hWdet : (l2W … q).det ≠ 0`
- `hLDUtie : prod (deepestM) (cleaned c'' tuple, Function.update form) = Score-(1,1)-Schur-integrand`
Q for DISCHARGE 2:
(e) `hWdet`: from `hball` + a radius coupling (`ball_l2ExtraRadius_subset` + `cutoffBump.rIn ≤
    l2ExtraRadius` + q-membership). Sketch the chain `psiSplitRawL2 q ∈ ball rIn → det (l2W q) ≠ 0`.
(f) `hLDUtie` (the kill-condition risk): the cleaned tuple's reduced product = the Score Schur integrand,
    via `rcore_schur_factor_of_corner_split` (on hS3b's corner-split) + the decode-`x` readback ties.
    Is this a genuine new ~100-LoC proof, or assembled from banked pieces? What's the load-bearing step
    that could WALL (vs bounded assembly)?
</task>

<output_contract>
For EACH of (a)-(f): a 2-4 line answer — the construction (lemma names from the context + the key
rewrite), OR "needs a real sub-proof: <what>". Rank (a)-(f) by risk (which is most likely to wall).
End with: is hsub3reg + hsub4core BOUNDED (banked pieces + cast/assembly) or does hLDUtie/(f) carry a
genuine new-math wall? One sentence.
</output_contract>

<grounding_rules>
Reason from the structure I gave; mark any step you can't determine from the context as "(unverified —
need to read <lemma>)". Don't invent lemma names beyond those I listed. If (a)/(b) (the Aψ/Aq + §iii
route) is wrong, say so plainly — that's the foundation of hsub3reg.
</grounding_rules>
