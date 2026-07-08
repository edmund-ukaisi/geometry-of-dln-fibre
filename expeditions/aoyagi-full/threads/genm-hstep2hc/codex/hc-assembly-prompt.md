<task>
Lean4/Mathlib formalisation, DLN-fibre RLCT project (v4.29 pin). I am closing the `hC` hypothesis of a
general-`L` keystone. Route + banked pieces are settled; I need a decorrelated verdict on the CLEANEST Lean
route for the two remaining hard pieces (a per-layer readback bridge "Claim-C", and the crux "Kcoup
frame-invariance"), and confirmation my cancellation algebra is correct.

## Objects (all banked, sorry-free)

Fix `H : Fin (L+1) → ℕ`, rank `r`, `hr : ∀ s, r ≤ H s`, `hL : 1 ≤ L`, `hL2 : 2 ≤ L`, `B`, `hB : B.rank = r`.
`J = frontEmbed H r hr`. Frames `Pf : (s:Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ`,
`Qf : (s:Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ`. Point `x : Fin (flatDim H) → ℝ`.
Let `w0 = paramsEquivFlat H (deepestPoint H r B hB hr hL)`, `q = deepestSplit H r hr hL w0 x` (the "split").
`decode x := (paramsEquivFlat H).symm x : Params H` (a family `Fin L → Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ`).

Two abstract chains (shape `Matrix (Fin r ⊕ Fin (chainWidth s − r)) (Fin r ⊕ Fin (chainWidth (s+1) − r)) ℝ`
at layer `s`, `chainWidth j := deepestChainWidth H j`):
- `D := deepestChain H r hr (decode x)`.
- `F := deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)`.
`deepestChain H r hr A s = reindex (deepestChainSplit s) (deepestChainSplit (s+1)) (deepestChainLayer A s)`,
`deepestChainSplit j = rThresholdSplit r (chainWidth j) _` (the `r ⊕ (·−r)` threshold split, an `Equiv`),
`deepestChainLayer A s = reindex (finCongr _) (finCongr _) (A ⟨s,_⟩)` for `s<L` (a pure width relabel).

## Banked facts

1. `framedParamsPivot_eq_frame_of_front` (given `hNF`,`hPfL`,`hcorner` frame-normal-form hyps): for ALL `s:Fin L`,
   `framedParamsPivot … q s = Pf s * (decode x) s * Qf s`.  [so `F s = reindex(deepestChainSplit)(deepestChainSplit)(Pf s · (decode x) s · Qf s)`]
2. `hInterior : ∀ s:Fin L, 0<s → s+1<L → Pf s = 1 ∧ Qf s = 1`. `hQf0 : Qf(firstLayer)=1`, `hPfL : Pf(lastLayer)=1`.
   Reindexed frame block conditions (over `rThresholdSplit`): `Pf 0` block-LOWER (`(reindex Pf0).toBlocks₁₂=0`,`₂₂=1`,`₁₁` Invertible);
   `Qf (last)` block-UPPER (`(reindex Qf_last).toBlocks₂₁=0`,`₂₂=1`,`₁₁` Invertible).
3. `psiSplitRawGen_deepestChain_hmove`: `deepestChain (framedParamsPivot (psiSplitRawGen q)) = movedC F (Z0edit0 F L)`.
4. `blockSchur_movedC : blockSchur (movedC C Z0e s) = schurTilde C s = (1 − Kcoup C s) * blockSchur (C s)`.
   `Kcoup C k = (C k).toBlocks₂₁ * Ring.inverse (partProd C (k+1)).toBlocks₁₁ * (partProd C k).toBlocks₁₂`.
   `partProd C 0 = 1`, `partProd C (k+1) = partProd C k * C k`. `Kcoup C 0 = 0` (banked `Kcoup_zero`).
5. `absorbedCoreConj_eq_blockSchur_synthetic` (step-A, banked): for any core/gauge slots pc,pg and `s:Fin L`,
   `coreRead pc s + schurCorrectionConj pg s = blockSchur (fromBlocks (deepBlkA_s + gaugeReadX pg s)(deepBlkY_s + gaugeReadY pg s)(deepBlkZ_s + gaugeReadZ pg s)(coreRead pc s))`.
6. Interior deepest-block facts (banked): `deepBlkA_interior_eq_one` (=1), `deepBlkY_interior_zero`, and my new `deepBlkZ_interior_zero`.
7. `deepestChain_framedParamsPivot_blocks_of_frame_one` (interior, frames=1): the framed chain layer's 4 blocks =
   `1 + gaugeReadX`, `reindex gaugeReadY`, `reindex gaugeReadZ`, `reindex coreRead` (reduced-width finCongr relabels).
8. Boundary Schur-invisibility (banked): `blockSchur_lowerFrame_left`: `blockSchur (fromBlocks P11 0 P21 1 · M) = blockSchur M`;
   `blockSchur_rightUpper_right`: `blockSchur (M · fromBlocks Q11 Q12 0 1) = blockSchur M`.
9. Boundary framed-chain decode (banked): `psiSplitRawGen_deepestChain_firstLayer` / `_lastLayer` give the moved framed chain's boundary layers as `frame · forcedDecode` blockwise.

## The target `hC` (verbatim, `s : Fin L`), with q = split x

`reindex (finCongr cc_s) (finCongr ss_s) ( coreRead(psiSplitRawGen q).2.1 s + schurCorrectionConj((psiSplitRawGen q).1,(psiSplitRawGen q).2.2) s )
  = blockSchur (movedC D (Z0edit0 D L) s)`.

## My route (please verify / correct / simplify)

Let `M_s^m := fromBlocks (deepBlkA_s + Xm)(deepBlkY_s + Ym)(deepBlkZ_s + Zm)(coreRead_moved)` where X/Y/Z/coreRead_moved
are the reads of the MOVED point `psiSplitRawGen q`. Step-A (fact 5) rewrites LHS-inner = `blockSchur M_s^m`.

- **Claim-C** (per `s`): `reindex (finCongr cc)(finCongr ss) (blockSchur M_s^m) = blockSchur (F' s)` where
  `F' := deepestChain (framedParamsPivot (psiSplitRawGen q))`. By hmove (fact 3), `F' = movedC F (Z0edit0 F L)`, so
  `blockSchur (F' s) = schurTilde F s`. Then LHS = `schurTilde F s = (1 − Kcoup F s)·blockSchur(F s)`.
  I intend to prove Claim-C per-layer: INTERIOR via fact 7 (F' blocks = 1+Xm, reindex Ym/Zm/coreRead) + fact 6 (deepBlk interior-zero) so `M_s^m` reindex-matches `F' s` and blockSchur commutes with the reduced-width reindex; BOUNDARY via fact 9 (F' boundary = frame · forcedDecode) + fact 8 (frame Schur-invisible) matching `blockSchur M_s^m` after the deepBlk-boundary reads combine. IS Claim-C the right target, and is the boundary case actually `blockSchur M_s^m` (reindexed) = `blockSchur(F' s)`, or does the deepBlk-boundary term break the match? Give the cleanest per-layer proof shape.

- **Lemma 4**: `blockSchur (F s) = blockSchur (D s)` (up to the finCongr reduced-width reindex). INTERIOR: F s = D s (fact 1 + hInterior). BOUNDARY: `F s = reindex(Pf s · D s · Qf s)`; Pf_0 block-lower / Qf_last block-upper, so blockSchur-invisible (fact 8). Confirm.

- **Lemma 5 (CRUX)**: `Kcoup F s = Kcoup D s` for all `s:Fin L`. My cancellation analysis:
  Because interior frames are 1 and only `Pf_0` (left, block-lower) and `Qf_{L-1}` (right, block-upper) survive,
  the partial products telescope: `partProd F k = reindex(Pf_0 · partProd D k)` for `k ≤ L−1`, and
  `partProd F L = reindex(Pf_0 · partProd D L · Qf_{L-1})`. Then for `1 ≤ k ≤ L−2` (interior layer, F k = D k):
  `Kcoup F k = (D k)₂₁ · (P11·(partProd D(k+1))₁₁)⁻¹ · (P11·(partProd D k)₁₂)` and the `P11` cancels between
  the two partial products ⟹ `= Kcoup D k`. For `k=0`: both sides 0 (`Kcoup_zero`). For `k=L−1` (last layer):
  `(F(L-1))₂₁ = (D_{L-1})₂₁·Q11`, `(partProd F L)₁₁ = P11·(partProd D L)₁₁·Q11`, `(partProd F(L-1))₁₂ = P11·(partProd D(L-1))₁₂`,
  so `Kcoup F(L-1) = (D_{L-1})₂₁·Q11·(P11·(PDL)₁₁·Q11)⁻¹·P11·(partProd D(L-1))₁₂ = Kcoup D(L-1)` (Q11 and P11 cancel).
  (a) Is this cancellation algebra correct (esp. the `(P11·X·Q11)⁻¹ = Q11⁻¹·X⁻¹·P11⁻¹` step needs P11,X,Q11 units)?
  (b) What is the CLEANEST Lean formalisation of the "partProd F k = frame · partProd D k · frame" telescoping —
      a direct induction on `k` (using `partProd (k+1) = partProd k · C k`, the block-multiply lemmas
      `toBlocks₁₁_mul/₁₂_mul/₂₁_mul`, and the interior `C k = D k`, boundary frame block structure)? Or is there a
      slicker invariant (e.g. carry `partProd F k = reindex(fromBlocks P11 0 P21 1) · reindex(partProd D k)` for k≤L−1
      as the induction hypothesis)? Give the induction hypothesis shape and the ~4 key rewrite steps.
  (c) Is `Ring.inverse` (total inverse) vs `⁻¹`/`Invertible` going to bite? All pivots are units at the deepest point;
      hypotheses `hP11inv`,`hQ11inv`, `hLayer`(layer pivots), `hPart`(partial pivots) are available as `Invertible`.

## Constraint
Reindex bookkeeping is the main friction (finCongr reduced-width relabels + the `deepestChainSplit` outer split).
Prefer doing reindex algebra at the equiv/`reindex_mul` level, never entrywise. `reindex` is multiplicative:
`reindex e1 e3 (A*B) = reindex e1 e2 A * reindex e2 e3 B`.
</task>

<output_contract>
Four terse sections:
1. Claim-C: is it the right per-layer target? Cleanest proof shape for interior and boundary. Flag any hidden gap (esp. does the deepBlk-boundary term in `M_s^m` break the boundary match with `blockSchur(F' s)`?).
2. Lemma 5 cancellation: correct? (yes/no + the one load-bearing step). Cleanest telescoping induction hypothesis + key rewrites.
3. Lemma 5 formalisation risks (Ring.inverse vs Invertible; the reindex relabels; which banked block-mul lemmas to use).
4. Any SIMPLER overall route you see that avoids either Claim-C or the explicit partProd telescoping (e.g. relate F to D as a single `movedC`/frame transform with a banked Kcoup-invariance). If none, say so.
</output_contract>

<grounding_rules>
Distinguish what you DERIVE from the given definitions/lemmas vs. what you INFER about repo internals you cannot see.
Do not invent Mathlib lemma names. If a step needs a fact I did not list as banked, say so explicitly.
</grounding_rules>
