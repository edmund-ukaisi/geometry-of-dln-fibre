<task>
Lean 4 + Mathlib v4.29 formalisation. I am closing the general-L "hmove" boundary half of a DLN-fibre
proof. The INTERIOR half is already proven; I need the same result for the two boundary layers
(firstLayer, lastLayer). I want you to red-team my proof PLAN and pick the cleanest whole-matrix route
to avoid a per-block cast grind.

## Objects (all real matrices; `reindex e1 e2 M = M.submatrix e1.symm e2.symm`)

* `deepestChain A s : Matrix (Fin r ⊕ Fin (cw s - r)) (Fin r ⊕ Fin (cw (s+1) - r)) ℝ`
  `= reindex (chainSplit s) (chainSplit (s+1)) (deepestChainLayer A s)`,
  where for `s < L`: `deepestChainLayer A s = reindex (finCongr castSucc) (finCongr succ) (A ⟨s,_⟩)`
  (a DLN parameter-tuple layer, `A : Params H`), and `chainSplit s = rThresholdSplit r (cw s)` is the
  `r ⊕ (·-r)` block split. `cw s = deepestChainWidth H s`.

* `framedParamsPivot ... q : Params H`. For a NON-last layer `s`,
  `framedParamsPivot q s = framedParams q s = framedLayer (Pf s) (Qf s) X Y Z T`, where
  `framedLayer P Q X Y Z T = reindex e_r.symm e_c.symm (fromBlocks 1 0 0 0) + P * reindex e_r.symm e_c.symm (fromBlocks X Y Z T) * Q`
  with `e_r = rThresholdSplit r (H s.castSucc)`, `e_c = rThresholdSplit r (H s.succ)`, and
  `(X,Y,Z,T)` are the four gauge/core "reads" of `q` at layer `s`. For the moved point
  `q = psiSplitRawGen q0` these reads round-trip (already-proven lemmas) to the four `toBlocks` of a
  chain-width matrix `psiGhat q0 s`.

* At firstLayer: `Qf firstLayer = 1` (given), `Pf firstLayer` is block-LOWER: reindex-to-threshold
  `Pt := reindex e_r e_r (Pf firstLayer)` has `Pt.toBlocks₁₂ = 0`, `Pt.toBlocks₂₂ = 1`, and `Pt.toBlocks₁₁`
  is a unit (`Pf firstLayer` is a unit). `psiFrame0` is defined as `Pt` transported to chain-width
  `r ⊕ (cw firstLayer - r)` via `deepestChainSplit ∘ finCongr`.

* `psiGhat q0 firstLayer = forcedDecodeLeft psiFrame0 (movedC ... firstLayer - fromBlocks 1 0 0 0)`
  where `forcedDecodeLeft F D = fromBlocks (Pinv*A) (Pinv*Y) (Z - F₂₁*(Pinv*A)) (T - F₂₁*(Pinv*Y))`,
  `A,Y,Z,T = D.toBlocks`, `Pinv = Ring.inverse F.toBlocks₁₁`.

* Already-proven BANKED lemma (frame move):
  `fromBlocks_lowerFrame_mul_forcedDecode : P11*Pinv = 1 →`
  `fromBlocks P11 0 P21 1 * fromBlocks (Pinv*A)(Pinv*Y)(Z-P21*(Pinv*A))(T-P21*(Pinv*Y)) = fromBlocks A Y Z T`.

* The INTERIOR decode (already proven, frame-trivial P=Q=1) works by proving
  `framedParamsPivot_frame_one_eq : framedParamsPivot q s = reindex e_r.symm e_c.symm (fromBlocks (1+X) Y Z T)`
  then decoding each of the 4 `toBlocks` of `deepestChain` via helper lemmas
  `rThr_finCongr_split_inl/inr : (rThr a) (finCongr.symm ((rThr b).symm (inl i))) = inl i` etc.

## Goal (firstLayer)

Prove `deepestChain (framedParamsPivot (psiSplitRawGen q0)) (firstLayer : ℕ)
     = movedC (deepestChain (framedParamsPivot q0)) (Z0edit0 ...) (firstLayer : ℕ)`.

## My PLAN

Step A. A frame-KEEPING analog of `framedParamsPivot_frame_one_eq` for firstLayer (Q=1, any P):
  `framedParamsPivot q firstLayer = reindex e_r.symm e_c.symm (fromBlocks 1 0 0 0 + Pt * fromBlocks X Y Z T)`,
  using the algebra `P * reindex e_r.symm e_c.symm M = reindex e_r.symm e_c.symm (reindex e_r e_r P * M)`
  (P square on the shared middle index `H castSucc`, split by e_r).

Step B. Reindex to chain-width, collapsing to
  `Cψ(firstLayer) = fromBlocks 1 0 0 0 + psiFrame0 * psiGhat q0 firstLayer`
  (chain-width). The `reindex(chainSplit∘finCongr)(reindex e_r.symm (...))` composite is exactly the
  interior `rThr_finCongr_split_*` collapse; `psiFrame0 = reindex(chain-split∘finCongr) Pt` and the reads
  round-trip to `psiGhat`'s blocks.

Step C. `psiFrame0 = fromBlocks psiFrame0₁₁ 0 psiFrame0₂₁ 1` (block-lower + ₂₂=1, via `fromBlocks_toBlocks`),
  `psiFrame0₁₁ * Ring.inverse psiFrame0₁₁ = 1` (unit, via `Ring.mul_inverse_cancel`), then
  `fromBlocks_lowerFrame_mul_forcedDecode` gives `psiFrame0 * psiGhat q0 firstLayer = movedC(firstLayer) - fromBlocks 1 0 0 0`.

Step D. `fromBlocks 1 0 0 0 + (movedC(firstLayer) - fromBlocks 1 0 0 0) = movedC(firstLayer)` by `abel`.
</task>

<output_contract>
1. VERDICT: is this plan sound? Any step that will not go through as stated?
2. Step B is the cast-grind risk. Give the single cleanest tactic strategy for the reindex collapse:
   should I (i) do it whole-matrix via `Matrix.submatrix_mul_equiv` / `reindex_mul_split_gen`, or
   (ii) prove `Cψ(firstLayer)` block-by-block like the interior decode then reassemble via
   `fromBlocks_toBlocks`? Name the specific Mathlib v4.29 lemmas.
3. Is there a SIMPLER overall route I am missing (e.g. avoiding Step A entirely by decoding
   `deepestChain` blocks directly, or expressing the whole layer as a single `reindex` of a product)?
4. Any trap with `Ring.inverse` vs `⁻¹`, or with `movedC(firstLayer)` living in chain-width vs the
   reads living in H-width, that will bite the block-reassembly?
Keep it under ~400 words. Flag inference vs certainty.
</output_contract>

<grounding_rules>
You do not have the repo. Reason from the signatures given. If a step depends on a lemma whose exact
form you cannot verify, say so and mark it as "needs local check" rather than asserting it exists.
</grounding_rules>
