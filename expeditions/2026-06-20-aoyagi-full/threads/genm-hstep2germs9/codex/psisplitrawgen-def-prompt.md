<task>
I am formalising in Lean 4 / Mathlib (v4.29). I need to DEFINE a function `psiSplitRawGen`
and I want the cleanest definition that makes a downstream equality `hmove` provable.
This is pure design/strategy — no need to write Lean, just adjudicate the definition shape
and flag any obstruction.

## Objects (all exist, sorry-free)

Widths: `H : Fin (L+1) → ℕ`, rank `r`, `hr : ∀ s, r ≤ H s`, `hL : 1 ≤ L`, and `L ≥ 2`.
`deepestM H r := fun s => H s - r` (reduced widths).

`DeepestSplit H r nG := (Fin nReg → ℝ) × ((Fin (flatDim (deepestM H r)) → ℝ) × (Fin nG → ℝ))`.
So `q : DeepestSplit` has `q.1` (reg slot), `q.2.1` (core slot), `q.2.2` (spec slot).

Per-layer gauge reads (bijective packing via a homeo `regGaugeSlotEquiv` on `(q.1, q.2.2)`):
  `gaugeReadX q s : Matrix (Fin r) (Fin r) ℝ`
  `gaugeReadY q s : Matrix (Fin r) (Fin (H s.succ - r)) ℝ`
  `gaugeReadZ q s : Matrix (Fin (H s.castSucc - r)) (Fin r) ℝ`
Core read (bijective via `paramsEquivFlat`): `(paramsEquivFlat (deepestM)).symm q.2.1 s : Matrix (Fin (H s.castSucc - r)) (Fin (H s.succ - r)) ℝ`.
Because `regGaugeSlotEquiv` and `paramsEquivFlat` are equivs, I can pack ARBITRARY target
blocks back into a new `DeepestSplit` (this is exactly what the L=2 template does via
`regGaugeSlotEquiv.symm` + `Function.update`).

`framedParamsPivot H r hr hL J Pf Qf q : Params H` reconstructs a full param tuple. For a layer
`s ≠ lastLayer` it is `framedLayer`, which unfolds to (in the `Fin r ⊕ Fin(·-r)` threshold-split
block form, writing `reindex` for the threshold reindex and `corM := reindex(fromBlocks 1 0 0 0)`):
    layer_s = corM + (reindex Pf_s) · (fromBlocks (gaugeReadX) (gaugeReadY) (gaugeReadZ) (coreRead)) · (reindex Qf_s)
For the LAST layer it uses a pivot-aligned reindex on the succ side (`pivotThresholdSplit` instead
of `rThresholdSplit`) but is structurally the same `corM_piv + reindex_piv(Pf)·fromBlocks(XYZT)·reindex_piv(Qf)`.

`deepestChain H r hr A s := reindex(split_s)(split_{s+1}) (deepestChainLayer A s)`, and for `s<L`,
`deepestChainLayer A s = reindex(finCongr)(finCongr)(A ⟨s,hs⟩)`. So `deepestChain A s` is just the
`Fin r ⊕ Fin(chainWidth·-r)`-block form of the layer `A ⟨s,·⟩`, up to `finCongr` width relabels.

The abstract "moved chain" `movedC C Z0e s := fromBlocks ((C s).toBlocks₁₁) (movedY C s) (movedZ C Z0e s) (movedT C Z0e s)`,
where `C = deepestChain (framedParamsPivot ... q)`, `Z0e = Z0edit0 C L`. `movedY/movedZ/movedT`
are explicit (Schur-untwist) functions of `C`. `movedZ` at layer ≥1 is unchanged (`= (C s).toBlocks₂₁`),
edited only at layer 0 (to `Z0e`).

## Banked frame facts (hypotheses available in the downstream theorem)
- Interior layers have TRIVIAL frames: `Pf s = 1`, `Qf s = 1` for `s ∉ {firstLayer, lastLayer}`.
  (So interior `deepestChain(framedParamsPivot q) s` decodes DIRECTLY to `fromBlocks (1+gaugeReadX q s)
  (reindex gaugeReadY) (reindex gaugeReadZ) (reindex coreRead)` — proven lemma.)
- Boundary frames are ONE-SIDED: `Qf firstLayer = 1` and `Pf lastLayer = 1` (given). So layer 0 is
  framed only on the LEFT by `Pf_0`; the last layer only on the RIGHT by `Qf_last`.
- The boundary frames are UNITS: `IsUnit (Pf firstLayer)`, `IsUnit (Qf lastLayer)`.
- The reindexed boundary frames are block-triangular: `(reindex Pf_s).toBlocks₁₂ = 0` (all s),
  `(reindex Qf_s).toBlocks₂₁ = 0` (all s).
- Forced-decode lemmas (proven): for a block-lower left frame `fromBlocks P11 0 P21 1` with `P11·Pinv=1`,
  the decode `fromBlocks (Pinv·A)(Pinv·Y)(Z−P21·Pinv·A)(T−P21·Pinv·Y)` satisfies
  `(fromBlocks P11 0 P21 1)·decode = fromBlocks A Y Z T`; symmetric right-frame version.

## The target equality `hmove` (what the definition must make provable)
    deepestChain H r hr (framedParamsPivot ... (psiSplitRawGen q))
      = movedC (deepestChain H r hr (framedParamsPivot ... q)) (Z0edit0 (deepestChain ... q) L)
proven layerwise by `funext s; by_cases s < L`, interior via the banked interior decode, boundary
via the forced-decode lemmas.

## The question
I am choosing the DEFINITION of `psiSplitRawGen q`'s per-layer reads (X', Y', Z', T' packed back via
the equivs). Two candidate designs:

(A) "Frame-inverse uniform": at EVERY layer, set `fromBlocks X' Y' Z' T' :=
    reindex⁻¹( Ring.inverse(reindex Pf_s) · ( reindex⁻¹? ... (movedC C Z0e s) − corM) · Ring.inverse(reindex Qf_s) )`,
    i.e. literally invert the frame conjugation + subtract corM. Interior collapses (frames=1, corM
    handled). Uses the full-matrix `Ring.inverse` of the frame; `hmove` needs `Pf·Pinv=1` (units, given).

(B) "Interior-blind + boundary forced-decode": interior reads = `movedY/movedZ/movedT` (finCongr-stripped);
    boundary layer-0 reads = the forced-decode `fromBlocks (Pinv·A)(Pinv·Y)(Z−P21·Pinv·A)(T−P21·Pinv·Y)`
    with `A,Y,Z,T` = movedC's layer-0 blocks and `P11,P21,Pinv` from the block-lower frame; last-layer
    symmetric. Matches the forced-decode lemmas directly but is NON-uniform (3 cases) and must handle the
    additive `corM` (the framed layer is `corM + frame·decode`, not `frame·decode`).

Note the additive `corM` in the framed layer: the framed layer is `corM + Pf·reindex(fromBlocks XYZT)·Qf`,
so producing `movedC C Z0e s = fromBlocks A Y Z T` needs `Pf·reindex(fromBlocks X'Y'Z'T')·Qf = fromBlocks A Y Z T − corM`,
i.e. the `(1,1)` block target is `A − 1` (corM's only nonzero block is `(1,1)=1`).

Which design (A vs B, or a variant) gives the cleanest `hmove` proof and least cast/reindex pain?
Is there a hidden obstruction — e.g. does subtracting `corM` before inverting the frame break the
forced-decode structure (since corM changes only the `(1,1)` block, and `A = (C s).toBlocks₁₁` already
includes the `+1` from corM in the base chain)? Concretely: in the base chain, `(C 0).toBlocks₁₁ = 1 +
(Pf_0·fromBlocks(Xq..))_{11}` — so `movedC`'s layer-0 `(1,1)` block IS `(C 0).toBlocks₁₁` (unchanged by the
move). When I subtract corM and left-invert `Pf_0`, do I recover exactly `fromBlocks(Xq..)` in the `(1,1)`
slot (so `X'_0 = Xq_0`, i.e. X unchanged) and the forced edits in the other three slots? Verify this is
consistent (no over/under-determination).
</task>

<output_contract>
1. VERDICT (1 line): design (A), (B), or a named variant is cleanest; and OBSTRUCTION: none / describe.
2. The recommended per-layer definition of `fromBlocks X' Y' Z' T'` (one formula, note the last-layer
   pivot-reindex difference), in prose/pseudo-math (no Lean syntax needed).
3. The corM-subtraction consistency check: confirm (or refute) that the `(1,1)` block works out so X is
   effectively unchanged and the move only touches Y/Z/T, with no over-determination.
4. The 2-3 riskiest steps of the resulting `hmove` proof, cheapest-first.
Keep it under ~500 words. Flag any step you are INFERRING vs. can DERIVE from the given facts.
</output_contract>

<grounding_rules>
Distinguish what you can DERIVE from the given block algebra vs. what you INFER about the Lean
mechanics you cannot see. Do not invent lemma names. If a claim needs a fact I did not state, say so.
</grounding_rules>
