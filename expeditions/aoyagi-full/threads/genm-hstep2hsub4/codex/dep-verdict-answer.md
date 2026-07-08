**1. V1**

Agree. The load-bearing point is `hq`: `deepestCoreF_coreAbsorbConj_eq_prodSchur` only peels the cutoff to the raw Schur correction inside `closedBall 0 rIn`. For the full germ, you need `∀ᶠ x, psiSplitRawGen (split x) ∈ closedBall 0 rIn`.

Strictly, this does not require the theorem named “continuity of `psiSplitRawGen`”; any direct `Tendsto (fun x => psiSplitRawGen (split x)) (𝓝 basepoint) (𝓝 0)` or eventual-ball lemma would suffice. But from the banked objects/signatures, I see no cutoff-free raw variant and no way for `Score` to absorb the cutoff without changing the target. So the full closed germ sequences after the Producer-1 analytic/value piece.

**2. V2**

Agree, with one qualification. The per-`x` keystone is the right parallel deliverable if it takes `hq`, unit/frame hypotheses, and the `hC` readback as hypotheses or proves `hC` algebraically.

It is Producer-1-free in the analytic sense: no `psiSplitRawGen` continuity, no `psiSplitRawGen 0 = 0`, no diffeo triple. It still uses the already-defined concrete `psiSplitRawGen`/`psiReadBlk` algebra.

**3. V3**

Agree: the telescope-facing `hC` is not directly banked. `absorbedCoreConj_eq_schurCore` is unmoved/raw-decode Schur readback under a `deepBlkT = 0` hypothesis; `psiSplitRawGen_deepestChain_hmove` is for `framedParamsPivot`, not raw `decode x`.

Cheapest route: prove a new layerwise readback theorem. Rewrite `coreRead`/`gaugeRead` of `psiSplitRawGen` to `psiReadBlk`/`psiGhat`; split first/interior/last; use existing frame-identity facts for interiors and `blockSchur_lowerFrame_left` / `blockSchur_rightUpper_right` for the boundary frames; then land exactly the raw `movedC (deepestChain (decode x))` form needed by `prod_deepestM_eq_schur_ldu_readback_gen`. This is new formalisation, not just plumbing; 300-600 lines sounds plausible.

**4. Recommendation**

Build the keystone now, scoped explicitly as pointwise/algebraic: `hq` and unit germs are inputs, and the main work is the new `hC` readback plus the composition with `prod_deepestM_eq_schur_ldu_readback_gen`. Report that the full germ is blocked on Producer-1 only for the eventual cutoff-ball proof. That gives the non-idle thread a real deliverable and leaves the final germ as a small assembly once Producer-1 supplies `Tendsto`/eventual-ball.