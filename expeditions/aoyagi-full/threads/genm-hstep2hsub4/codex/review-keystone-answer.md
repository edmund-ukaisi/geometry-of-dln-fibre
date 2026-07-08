**1. Fidelity — verdict: honest.**

The LHS is genuinely the moved point. The theorem’s conclusion applies `deepestCoreAbsorbConj` to `psiSplitRawGen ... q`, and the proof invokes `deepestCoreF_coreAbsorbConj_eq_prodSchur` with that same moved point as the argument, not with `q` or the basepoint. See [DeepestHsub4coreGen.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/DeepestHsub4coreGen.lean:129) and the rewrite at [line 131](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/DeepestHsub4coreGen.lean:131).

`psiSplitRawGen` is also a real definition, not an identity alias: it repacks per-layer `psiReadBlk` blocks into new reg/gauge/core slots. See [DeepestPsiSplitRawGen.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/DeepestPsiSplitRawGen.lean:165).

The free `Score` variable plus `hScoreDef` is faithful. The proof rewrites by `hScoreDef`, so after the rewrite the RHS is literally the displayed Schur/Frobenius formula. This does not hide mathematical content; it just lets downstream code use its chosen `Score` name. Caveat: downstream must really provide that exact `hScoreDef`.

**2. Non-vacuity — verdict: concern, not broken.**

`q` and `x` are independent except through `hC`; that is a serious conditionality. The theorem does not prove that the intended pair `q = split x` satisfies `hC`. The hypothesis `hC` is the whole framed-moved-readback-to-raw-chart bridge, and it is much stronger than a harmless cast or simplification. See [DeepestHsub4coreGen.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/DeepestHsub4coreGen.lean:99).

But I do not see a contradiction. In particular, the base-point objection in the prompt is not decisive. The repo has `psiSplitRawGen 0 = 0` at [DeepestPsiHraw0Gen.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/DeepestPsiHraw0Gen.lean:167). Also, for `L ≥ 2`, the deepest-point boundary package gives `deepBlkY_s = 0 ∨ deepBlkZ_s = 0` layerwise, with interiors handled by the corner form; see [DeepestDeepBlkBoundaryGen.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/DeepestDeepBlkBoundaryGen.lean:82). On the RHS, `blockSchur (movedC C Z s)` is exactly the moved Schur target `schurTilde C s`; see [DeepestPsiSplitGenMoved.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/DeepestPsiSplitGenMoved.lean:117). For the constructed deepest chain, the individual layer Schur cores are zero in the normal deepest configuration, not merely the final product.

So `hC ∧ hq` is not globally unsatisfiable. A concrete sanity witness is the front-corner normal-form case: `B = diag(I_r,0)`, identity frames, `q = 0`, `x = base`. Then the pivots are identities, `hq` holds since the cutoff inner radius is positive, and both sides of `hC` are zero layerwise. What is not proved here is the useful local statement: `hC` for all nearby `x` with `q = split x`.

**3. Laundering — verdict: honest partial, with a major dependency.**

`hC` does not literally assume the final conclusion `frobSqMat (...) = Score x`. It assumes a per-layer readback equality. Then `prod_deepestM_eq_schur_ldu_readback_gen` turns that into the product-level Score integrand; see [DeepestSchurScoreTelescopeGen.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurScoreTelescopeGen.lean:235). That is legitimate as a reduction, but `hC` contains the main missing algebra.

The frame hypotheses are also not the conclusion in disguise; they are endpoint triangularity, normalization, and invertibility assumptions. They are strong domain hypotheses, but not Frobenius-energy equality.

`hq` is honest for a pointwise theorem. It says the moved point is inside the cutoff inner ball, exactly what the cutoff-strip lemma needs; see [DeepestSchurShiftConj.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShiftConj.lean:505). For the eventual germ theorem, however, proving `hq` near the base is Producer-1 content. Carrying it explicitly is fine; using this theorem as if the germ were already closed would be laundering.

Bottom line: the Lean reduction is not broken or vacuous on its face. It is an honest conditional reduction. The unresolved burden is exactly `hC` for the intended `q = split x`, plus the eventual-ball proof for `hq`.