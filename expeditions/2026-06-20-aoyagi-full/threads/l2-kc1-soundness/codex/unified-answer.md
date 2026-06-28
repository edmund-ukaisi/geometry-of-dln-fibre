1. **YES.** Verified: `block_elimination` is only used to produce one `B = U * V`; replacing that producer with a separate aligned-factorization lemma does not touch `hSigma`/`:337`.

2. **YES, conditionally.** If “general position” means front `r` rows and front `r` columns give rank `r` equivalently a nonzero leading `r x r` minor, take `U` as the first `r` columns of aligned `B` and `V` as column coordinates in that basis; row/col permutations achieve this front-pivot condition, not generic position in a stronger sense.

3. **YES.** Verified from the current proof shape: product, ranks, interior `corM`, and boundary zero-shapes are proved for arbitrary `U,V` with `B = U * V` and ranks `r`.

4. **YES.** The two new facts are additive consequences of `layer0 = U * projM` and `last = embM * V`; Lean projection paths may need mechanical updates if `IsDeepLayers` remains a nested `∧`.

5. **ADDITIVE.** No place in supplying aligned `U,V` forces re-proving `hSigma` or the kernel/range/Sigma decomposition.

ADDITIVE