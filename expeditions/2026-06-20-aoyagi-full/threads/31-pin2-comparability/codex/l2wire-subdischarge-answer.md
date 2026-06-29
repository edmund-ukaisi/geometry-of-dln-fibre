(a) **Aψ/Aq: correct, one-liner setup.**  
Use `Aq := (paramsEquivFlat H).symm x`. Use `Aψ := (paramsEquivFlat H).symm (split.symm (psiSplitRawL2 H r hr hL (split x)))`.  
Key rewrite: `split (split.symm qψ) = qψ`, then `hsplit (split.symm qψ)` rewrites `qψ` as `deepestSplit … w0 …`.

(b) **hframeψ/hframeq: direct, one-liners plus rewrite.**  
`hframeq` is `framedParamsPivot_eq_frame_of_front … x s`, after `rw [hsplit x]`.  
`hframeψ` is the same lemma at `wψ := split.symm (psiSplitRawL2 … (split x))`, after rewriting `deepestSplit … w0 wψ = psiSplitRawL2 … (split x)` via `← hsplit wψ` and `Equiv.apply_symm_apply`.

(c) **hS3b: bounded sub-proof, not a one-liner.**  
Cheapest route: prove the basepoint frame `hframe0` using §iii at `w0`; telescope with `endpoint_telescoping_eq`; rewrite `B = prod H (deepestPoint …)` via `deepestPoint_isDeep`; then reduce `prod(framedParamsPivot 0)` by `framedParamsPivot_coreZero` and `reindex_prodAux_framedParamsRegPivot_zero`.  
`hcorner` supplies the last-layer corner, but is not enough alone; `hNF/hPfL/hinterface` are part of the basepoint frame/telescope assembly.

(d) **hm11/hm12/hm21: real sub-proof.**  
Per-layer route: unfold the `L=2` product as first layer times last layer; use S6r readbacks to show the first factor is unchanged and the last factor changes only `Y1,T1`; feed `reindex_prod_regBlocks_eq_of_e2`.  
The `he2` input is `e2_regPreserve` with `A0,Y0,Y1,T1,T1'`, after rewriting `Y1' = Y1 + A0⁻¹*Y0*(T1−T1')`. Risk: this needs `A0` invertible / unit-locus conversion from `⁻¹` to `⅟`; without that, the global `∀ x` form is not justified.

(e) **hWdet: bounded only from q-smallness, not from hball alone.**  
The valid chain is: prove `q ∈ Metric.ball 0 (l2ExtraRadius …)`; apply `ball_l2ExtraRadius_subset`; take `.2` of the resulting `l2ExtraUnitSetSplit` membership.  
A closed-ball hypothesis needs a strict radius inequality `< l2ExtraRadius`, not just `≤`. Also, `psiSplitRawL2 q ∈ closedBall …` does not imply `q` is small unless you have a separate q-membership/near-basepoint fact.

(f) **hLDUtie: genuine sub-proof, but banked-math assembly if the dictionaries exist.**  
Assemble cleaned-product = Score integrand via the L2 reduced-product unfold, `prod_absorbed_eq_schur_ldu`, and `rcore_schur_factor_of_corner_split` on the `hS3b` corner split, plus the decode-`x` readback ties.  
Most likely wall: matching the cleaned `Function.update` tuple and framed Score Schur blocks through the dependent `Fin 2` casts / frame dictionary; not new algebra if those readback lemmas are already banked.

**Risk ranking:** (d) highest if the current goal is truly global `∀ x`; otherwise (f) highest by proof size. Then (e), (c), (b), (a).

As currently shaped, `hsub3reg + hsub4core` are bounded only after local/unit-radius hypotheses are threaded correctly; `hLDUtie` looks like a large banked-piece assembly, not the genuine new-math wall.