1. **Yes, bounded**, but I would not scope the whole route (c) as only 6-10 lemmas unless that excludes cov/rate-transfer plumbing. The Schur determinant is now a bounded local build. The full chart construction is bounded but more like a small module.

Single riskiest sub-piece: `chartParamsFlat_eq_chartParamsGen` / `phiFlat_eq_phiGen` for the new flat chart. The Schur determinant no longer looks like the blocker; the hard part is proving the flat, factor-built layer matrices are the same `Params M` consumed by `routeMCore_phiGen`, through the dependent `Fin` reindexing.

Caveat: `LinearMap.det_pi` applies after conjugating matrix spaces to `Fin c → (Fin t → ℝ)` or `Fin r → (Fin t → ℝ)`. You likely still need custom bridge lemmas using `Matrix.mulVecLin`, `Matrix.vecMulLinear`, `Matrix.transposeLinearEquiv`, `LinearMap.det_conj`, `LinearMap.det_toLin'`, and `Matrix.det_transpose`. Also include `t=0`, `r=0`, `c=0`; the formula should survive, but Lean will not forgive hidden `t-i` assumptions.

2. **Cheaper: (i), transfer through `phiGen`, but only if you make the equality a construction invariant.** Do not prove a late, flat-coordinate extensional equality against an independently-built chart. Define/expose a `chartParamsFlat` decoder and prove:

```lean
chartParamsFlat u = chartParamsGen (u p) M t (Bflat u) hle
```

Then `phiFlat_eq_phiGen` is just `congrArg (paramsEquivFlat M)`, and `routeMCore_phiGen` gives the rate identity.

A direct re-proof reruns the landed telescope/cast work: `prod_chartParamsGen_eq`, `dlnLoss_chartParamsGen`, `hWgen`, `hAgen`, and the chain/product bridge. That is more Lean unless the equality bridge is made impossible by definitions.

3. **Yes, structural `injOn` is the right route.** No more 27-coordinate recovery.

Use factor lemmas:

```lean
schur_injOn_detK_ne_zero
ldu_injOn_q_ne_zero
radial_injOn
```

then compose with `Set.InjOn.comp`, carrying `Set.MapsTo` hypotheses. But the good set must be prefix-pulled:

```lean
⋂ i, prefix_i ⁻¹' good_i
```

not merely “each factor good in its own coordinates” informally.

For `cov`, the current `NodeAchieverChart.cov` only exposes `V \ {u_p = 0}`. Extra bad slices must be hidden the way `phi334_cov` does: apply c-o-v on the smaller good set, then add back null slices. If `det K` pulls back to a product of LDU `q` coordinates, use coordinate hyperplane nullity; otherwise you need polynomial-zero nullity for `det K = 0`.

4. **You still need prefix evaluation structure.** `general_composed_clm_abs_det` can remain the flat determinant telescope, but the derivative list is:

```lean
[D f_i (prefix_i u)]
```

not `[D f_i u]`.

So introduce a lightweight `ChartFactor`/prefix fold for `HasFDerivAt`, `InjOn`, and `hfac`. The “own K-block monomial” fact helps only after you prove pullback lemmas like:

```lean
detK_s (prefix_s u) = ± monomial_s u
```

Then the final determinant rewrite is clean. It does not remove the need to track prefixes.

5. **Recommendation:** use route **(c)** for determinant/cov, but transfer the rate identity through `phiGen`; keystone is `chartParamsFlat_eq_chartParamsGen` / `phiFlat_eq_phiGen`, while the parametric Schur determinant is now a bounded local theorem.