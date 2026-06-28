1. **Q1 Verdict: Wall**

This is **not** a bounded hfin-style reshape. Derived from the `NodeAchieverChart` fields: the lower atom needs a genuine full-dimensional chart with exact rate factorization, Jacobian c-o-v, injectivity/null-slice handling, and image control. That is categorically different from the MP/Tonelli hfin reshape.

Biggest obstruction: **the uniform actual chart `phi_{r,r,4}` with a proved c-o-v package**, i.e. determinant matching the true `leafH`, injectivity off bad slices, and exact `F ∘ phi = u_p^2 U` for all `r`.

2. **Q2 Jacobian Verdict**

If all you have is the bespoke `phi334_abs_det`, then the `∀r` Jacobian is **not** a known small Lean trick. It needs general determinant machinery.

Correction from this checkout: there is already reusable determinant infrastructure (`ChartFactor`/`composeFold_abs_det_leafH`/factored target lemmas), so the determinant telescope itself is no longer “invent from zero.” But applying it still requires a factored `∀r` chart, per-factor det bookkeeping, product-to-`leafH`, and c-o-v/injOn transfer. That is still not a few-hundred-line reshape.

3. **Q3 Shortcuts Ranked**

1. **Direct monomial reduction via cheaper coordinates:** only viable if “cheaper” still means a real rank/Schur coordinate chart with positive-measure domain and Jacobian control. That collapses back to the chart problem, so not a shortcut.

2. **Scaling/homogeneity:** not viable for the sharp threshold. A 1-D or global radial slice is measure-zero or gives the wrong exponent; it cannot replace the full-dimensional c-o-v.

3. **Restrict to a trivial sub-locus:** not viable as stated. Exact sub-loci are null; thickening them requires the same coordinate/Jacobian analysis.

Inference to check: there may be a specialized `(r,r,4)` Schur-core chart cheaper than full general-`M`, but it is still a chart build, not hfin plumbing.

4. **Q4 Recommendation: C**

Report this as a **research-scale wall / depth-checkpoint**, not a bounded build. The reason is precise: the task is not “reshape an integral”; it is “construct and verify a dimension-parametrized resolution chart.” A future route can reuse existing general determinant scaffolding, but the missing deliverable is still the actual `NodeAchieverChart (![r,r,4])` package, including c-o-v and exact factorization.