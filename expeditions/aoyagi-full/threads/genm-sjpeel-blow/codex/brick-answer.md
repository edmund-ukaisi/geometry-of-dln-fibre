**1. Confirm, with a caveat.**

Yes: closing `sjBoundaryPeel` is not bounded plumbing over `radial_morse_residual_power_le`. The tight integrand needs the Schur corank block and the anisotropic dependence on `Q_bot`, plus chart-cover and a.e. null-locus assembly.

Caveat: be careful with any fixed-`Q` anisotropic lemma whose constant is only `P_full^{-a/2}`. In general that pointwise claim is false. Example: `p=1, q=2, a=2`, `W = (1,0)^T`. Then

`∫_{[-1,1]^2} (g² + u²)^(-c') du dv ~ C g^(1-2c')`

but the desired Frobenius-only RHS scales like

`C' g^(2-2c') (g²+1)^(-1) ~ C' g^(2-2c')`.

The ratio blows like `1/g`. So the anisotropy/rank-defect cannot be compressed to Frobenius norm pointwise without extra resolution/integration.

**2. Right brick.**

Do **not** spend the tide on (A) if the criterion is “eventual `sjBoundaryPeel` assembly consumes this.” (A) is clean and likely a real 80-150 line wrapper if flattening helpers are present: matrix block → `Fin (p*q)`, prove `frobSq = ∑ squares`, use the existing box-to-ball residual lemma. Snags are mundane: `p*q = 0`, `m+1` indexing, casts, and `ofReal` algebra. But it only proves the isotropic special case and misses the `P_full^{-a/2}` coupling.

(B) is the right mathematical level, but not in the naive Frobenius-only form. A safe useful B-type lemma would expose the singular-value/regularized-Gram/angular factor explicitly; the later `(S,J)` resolution is what can consume or dominate that factor.

For this tide, the tightest reusable brick is **(C) strengthened from mere finiteness to a quantitative finite-cutoff Beta bound**:

`∫₀^R (g² + z² h²)^(-c') z^(a-1) dz`

bounded uniformly in the two regimes `h ≪ g` and `h ≫ g`, with assumptions `a>0`, `g>0`, `c'>a/2`. Mere `<∞` is too weak; the assembly needs the scaling/cutoff dependence. This scalar brick is self-contained and sits directly inside the eventual polar/radial anisotropic proof.

**3. Null-locus trap.**

Yes. With `Real.rpow` under `ENNReal.ofReal`, `0^negative = 0`, not `⊤`. So unconditional pointwise RHS statements using `P_tail` are dangerous.

Safe statements should carry explicit positivity hypotheses like `0 < w` or `0 < g`. In the final peel, handle `{P_tail = 0}` by `lintegral_mono_ae` after proving it is null in the relevant nondegenerate cases. `P_full = 0` is less dangerous because then `Q=0` and the left integrand also collapses under the same convention, but `P_tail = 0 < P_full` is exactly the bad locus.