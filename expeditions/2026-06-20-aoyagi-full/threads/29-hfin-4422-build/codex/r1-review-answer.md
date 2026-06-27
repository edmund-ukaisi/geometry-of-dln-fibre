**QUESTION 1**

Yes: for the stated landed lemma, the threshold `c' < 2` is correct and no `n`/`q` threshold appears. The `A0` fibre has `(p,n,q)=(4,4,2)`, so it needs `c' < p/2 = 2`; `n,q` only affect the finite constant. The `A1` fibre has `(p,n,q)=(4,2,2)`, again `c' < 2`; `n,q` only affect the constant. The `A2` leaf is a 4-dimensional radial integral over `[-1,1]^4`, finite exactly for `c' < 4/2 = 2`. Tonelli is harmless for nonnegative integrands, finite `Y`-independent constants can be pulled out, and associativity is ordinary finite-sum matrix associativity. The threshold is sharp mathematically, by restricting to positive-measure neighborhoods where `A0,A1` have full rank so the singularity is comparable to the `A2` radial one.

**QUESTION 2**

1. (a) **SOUND-BOOKKEEPING**: `routeMCore = frobSq(prod)` is nonnegative, so `|routeMCore| = routeMCore`.

2. (b) **SOUND-BOOKKEEPING**: at `c'=0`, the integrand is `1`, so the integral is just the finite volume of `(-1,1)^28`.

3. (c) **SOUND-BOOKKEEPING**: for finiteness, open-to-closed is just monotonicity; if equality is wanted, the boundary is null and contributes zero even if the integrand blows up there.

4. (d) **SOUND-BOOKKEEPING, INFERENCE**: given your stated measure-preserving `paramsEquivFlat` and proven entrywise reshape/product identities, this is coordinate permutation plus Tonelli, with no Jacobian issue; only an actual mismatch in the proven coordinate order would be a gap.

Final verdict: **HONESTLY-SCOPED**, conditional on the stated reshape/product identities really matching the flat coordinate order.