1. **Q1**

The literal fixed-axis witness `S0 = eps E12`, `S1 = eps E21`, `W[k,k]=0` is **off-germ**: forcing that diagonal entry of `W` to vanish needs an `O(1)` off-pivot correction.

But `(e)` is still false on the germ. For `M ≥ 2`, take `W = I + eta E12` with `eta -> 0`, realized by `Y0, Z1 = O(sqrt eta)` and `A = I`. Let
`S1 = eps e2 e1ᵀ`, `S0 = eps e1 (e1ᵀ - eta e2ᵀ)`.
Then `S0 W S1 = 0`, while `S0 S1 = -eps^2 eta E11 ≠ 0`. All coordinates tend to the deepest point as `eps, eta -> 0`.

So: your specific `W[k,k]=0` counterexample is off-germ, but the corrected tilted-kernel counterexample is a genuine germ path. Thus `(e)` is false.

2. **Q2**

Shrinking `U` does **not** rescue `(e)` in the matrix-core case. The needed relative estimate

`||S0(W-I)S1|| ≤ rho ||S0S1||`, `rho < 1`

does not follow from `W -> I`. The product `S0S1` can vanish, or vanish to higher order, along rank-deficient directions while `S0(W-I)S1` remains comparable.

In the germ witness above, `R - S0S1 = -S0S1`, so the relative error ratio is exactly `1`; no `theta < 1` works. Conversely, with the same `W` and `S1`, take `S0 = eps e1e1ᵀ`; then `S0S1 = 0` but `S0WS1 = eps^2 eta E11 ≠ 0`, so `(d)` also fails.

A rescue needs an extra structural hypothesis, e.g. scalar `W = lambda I` bounded away from `0`, or an explicit uniform relative-error assumption. Mere germ smallness of `Y0,Z1` is insufficient.

3. **Q3**

**MUST-RESTATE** for `M > 1`. The bare uniform conjuncts

`||Rcore||² ≤ gamma2 coreF` and `coreF ≤ gamma1 ||Rcore||²`

are not provable as stated.

Correct statement:

`∃ U, C, ∀ w ∈ U, | ||Rcore(w)||_F² - coreF(w) | ≤ C * Sreg(w)`

where `Sreg = sumE2` is the regular energy controlling the off-pivot data and pivot inverse bounds.

Equivalently, use the folded form:

`Sreg + ||Rcore||_F² ≍ Sreg + coreF`

uniformly on a small neighborhood. That is the statement compatible with the exact identity `R = S0(I-K)S1`, the Frobenius remainder bound, and the regular-energy charge.

BOTTOM LINE: `(d)` and `(e)` must be restated with the regular energy folded in; bare multiplicative comparability is false on the germ for `M > 1`.