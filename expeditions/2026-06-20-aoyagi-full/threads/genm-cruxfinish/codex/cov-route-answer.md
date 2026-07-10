1. **Telescoping**

Use **(a)**: define the backward data first, then prove a forward-prefix telescope. Do not induct right-to-left through `prodAux`; let the recursion mismatch live only in the definitions of `K i`.

Clean invariant, with `N := L+1` tail layers, `H := tailChain M`, `a i := H i - q`, and every matrix reindexed by `blockSplitEquiv`:

```lean
Pblk n := reindexed (prodAux H A' n)
S i    := fromBlocks 1 0 (-(K i)) 1
Sinv i := fromBlocks 1 0 (K i) 1
Ustep i := fromBlocks (α i) (B i) 0 (Y i)

Invariant(n):
  ∃ Bacc,
    S 0 * Pblk n * Sinv n
      = fromBlocks (αProd n) Bacc 0 (YProd n)
```

where

```lean
αProd 0 = 1
YProd 0 = 1
αProd (n+1) = αProd n * α n
YProd (n+1) = YProd n * Y n
```

The step is:

```lean
S 0 * Pblk (n+1) * Sinv (n+1)
= (S 0 * Pblk n * Sinv n) * (S n * Xblk n * Sinv (n+1))
```

then apply `blockShear_step` to the second factor and `fromBlocks_multiply`. Use fully-applied associativity terms, not `rw [Matrix.mul_assoc]`.

At `n = N`, `K N = 0`, so `Sinv N = 1`, giving the normal form. Keep this as a theorem from abstract `ThreadedShearData`; construct the data from the chart separately.

2. **Radius Scaling**

For a chain `H : Fin (N+1) → ℕ`, the fixed-radius product-box identity is:

```lean
∫⁻ A in paramsBoxM H T,
  ofReal ((frobSq (prod H A)) ^ (-c'))
=
ofReal (T ^ ((flatDim H : ℝ) - 2 * (N : ℝ) * c')) *
∫⁻ A in paramsBoxM H 1,
  ofReal ((frobSq (prod H A)) ^ (-c'))
```

assuming `0 < T`. This follows from:

```lean
prod H (T • A) = T^N • prod H A
frobSq (T^N • P) = T^(2*N) * frobSq P
```

and linear cube scaling. I am certain about the exponent; I am not asserting the exact Mathlib lemma names for the scaling API.

For `reducedMorseFront`, isotropic radius `T` is **not** an exact scalar identity unless `N=1`, because

```lean
sumSq (T • X) + frobSq (prod H (T • Y))
= T^2 * sumSq X + T^(2*N) * frobSq (prod H Y).
```

Use either a domination for `T ≥ 1`, or the cleaner anisotropic identity with `X`-radius `T^N`:

```lean
I(T^N,T) =
ofReal (T ^ ((flatDim H : ℝ) + (N : ℝ) * d - 2 * (N : ℝ) * c')) * I(1,1)
```

where `d = M 0 * q`.

Verdict: any finite `T > 0` is harmless; exponent sign never breaks finiteness because `T^e` is a finite positive real. But inferred warning: if the CoV image is genuinely unbounded because `K_i` are unbounded, fixed-radius scaling alone does not cover the whole image. It proves radius-independence for finite boxes, not integrability over an unbounded Schur-coordinate image.

3. **Loss Split**

Yes: the `A0` integral needs its own shear. From

```lean
S 0 * P = fromBlocks α B 0 Z
```

rewrite

```lean
A0 * P = (A0 * (S 0)⁻¹) * fromBlocks α B 0 Z.
```

For fixed tail data, `A0 ↦ A0 * (S 0)⁻¹` is rowwise unit-triangular and measure-preserving. Then block-split the columns of the sheared `A0`.

Clean route: prove a named pointwise lemma after this `A0` shear, with all reindexing already absorbed:

```lean
frobSq (A0 * P)
  = / ≤ / comparable_to
    (∑ i, (R i)^2 + frobSq Z)
```

For Lean, I would aim first for the exact block expression and then the inequality needed for `lintegral_mono`, not a brittle global equality if extra non-orthogonal `α,B` changes introduce determinant factors.

4. **Feasibility**

Difficulty, hardest first:

1. **MP / CoV domain control**: hardest if the image is unbounded; fixed-box scaling does not solve that by itself.
2. **Loss split**: hard, but local if isolated after the `A0` shear.
3. **Telescoping**: tedious opaque-width algebra, but the invariant above is stable.
4. **Radius scaling**: easiest; mostly homogeneity plus cube scaling.

If you need one named sub-sorry, isolate:

```lean
frontChartIntegral_le_reducedMorseFront_radius
```

or more explicitly:

```lean
frontChartIntegral_lt_top_of_threadedCoV
```

with hypotheses packaging the telescope, measure-preserving CoV, `A0` loss split, and finite-radius/image control. Everything above it can then consume `reducedMorseFront_lt_top` cleanly.