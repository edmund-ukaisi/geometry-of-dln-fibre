**Short Verdict**

Your “S2-only feasible” verdict is **repairable and likely sound**, but the resolution as stated has a real hole: the first point blow-up of `Δ=0` does **not** by itself give leaves that are only full-rank Morse or lower point-blow-up cores. The missing piece is a **rank-stratified local normal form** on the exceptional divisor.

The obstruction is not a forced need for the general Aoyagi/Watanabe `rlct >= codim/2` bound. It is a missing elementary induction lemma.

**(1) Completeness**

Point-blowing up `Δ=0` gives

```text
Δ = a R,      Jac ~ |a|^{r^2-1},      G = a^2 ||R S||^2.
```

But on the exceptional divisor, `{rank R < r}` is still determinantal and is singular for `r >= 3`. The intermediate strata `{rank R = j}`, `0 < j < r`, must be handled.

Near a rank-`j` point of `R`, after choosing a nonzero `j x j` minor and doing analytic row/column elimination,

```text
R S  ~  ( P , B Q )
```

up to uniformly invertible linear changes, where

```text
P ∈ R^{j x p},   B ∈ R^{(r-j) x (r-j)},   Q ∈ R^{(r-j) x p}.
```

So locally

```text
||R S||^2  comparable to  ||P||^2 + ||B Q||^2.
```

That is **not just a lower core**. It is a Euclidean Morse block plus a lower determinantal core. This is the missing stratum analysis.

Concrete warning: for `r=3, p=4`, the rank-one stratum gives

```text
a^2 ( ||P||^2 + ||B Q||^2 )
```

with `P` four-dimensional and `B Q` the `r=2,p=4` core. Its inner threshold is

```text
4/2 + 2 = 4,
```

which is below the first blow-up scale threshold `9/2`. So if one only sees the full-rank branch, one gets the wrong answer.

**(2) Full-Rank Morse Claim**

Locally, yes. If `R0` has full rank, then `S ↦ ||R S||^2` is a positive definite quadratic form in the `rp` variables of `S`. The `R` variables are harmless parameters.

But this is only uniform on neighborhoods staying away from `det R = 0`. On the whole full-rank locus, the smallest singular value of `R` can tend to zero. So “full-rank Morse” is valid only after localization; the boundary is exactly the rank-drop locus handled above.

No positive-measure degeneracy appears. The degeneracy is determinantal, not Morse, and must be covered by the rank-stratified recursion.

**(3) Joint Convergence**

The dangerous expression is already visible in your `r=2` model:

```text
a^2 ( ||P||^2 + e^2 ||Q||^2 ).
```

This is **not** a product normal crossing leaf

```text
a^2 e^2 ( ||P||^2 + ||Q||^2 ).
```

So treating `{a^2,e^2}` and `{||P||^2,||Q||^2}` as independent leaves is not formally valid.

However, the convergence can still be proved from radial integration and Tonelli. The needed lemma is:

```text
rlct( ||P||^2 + H(z) ) = dim(P)/2 + rlct(H)
```

for disjoint variables, proved by integrating radially in `P`. Together with

```text
∫ |a|^{r^2-1} (a^2 H)^{-c} da dz
```

this gives the recursive threshold

```text
λ_{r,p}
= min( r^2/2,  min_{1 <= j <= r} ( jp/2 + λ_{r-j,p} ) ),
with λ_{0,p} = 0.
```

This is an S2/S2-free induction, not the general Aoyagi/Watanabe codimension bound.

**(4) Net**

There is a hole in the written verdict:

```text
rank-drop locus = lower core
```

is false as stated. The true local form is

```text
Morse block + lower core.
```

Also, the weighted sums are not normal-crossing leaves by themselves.

But there is no forced non-S2 citation if you add the missing rank-stratified induction and the radial disjoint-sum lemma. The mechanism is elementary:

```text
point blow-up in Δ
→ stratify exceptional divisor by rank j
→ Gaussian/Schur normal form
→ Euclidean radial integration for the P block
→ recurse on the smaller BQ core
→ monomial scale handled by S2/one-variable radial integration.
```

So: **your conclusion is sound only after this repair**. The current argument is incomplete; the specific missing stratum is the intermediate-rank exceptional stratum, especially visible at `r=3`, `rank R=1`.