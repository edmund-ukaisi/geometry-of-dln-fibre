**1. TRUE / Threshold**

TRUE. In fact the threshold is exactly `c' = 2`.

At a generic point of `{A0 A1 A2 = 0}`, we have `rank(A0 A1)=2`, so locally the equation is just `A2=0` through an injective linear map. This is a codimension-`4` normal direction, hence local model
```text
∫_{R^4} ‖x‖^{-2c'} dx,
```
finite iff `c' < 4/2 = 2`.

For `c' ≥ 2`, divergence follows on any positive-measure set where `A0 A1` has rank `2` and bounded operator norm: near `A2=0`,
```text
‖A0 A1 A2‖ ≤ C ‖A2‖,
```
so the integrand dominates `‖A2‖^{-2c'}`, which diverges in dimension `4`.

Deeper strata do **not** lower the threshold below `2`. Codimension heuristics suggest they are not worse, but the clean proof is the fibre estimate below: it uniformly controls rank drops of `A0`, `A1`, and rank-one `A2`, reducing everything to the same final `4`-dimensional radial integral in `A2`.

**2. Ranked Routes**

1. **New shortcut (best): iterated fibre integration by largest-entry shears.** Two copies of one elementary lemma reduce
   `A0 A1 A2 → A1 A2 → A2`, then `radial_ball_iff` finishes.

2. **(a) Full rank-stratified recursion.** Correct and robust, but unnecessary here; it proves much more structure than this integral needs.

3. **(b) Single global generic shear.** Not valid globally. At `A0=0` or `A1=0`, the product is identically zero in all `A2` directions, so no global positive `4`-square block in `A2` can survive. An a.e. generic shear has coefficients blowing up or vanishing near rank-drop loci, so it does not by itself give domination.

**3. Top Route: Explicit Shear Bound**

Use this lemma twice. Let `X ∈ R^{p×n}`, `Y ∈ R^{n×q}`, with `p=4`, `q=2`, and `Y ≠ 0`. Pick an entry `Y_{ℓj}` of maximal absolute value, so
```text
Y_{ℓj}^2 ≥ ‖Y‖_F^2 / (nq),
|Y_{kj} / Y_{ℓj}| ≤ 1.
```

For each row `i` of `X`, define new coordinates
```text
u_i = (XY)_{ij} / Y_{ℓj}
    = X_{iℓ} + Σ_{k≠ℓ} (Y_{kj}/Y_{ℓj}) X_{ik},

v_{ik} = X_{ik}   for k≠ℓ.
```

Inverse:
```text
X_{iℓ} = u_i - Σ_{k≠ℓ} (Y_{kj}/Y_{ℓj}) v_{ik},
X_{ik} = v_{ik}.
```

This is triangular with determinant `1`. Also
```text
‖XY‖_F^2 ≥ Σ_i (XY)_{ij}^2
          = Y_{ℓj}^2 Σ_i u_i^2
          ≥ (‖Y‖_F^2 / (nq)) Σ_i u_i^2.
```

Since the original row box maps into `|u_i| < n`, `|v_{ik}| < 1`, we get
```text
∫_{X∈(-1,1)^{pn}} ‖XY‖_F^{-2c'} dX
  ≤ K_{p,n,q,c'} ‖Y‖_F^{-2c'},
```
where `K` is finite exactly because
```text
∫_{(-n,n)^4} (Σ_i u_i^2)^{-c'} du < ∞  ⇔  c' < 2.
```

Apply first with `X=A0`, `Y=A1A2`, `p=4,n=4,q=2`:
```text
∫_{A0} ‖A0 A1 A2‖^{-2c'} dA0
  ≤ K0 ‖A1 A2‖^{-2c'}.
```

Apply again with `X=A1`, `Y=A2`, `p=4,n=2,q=2`:
```text
∫_{A1} ‖A1 A2‖^{-2c'} dA1
  ≤ K1 ‖A2‖^{-2c'}.
```

Thus
```text
I ≤ K0 K1 ∫_{A2∈(-1,1)^4} ‖A2‖^{-2c'} dA2 < ∞
```
by your `radial_ball_iff`, since `c' < 2`.

**4. Biggest Risk**

The main Lean risk is not mathematics; it is packaging the parameter-dependent shear cleanly, especially at `Y=0`.

Cheapest de-risk: first prove a standalone fixed-`Y` lemma assuming a chosen maximal nonzero entry `Y_{ℓj}`. Treat `Y=0` separately by allowing the bound RHS to be `∞` or by splitting off the null set. Then instantiate the lemma only twice: `(A0, A1A2)` and `(A1, A2)`.