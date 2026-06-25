**Q1: G2 Reachability**

Verdict: **reachable only as a real infrastructure build; not reachable by just writing the Schur chart and invoking existing Mathlib dimension lemmas.**

**(a) Coordinate-ring isomorphism.**  
Yes, the Schur-complement section gives a genuine algebraic isomorphism, but **only after localizing at the pivot determinant**. The target chart is not affine closed; it is the basic open where the `r × r` pivot minor is invertible. Algebraically you should expect an `AlgEquiv` between localized quotient rings, roughly:

```lean
(R_rep ⧸ I_rank_le_r_mult)[1/Δ_mult]
  ≃ₐ[k]
(R_fibre_E ⊗[k] k[pivot_chart_vars][1/det])
```

or better, avoid a general tensor theorem and rewrite the RHS as:

```lean
(MvPolynomial chartVars R_fibre_E)[1/det]
```

The Schur formulas are regular in this localization because `A⁻¹` is `adj(A)/det(A)`. Building the `AlgEquiv` is tedious but conceptually solid.

What I would **not** expect to be ready in Mathlib v4.29:

```lean
ringKrullDim_tensorProduct_eq_add
ringKrullDim_mvPolynomial_eq_add
ringKrullDim_localization_away_eq
dim_product_variety_eq_add
```

under the hypotheses you need. I would search for `ringKrullDim`, `Ideal.height`, `IsLocalization`, `Localization.Away`, `MvPolynomial`, `TensorProduct`, but my expectation is that the exact additivity package is missing.

The better route is to prove the special lemma you need:

```lean
ringKrullDim ((MvPolynomial σ A) localized away fresh_det)
  = ringKrullDim A + Fintype.card σ
```

for finite-type reduced/prime affine `k`-algebras, then extend to reducible rings by minimal primes.

**(b) Principal opens.**  
Be careful: “dimension is preserved by `D(f)`” is not a pure localization fact for arbitrary domains. For finitely generated domains over a field and nonzero `f`, yes, nonempty principal opens have the same dimension. But I would not expect Mathlib v4.29 to have this in the needed form.

Also, your current `varietyDim Z := ringKrullDim (MvPolynomial ⧸ vanishingIdeal Z)` does **not** really model locally closed charts. If you feed it a dense open subset, its vanishing ideal is the closure ideal. That can be useful, but it is not the coordinate ring of the open chart. For G2 you need a new localized chart-ring layer.

**(c) Size and hard wall.**  
Estimate: **6-9 modules**, not 1-2.

Likely modules:

1. basic-open coordinate rings as localizations of affine quotients;
2. pivot chart for rank-`r` matrices via Schur complement;
3. localized endpoint-action formulas for `mult`;
4. the actual chart `AlgEquiv`;
5. polynomial-extension Krull dimension additivity;
6. localization-at-fresh-determinant preserves dimension;
7. reducible/minimal-prime passage;
8. finite pivot-chart cover / full-dimension exact-rank argument;
9. assembly into `codimRepCanonical`.

Single hardest sub-wall: **Krull-dimension additivity for localized polynomial extensions over possibly reducible affine coordinate rings**, tied back to `Ideal.height`/minimal primes. The Schur `AlgEquiv` is not the mathematical wall; dimension transport is.

**Q2: Route Choice**

Verdict: **use G2 as the primary route; do not bet on the inner-group route.**

The inner-group idea is seductive but likely worse in Lean. `mult⁻¹(E)` is not a single orbit, and the old rank-pattern classification for quiver orbits does not directly classify `H`-orbits with frozen endpoint product `E`. You would need new relative-position invariants: kernels/images relative to `ker E`, `im E`, and intermediate transmitted rank-`r` data. The existing `OrbitImageDim` machinery computes dimensions of known orbit closures; it does not by itself identify the fibre as a finite union of such closures with the correct maximal dimension.

The recursion-on-`N` idea also looks bad. Peeling off `A_N` creates incidence conditions like `ker(previous product) ⊆ ker E`, then rank strata and maximization. That is likely a new stratified dimension theorem in disguise.

For the `d - r` lead: **the fibre over `E` is not exactly `Σ⁰_{d-r}`.** The numeric anchor already kills that:

```text
d = (2,2,2), r = 1
dim fibre(E) = 4
dim Σ⁰_(1,1,1) = dim {ba = 0} = 1
```

What is plausible is a chart/dimension relation with extra affine/frame parameters. The expected extra dimension is

```text
D(d) - D(d-r) - δ
= Σ_{i=1}^{N-1} r(2 d_i - r).
```

So a better reduced-rank statement would be:

```text
dim fibre(E)
= dim Σ⁰_{d-r} + Σ_{i=1}^{N-1} r(2 d_i - r),
```

assuming the usual codim equality `C_r(d) = C_0(d-r)`. That is useful as a calculation target, but it still needs chart/localization/product-dimension infrastructure. It is not a free replacement for G2.

**Q3: Things I Would Attack First**

Main overclaims / risks:

- A single pivot chart does not automatically compute global `dim Σ^r`; you need finite chart cover or a proof the chart meets all top-dimensional components.
- `Σ^r` and `Mat^{rk=r}` are locally closed, not closed. Your current `vanishingIdeal` substrate sees closures unless you add localized coordinate rings.
- Reducibility matters. You cannot use the irreducible catenary bridge directly on `Σ̄^r` or the fibre unless you pass through minimal primes/maximal components.
- Product dimension is not free. Avoid general tensor-product dimension if possible; prove the special localized polynomial-extension formula.
- The `d-r` fibre-is-`Σ⁰` slogan is false literally; only a dimension relation with extra parameters is plausible.

**Final Go / No-Go**

Go for **G1 first**; it is clean and independent.

For the main proof: **conditional go** on G2 if you accept a serious commutative-algebra/chart infrastructure build. **No-go** if the plan assumes Mathlib already has product/open-chart dimension lemmas in the needed form.

Recommended order:

1. G1 reduce arbitrary rank-`r` `B` to `E`.
2. Prototype the localized Schur `AlgEquiv` for one pivot chart.
3. Build the special `ringKrullDim` lemma for localized polynomial extensions.
4. Add finite chart cover / reducible minimal-prime bookkeeping.
5. Assemble G3/G4.

Single hardest sub-wall: **dimension of localized polynomial extensions over the fibre coordinate ring, especially reducible/minimal-prime handling.**