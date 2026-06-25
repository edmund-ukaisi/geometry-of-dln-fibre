**Verdict:** use **Route B** as the Lean-facing target.

Route A is mathematically true, but it asks you to build an extra reducible `varietyDim` bridge: `dim R/I = max dim R/P` over minimal primes. I did not find that packaged in Mathlib v4.29. Route B matches your `SigmaCodim` precedent and the actual codimension definition:

```lean
codimRepCanonical (fibre d E)
= (fibreGenIdeal d E).height
= ⨅ P ∈ (fibreGenIdeal d E).minimalPrimes, P.primeHeight
```

The fibration count is **not** carried by `trdeg_add_eq` all the way to the closed fibre `E`. `trdeg_add_eq` gives the **generic fibre** of a dominant map of domains:

```lean
Algebra.trdeg k Frac(B)
  = Algebra.trdeg k Frac(A) + Algebra.trdeg Frac(A) Frac(B)
```

This is buildable from `trdeg_add_eq` plus your `ringKrullDim = trdeg` bridge. But it only computes the fibre over the generic point of `Spec A`. To identify the fibre over the closed rank-`r` point `E`, you still need a no-jump statement: local flatness/product triviality over the exact-rank chart, or an equivalent direct dimension upper bound. Without that, the statement is false in general.

The affine height statement that actually moves closed fibres is:

```lean
Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
```

If `A → B` has `Algebra.HasGoingDown A B` and `P` lies over `p`, then

```lean
P.height =
  p.height + (P.map (Ideal.Quotient.mk (p.map (algebraMap A B)))).height
```

For `P` minimal over `pB`, the second height is `0`, so `height_B P = height_A p`. This is exactly the affine replacement for “flat fibre dimension is constant”. But the hidden hypothesis is going-down, usually from flatness. Without it Mathlib only gives `Ideal.height_le_height_add_of_liesOver`, the wrong direction for your lower bound.

**Recommended Sub-Lemmas**

1. `fibre_height_iInf_minPrimes`  
   Retarget with H1, then unfold `Ideal.height`.

2. `height_base_maxIdeal_E_eq_delta`  
   In the determinantal base `Mat^{≤r}`, prove `m_E.IsMaximal` and `m_E.height = δ`, using irreducibility/primality of the `N=1` determinantal variety and `height_eq_ringKrullDim_of_isMaximal`.

3. `minimal_fibre_prime_lies_over_component_and_E`  
   For each minimal prime `P` of `fibreGenIdeal d E`, choose a minimal prime `Q` of `sigmaIdeal d r` with `Q ≤ P`; in `(R ⧸ Q)`, show `P/Q` lies over `m_E`.

4. **Hard rung:** `relative_height_E_eq_delta_on_exact_rank_chart`  
   For every relevant component `Q`, every minimal prime over `m_E` in `R ⧸ Q` has relative height `δ`. This is where flatness/local product/no-jump enters. Trdeg alone does not prove it.

5. `all_fibre_components_height_ge_C_add_delta`  
   Use `height Q ≥ C` from the SigmaCodim per-component bound plus the hard relative-height lemma.

6. `exists_fibre_component_height_eq_C_add_delta`  
   Exhibit one top component, e.g. from a minimising Kostant partition/`realizerD`, whose product has rank exactly `r`; apply the same relative-height lemma to get equality.

Then the `iInf` over minimal primes gives `C + δ`.

**Hard Direction:** `codim ≥ C+δ`, i.e. every fibre component has dimension at most `card−C−δ`. Krull height theorem gives upper bounds on height, not lower bounds, and the generator count is much too large. The easy direction is exhibiting one component of height `≤ C+δ`.

**Mathlib v4.29 Names To Check/Use**

- `trdeg_add_eq`
- `MvPolynomial.trdeg_of_isDomain`
- `trdeg_eq_zero`
- `trdeg_le_of_injective`, `trdeg_le_of_surjective`
- `AlgEquiv.trdeg_eq`
- `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`
- `Ideal.height_le_height_add_of_liesOver`
- `Algebra.HasGoingDown.of_flat`
- `Module.Flat.of_linearEquiv`
- `Module.flat_of_localized_span`
- `RingHom.Flat.propertyIsLocal`
- `Ideal.height`, `Ideal.height_eq_primeHeight`, `Ideal.height_mono`
- `Ideal.height_strict_mono_of_is_prime`
- `Ideal.radical_minimalPrimes`
- `Ideal.minimalPrimes.equivIrreducibleComponents`
- local: `affine_domain_height_add_ringKrullDim_quotient_eq`, `height_eq_ringKrullDim_of_isMaximal`, `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`

I would not build around generic flatness in v4.29; I did not find a packaged generic-flatness theorem. Build the exact-rank chart/no-jump statement explicitly, or keep it as the named hard rung.