**Verdict**

The equality is mathematically plausible, but the clean Lean route is **not** “transport heights through `e`”. Use a coordinate-ring predicate:

```lean
TopDimMinPrimes A :=
  {p : Ideal A | p ∈ minimalPrimes A ∧ ringKrullDim (A ⧸ p) = ringKrullDim A}
```

Then convert to/from your ambient “minimal primes of minimal height” only at the two ends.

**Confirmed Mathlib v4.29 names**

Present locally: `IsLocalization.orderIsoOfPrime`, `IsLocalization.minimalPrimes_map`, `IsLocalization.minimalPrimes_comap`, `RingEquiv.height_comap`, `Ideal.minimalPrimes.equivIrreducibleComponents`, `MvPolynomial.mem_map_C_iff`, `MvPolynomial.quotientEquivQuotientMvPolynomial`, `MvPolynomial.ringKrullDim_of_isNoetherianRing`.

Not found as a packaged theorem: minimal primes of `MvPolynomial ι A` over `Ideal.map C I`. Build it.

**Clean Route**

1. **Fibre ambient top primes → fibre coordinate-ring top primes.**  
   Hand lemma:
   ```lean
   topHt_minPrimes_equiv_topDim_quot_radical
   ```
   for `I : Ideal (MvPolynomial σ k)`. Use `Ideal.radical_minimalPrimes`, `Ideal.height_radical`, `DoubleQuot.quotQuotEquivQuotOfLE`, and catenary `height_add_ringKrullDim_quotient_eq_card_of_ne_top`. Apply to `I = fibreGenIdeal d E` and `vanishingIdeal_image_fibre_eq_radical`.

2. **Polynomial extension.**  
   Hand-build:
   ```lean
   MvPolynomial.comap_C_map_C
   MvPolynomial.minimalPrimes_map_C
   topDimMinPrimes_mvPolynomial_equiv
   ```
   Proof of `minimalPrimes_map_C` is short:
   - `comap C (map C q) = q` from `MvPolynomial.mem_map_C_iff`;
   - `map C q` is prime if `q` is prime. Repo already has this as `DLNFibre.Core.SchurSideNoDrop.isPrime_map_C_of_isPrime`; move/generalize it;
   - minimality goes both ways by comparing `q[X] ≤ P` and taking `comap C`.
   Topness is preserved because both quotient dimensions gain `Nat.card ι` via `MvPolynomial.quotientEquivQuotientMvPolynomial` and `MvPolynomial.ringKrullDim_of_isNoetherianRing`.

3. **Schur localization.**  
   Hand lemma:
   ```lean
   topDimMinPrimes_localizationAway_equiv
   ```
   for top primes avoiding `g`. For `gF`, prove **all** top primes avoid it, not just one: if `q` is prime in `Ofib`, then `gF = MvPolynomial.map (algebraMap k Ofib) detSchurS` is not in `Ideal.map C q` because its reduction to `MvPolynomial _ (Ofib ⧸ q)` is nonzero. This is the same argument already inside `ringKrullDim_localizationAway_eq_of_schurSide`.

4. **Chart equivalence.**  
   Use `chartLocalizedAlgEquiv`. Hand lemma:
   ```lean
   topDimMinPrimes_ringEquiv_equiv
   ```
   using quotient ring equivalences and `ringKrullDim_eq_of_ringEquiv`. `RingEquiv.height_comap` is confirmed, but you should not need it here.

5. **Source localization descent.**  
   Same localization lemma. The extra proof obligation is all top exact-rank source components avoid `chartDsig`. Use `chartDsig_not_mem_partitionIdeal` plus the existing recovery theorem `exists_kostantPartition_partitionIdeal_eq_of` instantiated with `cCodim_zero_strict`.

6. **Exact-rank source ↔ closed `Σ̄^r` top components.**  
   Hand bridge:
   ```lean
   topDimMinPrimes_sweepSigma_equiv_topComponents_sigma
   ```
   A top closed component is a corner-`r` partition ideal, hence contains `vanishingIdeal(sweepSigma)` and avoids `chartDsig`. Conversely, a full-dimensional minimal prime over the exact-rank ideal has height `C`, contains `sigmaIdeal`, and is minimal over `sigmaIdeal` by `Ideal.mem_minimalPrimes_of_height_eq`.

**Height / `|δ|` Point**

Do not prove a “height shifts by `|δ|` under polynomial extension” lemma. Literally, for `p ↦ p[X]`, height does **not** shift; coheight/component dimension shifts by `|δ|`. The ambient codimensions differ by `δ` between fibre and sigma, but the polynomial-extension step preserves topness because:

```text
dim ((A[X]) / p[X]) = dim (A / p) + |ι|
dim (A[X])          = dim A       + |ι|
```

So the equality “top = minimal height” should be handled only at the endpoints by catenary.

**Scope**

Full theorem is **several tides**, not one ≤400 LoC tide. The polynomial-extension piece alone is a focused tide. The full route also needs source exact-vs-closed count matching and two endpoint catenary bridges.

Best intermediate theorem to land now:

```lean
/-- Full-dimensional minimal primes are unchanged by adjoining finitely many
variables and inverting a nonzero `k`-polynomial in those variables. -/
noncomputable def topDimMinPrimes_polyAway_equiv
    {k A ι : Type*} [Field k] [CommRing A] [Algebra k A]
    [IsNoetherianRing A] [Algebra.FiniteType k A] [Finite ι]
    (g₀ : MvPolynomial ι k) (hg₀ : g₀ ≠ 0) :
    TopDimMinPrimes A ≃
      TopDimMinPrimes
        (Localization.Away
          (MvPolynomial.map (algebraMap k A) g₀ : MvPolynomial ι A))
```

That isolates the hard fibre-side “extra variables + localization” descent cleanly.

**Cheaper Reformulations**

Defining fibre top components as the image through `e` is cheap but changes the theorem; it does not prove equality with the actual minimal primes of `fibreGenIdeal`. Counting via `OrderIso` helps for localization/ring equivalence, but it does not remove the polynomial-extension minimal-prime lemma. The genuinely cheaper move is the `TopDimMinPrimes` formulation above, which avoids transporting ambient heights through the chart.