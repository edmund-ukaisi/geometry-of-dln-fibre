**Route Rank**

Use the dim-based notion for the new transport layer:

```lean
def TopDimMinPrimes (A : Type*) [CommRing A] : Set (Ideal A) :=
  {p | p ∈ minimalPrimes A ∧ ringKrullDim (A ⧸ p) = ringKrullDim A}
```

Keep the existing height-based `topComponents` on the `Σ̄^r` side. Do not rewrite it. Bridge it once to `TopDimMinPrimes (PΣ ⧸ sigmaIdeal d r)`.

For `p ∈ (sigmaIdeal d r).minimalPrimes`, the predicates

```lean
p.height = (cCodim d r h).toNat
ringKrullDim (PΣ ⧸ p) = ringKrullDim (PΣ ⧸ sigmaIdeal d r)
```

are the same in this setting, using the polynomial-ring catenary formula already in the repo (`height_add_ringKrullDim_quotient_eq_card`, plus the reducible-ideal form). They can diverge if you use height inside the coordinate ring `PΣ ⧸ I`: minimal primes there usually have height `0`, so that height is not component codimension. The faithful transport notion is quotient dimension.

**Bijection-Count Shortcut**

Yes, you can avoid computing fibre-prime heights individually. But you cannot avoid proving set-level preservation of `TopDimMinPrimes`.

The clean chain is:

```text
minimisingPartitions d r h
  ≃ topComponents Σ̄^r
  ≃ TopDimMinPrimes (PΣ ⧸ sigmaIdeal d r)
  ≃ TopDimMinPrimes (O(Σ^r)[1/dsig])
  ≃ TopDimMinPrimes ((O(F)[SchurVar])[1/gF])
  ≃ TopDimMinPrimes (O(F)[SchurVar])
  ≃ TopDimMinPrimes O(F)
  ≃ TopDimMinPrimes Q
```

Predicate preservation:

- ring equivalence: `ringKrullDim_eq_of_ringEquiv` plus quotient equivalences;
- polynomial extension: both `A` and `A ⧸ p` gain `Nat.card ι`; confirmed via `MvPolynomial.ringKrullDim_of_isNoetherianRing` and cancellation by `WithBot.add_natCast_cancel`;
- localization: needs all relevant top primes avoid the element and ambient no-drop;
- radical/generator bridge `Q = P/I` to `O(F)=P/rad I`: minimal primes and dimensions are radical-insensitive.

The no-drop lemmas `SourceNoDrop` and `SchurSideNoDrop` give only the ambient number `ringKrullDim S = ringKrullDim R`. They do not by themselves prove every top component survives.

**δ-Shift**

Cheapest route: ideal-level `map C` / `comap C`, not `PrimeSpectrum`.

Hand-prove:

```lean
theorem minimalPrimes_mvPolynomial_eq_map_C
    {A : Type*} [CommRing A] {ι : Type*} :
    minimalPrimes (MvPolynomial ι A)
      = Ideal.map (MvPolynomial.C : A →+* MvPolynomial ι A) '' minimalPrimes A
```

Then:

```lean
noncomputable def topDimMinPrimes_mvPolynomialEquiv
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    {ι : Type*} [Finite ι] :
    {P : Ideal (MvPolynomial ι A) // P ∈ TopDimMinPrimes (MvPolynomial ι A)}
      ≃ {p : Ideal A // p ∈ TopDimMinPrimes A}
```

Verified useful lemmas: `MvPolynomial.ringKrullDim_of_isNoetherianRing`, `MvPolynomial.quotientEquivQuotientMvPolynomial`, `MvPolynomial.mem_map_C_iff`, `MvPolynomial.C_injective`, `WithBot.add_natCast_cancel`.

Missing packaged lemma: minimal primes of `R[X]` / `MvPolynomial ι R`.

**Two Localizations**

Clean sufficient condition:

```lean
(hNoDrop : ringKrullDim (Localization.Away f) = ringKrullDim A)
(havoid : ∀ p ∈ TopDimMinPrimes A, f ∉ p)
```

plus quotient no-drop for surviving minimal primes, which is automatic in your affine finite-type domain quotients by `ringKrullDim_localizationAway_eq_of_fg_domain`.

Then use `IsLocalization.orderIsoOfPrime`, `IsLocalization.minimalPrimes_map`, `IsLocalization.minimalPrimes_comap`.

For `detΔ` on the fibre: already trivial, since it is a unit and `fibreLocalizationAwayDetΔ_algEquiv` gives a ring equivalence.

For `gF`: after polynomial minimal-prime descent, every minimal prime is `Ideal.map C q`; `gF = map (algebraMap k A) detSchurS` avoids it because `detSchurS ≠ 0` remains nonzero over `A ⧸ q`.

For `dsig`: you need the all-top-prime version of the existing source avoidance, not just the one-prime no-drop witness.

**Landing Order**

1. `TopDimMinPrimes` + ring-equiv transport.
   Pure Mathlib wiring: `ringKrullDim_eq_of_ringEquiv`, `Ideal.quotientEquiv`.

2. Ambient quotient bridge:

```lean
topComponents d r h
  ≃ TopDimMinPrimes (MvPolynomial (RepCoord d) k ⧸ sigmaIdeal d r)
```

Uses existing catenary/codim results. Pure wiring.

3. Polynomial minimal-prime descent and top equivalence.
   This is the main Mathlib wall.

4. Localization top-prime equivalence:

```lean
TopDimMinPrimes (Localization.Away f) ≃ TopDimMinPrimes A
```

under `hNoDrop` and `havoid`. Mostly wiring, with a small quotient-localization lemma.

5. Avoidance certificates:
   `gF` all-top avoidance is easy after step 3.
   `dsig` all-top avoidance needs source recovery of every top component.

6. Final assembly:
   chain subtype equivalences, apply `Set.BijOn.ncard_eq`/subtype `Equiv`, then rewrite with `ncard_topComponents_sigma_eq_cTheta_dminus`.

**Indexing Trap**

This is a real thing to check. `RouteCAssembly` / `ClosureBridge` proves dimension equality between exact-rank `Σ^r` and closed `Σ̄^r`; it does not automatically identify top-dimensional minimal primes.

You need one of these set-level bridges:

```lean
Localization.Away (mk (sigmaIdeal d r) Δ)
  ≃ₐ[k] Localization.Away (mk (vanishingIdeal exactRank) Δ)
```

or an equivalent saturation/radical statement after inverting `Δ`.

Also expose or build an unconditional wrapper for the partition bijection: in this tree I only found the gated theorem `bijOn_partitionIdeal_topComponents_of`; if the gates are discharged upstream, make that wrapper available before using it in the transport.