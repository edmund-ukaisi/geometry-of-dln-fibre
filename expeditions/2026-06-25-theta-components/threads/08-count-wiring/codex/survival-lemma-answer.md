**1. Recommended Abstract Statement**

Use **`comap` as the public `Set.BijOn` map**, but put the **no-drop hypothesis on the A-side top primes**. Do not use

```lean
∀ P ∈ TopDimMinPrimes S, ...
```

as the main per-prime hypothesis: it is too weak for surjectivity, because for `p ∈ TopDimMinPrimes A` you must prove `map p ∈ TopDimMinPrimes S` before you may apply such a hypothesis.

Recommended wrapper for the away case:

```lean
theorem bijOn_comap_topDimMinPrimes_localizationAway
    {A : Type u} [CommRing A] (f : A)
    (hdim :
      ringKrullDim (Localization.Away f) = ringKrullDim A)
    (havoid :
      ∀ p, p ∈ TopDimMinPrimes A → f ∉ p)
    (hper :
      ∀ p, p ∈ TopDimMinPrimes A →
        ringKrullDim (Localization.Away ((Ideal.Quotient.mk p) f))
          = ringKrullDim (A ⧸ p)) :
    Set.BijOn
      (Ideal.comap (algebraMap A (Localization.Away f)))
      (TopDimMinPrimes (Localization.Away f))
      (TopDimMinPrimes A)
```

Then:

```lean
theorem topDimMinPrimes_localizationAway_ncard_eq ... :
    (TopDimMinPrimes (Localization.Away f)).ncard
      = (TopDimMinPrimes A).ncard :=
  (bijOn_comap_topDimMinPrimes_localizationAway f hdim havoid hper).ncard_eq
```

This keeps the abstract lemma independent of f.g. `k`-domain facts. W1/W2 discharge `hper` by proving `A ⧸ p` is an f.g. domain and `(mk p) f ≠ 0`, then applying your `ringKrullDim_localizationAway_eq_of_fg_domain`.

**2. Bijection Skeleton**

Let `S := Localization.Away f`, `φ := algebraMap A S`, `M := Submonoid.powers f`.

Forward direction, `P ∈ TopDimMinPrimes S`:

```lean
p := P.comap φ
```

Minimality: use

- `IsLocalization.minimalPrimes_map M S (⊥ : Ideal A)` [CONFIDENT exists]
- `Ideal.map_bot` [CONFIDENT exists]

to get `p ∈ minimalPrimes A`.

Top-dimensionality: use the quotient-localization inequality

```lean
ringKrullDim (S ⧸ P) ≤ ringKrullDim (A ⧸ p)
```

derived from the helper below. Then:

```lean
ringKrullDim A
  = ringKrullDim S        -- hdim.symm
  = ringKrullDim (S ⧸ P) -- P top
  ≤ ringKrullDim (A ⧸ p)
  ≤ ringKrullDim A       -- ringKrullDim_le_of_surjective (Ideal.Quotient.mk p)
```

so `p ∈ TopDimMinPrimes A`.

Injectivity: use

- `IsLocalization.map_comap M S P` [CONFIDENT exists]

If `P.comap φ = Q.comap φ`, map both sides back to `S`.

Surjectivity, `p ∈ TopDimMinPrimes A`:

```lean
P := Ideal.map φ p
```

Use `havoid` plus

- `Ideal.disjoint_powers_iff_notMem` [CONFIDENT exists]

to get `Disjoint (M : Set A) (p : Set A)`. Then

- `IsLocalization.comap_map_of_isPrime_disjoint M S` [CONFIDENT exists]

gives `P.comap φ = p`, and `IsLocalization.minimalPrimes_map` gives `P ∈ minimalPrimes S`.

For top-dimensionality:

```lean
ringKrullDim (S ⧸ P)
  = ringKrullDim (Localization.Away ((Ideal.Quotient.mk p) f)) -- helper
  = ringKrullDim (A ⧸ p)                                      -- hper p hp
  = ringKrullDim A                                            -- hp.2
  = ringKrullDim S                                            -- hdim.symm
```

**3. Per-Prime Dim Equality**

I would not rely on a packaged Mathlib theorem named “quotient of localization is localization of quotient”; I did not see a general one in v4.29. Build a small reusable helper.

Best helper:

```lean
theorem ringKrullDim_quotient_map_localizationAway_eq
    {A : Type u} [CommRing A] (f : A) (p : Ideal A) :
    ringKrullDim
      (Localization.Away f ⧸
        Ideal.map (algebraMap A (Localization.Away f)) p)
      =
    ringKrullDim
      (Localization.Away ((Ideal.Quotient.mk p) f))
```

Route:

- show the quotient
  ```lean
  Localization.Away f ⧸ map φ p
  ```
  is an `IsLocalization` of `A ⧸ p` at
  ```lean
  Submonoid.map (Ideal.Quotient.mk p) (Submonoid.powers f)
  ```
  using `IsLocalization.of_surjective` [CONFIDENT exists];
- rewrite that submonoid by `Submonoid.map_powers` [CONFIDENT exists];
- compare with `Localization.Away ((Ideal.Quotient.mk p) f)` using `IsLocalization.algEquiv` [CONFIDENT exists];
- apply `ringKrullDim_eq_of_ringEquiv` [CONFIDENT exists].

Equivalent by-hand route: use `Localization.awayMap (Ideal.Quotient.mk p) f` [CONFIDENT exists], prove surjectivity with `Localization.awayMap_surjective_iff` [CONFIDENT exists], compute its kernel with `IsLocalization.ker_map` [CONFIDENT exists] and `Submonoid.map_powers`, then use `RingHom.quotientKerEquivOfSurjective` [CONFIDENT exists].

**4. v4.29 Pitfalls**

- `IsLocalization.minimalPrimes_map` is a **preimage-under-comap** statement, not a ready-made bijection. Use `map_comap` / `comap_map_of_isPrime_disjoint` for the inverse.
- `map p` can be `⊤` if `f ∈ p`; `havoid` is essential.
- `Localization.Away ((Ideal.Quotient.mk p) f)` often needs help rewriting from `Submonoid.map ... (powers f)` via `Submonoid.map_powers`.
- For W1/W2, after `p ∈ TopDimMinPrimes A`, get `p.IsPrime` from your `isPrime_of_mem_topDimMinPrimes`; then `A ⧸ p` is a domain and `(mk p) f ≠ 0` follows by `Ideal.Quotient.eq_zero_iff_mem` plus `havoid`.
- Keep `hdim` ambient and `hper` per-prime separate. Ambient no-drop never implies the componentwise no-drop.