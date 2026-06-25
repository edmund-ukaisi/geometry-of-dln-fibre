Yes: I would **avoid proving the component-sup theorem first**. The shortest route in v4.29 is an order/chain proof over `PrimeSpectrum`, using coheight. The radical hypothesis is not needed.

**Recommended Statement**
```lean
theorem height_add_ringKrullDim_quotient_eq_card_of_ne_top
    {σ : Type*} [Finite σ] {k : Type*} [Field k]
    (I : Ideal (MvPolynomial σ k)) (hIne : I ≠ ⊤) :
    (I.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial σ k ⧸ I)
      = (Nat.card σ : WithBot ℕ∞)
```

Then your radical version is just a wrapper ignoring `hI`.

**Key Helpers**
1. **Prime quotient dimension is coheight**
```lean
lemma ringKrullDim_quotient_prime_eq_coheight
    {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] :
    ringKrullDim (R ⧸ p)
      = (Order.coheight (⟨p, inferInstance⟩ : PrimeSpectrum R) : WithBot ℕ∞)
```
Use:
- `ringKrullDim_quotient`
- `Ideal.primeSpectrumQuotientOrderIsoZeroLocus`
- `Order.coheight_eq_krullDim_Ici`
- `zeroLocus p = Set.Ici ⟨p, _⟩`

2. **A minimal prime realizes `I.height`**
```lean
lemma exists_minimalPrime_height_eq_height
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (hIne : I ≠ ⊤) :
    ∃ p ∈ I.minimalPrimes, p.height = I.height
```
Use:
- `Ideal.finite_minimalPrimes_of_isNoetherianRing`
- `Ideal.nonempty_minimalPrimes`
- `Set.Finite.exists_min_image`
- unfold `Ideal.height`
- `Ideal.height_eq_primeHeight` for minimal primes.

**Upper Bound**
Prove:
```lean
(I.height : WithBot ℕ∞) + ringKrullDim (R ⧸ I) ≤ n
```

Make `R ⧸ I` finite-dimensional:
- quotient is nontrivial from `hIne`
- `ringKrullDim (R ⧸ I) ≤ ringKrullDim R = n`
- use `finiteRingKrullDim_iff_ne_bot_and_top`.

Let
```lean
L := LTSeries.longestOf (PrimeSpectrum (R ⧸ I))
```
Then
```lean
ringKrullDim (R ⧸ I) = L.length
```
by `Order.krullDim_eq_length_of_finiteDimensionalOrder`.

Map the chain into `Spec R` via quotient comap:
```lean
L.map (PrimeSpectrum.comap (Ideal.Quotient.mk I))
  (RingHom.strictMono_comap_of_surjective Ideal.Quotient.mk_surjective)
```

Let `q` be its head. Since `I ≤ q.asIdeal`, choose:
```lean
obtain ⟨p, hpmin, hple⟩ := Ideal.exists_minimalPrimes_le ...
```

Then:
```lean
L.length ≤ Order.coheight (⟨p, _⟩ : PrimeSpectrum R)
```
by `Order.length_le_coheight`.

Now use:
```lean
I.height ≤ p.height
```
and prime catenary for `p`:
```lean
(p.height : WithBot ℕ∞) + ringKrullDim (R ⧸ p) = n
```
with helper 1 replacing `ringKrullDim (R ⧸ p)` by coheight.

**Lower Bound**
Pick a minimal prime realizing height:
```lean
obtain ⟨p₀, hp₀min, hp₀height⟩ :=
  exists_minimalPrime_height_eq_height I hIne
```

Since `I ≤ p₀`, there is a surjection:
```lean
R ⧸ I ↠ R ⧸ p₀
```
via `Ideal.Quotient.factor`, so:
```lean
ringKrullDim (R ⧸ p₀) ≤ ringKrullDim (R ⧸ I)
```
by `ringKrullDim_le_of_surjective`.

Prime catenary gives:
```lean
n = (p₀.height : WithBot ℕ∞) + ringKrullDim (R ⧸ p₀)
  = (I.height : WithBot ℕ∞) + ringKrullDim (R ⧸ p₀)
  ≤ (I.height : WithBot ℕ∞) + ringKrullDim (R ⧸ I)
```

Then `le_antisymm`.

**Answers**
Q1: Yes, the `≤` direction of `dim(R/I) = sup dim(R/p_min)` is the real work if you insist on that lemma. There is no landed component-sup theorem; use `LTSeries`/`coheight`, not irreducible-component topology.

Q2: Yes, avoid step 1. The direct coheight/longest-chain proof above is shorter and proves exactly the additive catenary identity.

Q3: Stay in `WithBot ℕ∞` for the catenary theorem. Convert to `ℕ∞` only for `varietyDim` using the existing `unbotD` pattern once you know the quotient is nontrivial.

Q4: I’d prove the general lemma. Estimate: about 100-150 Lean lines with the helpers. Special-casing `sigmaIdeal` may be shorter only because its components are already landed, but for the fibre with no component characterization the general theorem is the clean route.