Yes, the mechanism is correct. No mathematical gap: for `x ∈ I_M`, it is enough to find `s ∉ q` with `s ∈ I_j` for every `j ≠ M`. Then `s*x ∈ I_M` because `x ∈ I_M`, and `s*x ∈ I_j` for every other minimal prime because `s ∈ I_j`; hence `s*x` lies in the intersection of all minimal primes, which is `⊥` in a reduced ring.

One simplification: you do **not** need prime avoidance. For each `j ≠ M`, choose `s_j ∈ I_j \ q`; then take `s = ∏ s_j`. Since `q.primeCompl` is multiplicatively closed, `s ∉ q`, and since each `I_j` is an ideal, `s ∈ I_j` for every other component. In Lean this is usually cleaner than `Ideal.subset_union_prime`.

Mathlib route I would use:

```lean
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.RingHom.Surjective
```

Key APIs:

```lean
Ideal.sInf_minimalPrimes
Ideal.isRadical_bot
Ideal.IsPrime.prod_mem_iff
Ideal.prod_mem
IsLocalization.map_eq_zero_iff
Ideal.comap_map_mk
Ideal.isPrime_map_quotientMk_of_isPrime
Localization.localRingHom
RingHom.surjective_localRingHom_of_surjective
IsLocalization.ker_map
RingEquiv.ofBijective
minimalPrimes.finite_of_isNoetherianRing
```

I would split it into two lemmas.

First, prove the component-killing lemma:

```lean
lemma map_eq_bot_localizationAtPrime_of_unique_minimal_le
    {R : Type*} [CommRing R] [IsReduced R]
    (I q : Ideal R) [q.IsPrime]
    (hImin : I ∈ minimalPrimes R)
    (hIq : I ≤ q)
    (huniq : ∀ J ∈ minimalPrimes R, J ≤ q → J = I)
    (hfin : (minimalPrimes R).Finite) :
    I.map (algebraMap R (Localization.AtPrime q)) = ⊥ := by
  -- For x ∈ I, choose product over all minimal primes J ≠ I:
  --   s_J ∈ J \ q
  --   s = ∏ J, s_J
  -- Then s ∉ q by `Ideal.IsPrime.prod_mem_iff`,
  -- and s*x ∈ every minimal prime.
  -- Use:
  --   Ideal.sInf_minimalPrimes
  --   Ideal.isRadical_bot.radical
  -- to conclude s*x = 0.
  --
  -- Finish with:
  --   Ideal.map_eq_bot_iff_le_ker
  --   IsLocalization.map_eq_zero_iff q.primeCompl (Localization.AtPrime q)
  sorry
```

Then the localization quotient equivalence:

```lean
noncomputable def localizationAtPrimeQuotientEquiv
    {R : Type*} [CommRing R]
    (I q : Ideal R) [q.IsPrime]
    (hIq : I ≤ q)
    (hkill : I.map (algebraMap R (Localization.AtPrime q)) = ⊥) :
    Localization.AtPrime q ≃+*
      Localization.AtPrime (q.map (Ideal.Quotient.mk I)) := by
  let π : R →+* R ⧸ I := Ideal.Quotient.mk I
  haveI hqbar : (q.map π).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hIq

  have hcomap : q = (q.map π).comap π := by
    rw [Ideal.comap_map_mk hIq]

  let f : Localization.AtPrime q →+*
      Localization.AtPrime (q.map π) :=
    Localization.localRingHom q (q.map π) π hcomap

  refine RingEquiv.ofBijective f ?_

  constructor
  · -- injective
    -- Clean route:
    -- use `RingHom.injective_iff_ker_eq_bot`,
    -- identify the kernel by `IsLocalization.ker_map`,
    -- rewrite `RingHom.ker π = I` via `Ideal.mk_ker`,
    -- then close with `hkill`.
    sorry

  · -- surjective
    -- `π` is surjective, and localizing a surjective map is surjective.
    -- Use:
    --   RingHom.surjective_localRingHom_of_surjective π Ideal.Quotient.mk_surjective (q.map π)
    -- with a small `convert` using `hcomap`.
    sorry
```

For a `k`-algebra equivalence, use the same proof with:

```lean
Localization.localAlgHom
AlgEquiv.ofBijective
```

provided the `Algebra k R`, quotient algebra, localization algebra, and scalar towers are in place.

On your questions:

1. Correct. The only essential ingredients are finite other minimal primes, `s ∉ q`, and `s*x` in every minimal prime. Reducedness turns the intersection into zero.

2. I would not first try to register `(R ⧸ I)_(q/I)` as an `IsLocalization` of `R` at `q.primeCompl`; it is possible but creates annoying algebra-instance bookkeeping. The idiomatic route is `Localization.localRingHom` plus bijectivity, then `RingEquiv.ofBijective`.

3. Prime avoidance works, but finite product is cleaner. If you need finiteness from Noetherianity, use `minimalPrimes.finite_of_isNoetherianRing`.

4. The “unique minimal prime after localization” route is conceptually nice but not shorter for the iso. `IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes` does not directly apply unless you localize at a minimal prime itself. Your annihilator/product argument is the most direct.

Difficulty: about 80-140 Lean lines for a reusable polished lemma, depending on how abstractly you state the finite minimal-prime family. The main friction is not the algebra; it is Finset bookkeeping and coercions around quotient/localization maps.