# Codex consult — Lean v4.29 proof of the radical-locus catenary `height I + dim(R/I) = n`

Lean 4 + Mathlib v4.29. I need the cleanest proof decomposition (NOT full code) of a catenary identity
for a RADICAL (possibly non-prime, reducible) ideal in a polynomial ring over a field.

## Target

```lean
theorem height_add_ringKrullDim_quotient_eq_card_of_radical
    {σ : Type*} [Finite σ] {k : Type*} [Field k]
    (I : Ideal (MvPolynomial σ k)) (hI : I.IsRadical) (hIne : I ≠ ⊤) :
    (I.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial σ k ⧸ I) = (Nat.card σ : WithBot ℕ∞)
```
(or the `ℕ∞` additive form `I.height + varietyDim = Nat.card σ`, whichever is cleaner). I will apply it
at `I = vanishingIdeal Z` for a nonempty Zariski-closed `Z` (radical over alg-closed `k`), to get
`codimRepCanonical Z + varietyDim Z = card` for REDUCIBLE loci (the fibre `mult⁻¹(E)`, which has
components of dims {10,9,9}, and the rank locus `Σ̄^r`).

## What is LANDED (usable as-is)

- `Ideal.height I = ⨅ J ∈ I.minimalPrimes, primeHeight J` (DEFINITION in Mathlib v4.29 Height.lean).
- PRIME catenary (my engine, PROVED): for `MvPolynomial σ k` with `σ` finite, prime `p`:
  `(p.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial σ k ⧸ p) = Nat.card σ`
  (`height_add_ringKrullDim_quotient_eq_card`).
- `affine_domain_height_add_ringKrullDim_quotient_eq_fintype` (engine): for prime `I`, prime `p` of `R⧸I`:
  `p.height + ringKrullDim((R⧸I)⧸p) = ringKrullDim(R⧸I)`.
- Mathlib: `ringKrullDim_quotient_le`, `ringKrullDim_le_of_surjective`, `ringKrullDim_eq_of_ringEquiv`,
  `Ideal.exists_minimalPrimes_le`, `Ideal.minimalPrimes_isPrime`, `Ideal.nonempty_minimalPrimes`,
  `Ideal.height_mono`, `Ideal.primeHeight_le_ringKrullDim`. `MvPolynomial σ k` is Noetherian
  (finite σ, field) ⟹ `I.minimalPrimes` is FINITE.
- `varietyDim Z = (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0`.

## What Mathlib v4.29 does NOT have (confirmed by grep)

- `ringKrullDim (R⧸I) = ⨆_{p ∈ I.minimalPrimes} ringKrullDim (R⧸p)` — NO such lemma.
- product/tensor Krull-dim additivity — NO.

## My intended decomposition (CRITIQUE / IMPROVE)

The math: `height I = min_p height p` and `dim(R/I) = max_p dim(R/p) = max_p (n − height p) = n − min_p height p`.
So I want, with `p` ranging over minimal primes of `I`:
1. `dim(R/I) = ⨆_{p min} dim(R/p)` — the geometric "dim of a variety = max component dim". The `≥` is
   easy (`I ≤ p` ⟹ surjection `R/I ↠ R/p` ⟹ `dim(R/p) ≤ dim(R/I)`... wait that's the WRONG direction;
   `R/I ↠ R/p` gives `dim(R/p) ≤ dim(R/I)`, good for `⨆ ≤ dim(R/I)`? No — gives each `dim(R/p) ≤ dim(R/I)`
   hence `⨆ ≤ dim(R/I)`). The `≤` (`dim(R/I) ≤ ⨆`) is the chain-lifting: a prime chain in `R/I` lifts to
   a chain of primes `⊇ I`, whose minimum contains a minimal prime `p` of `I`, so the chain embeds in
   `R/p`. **Is this `≤` the hard part? What is the cleanest Mathlib v4.29 handle** (LTSeries / RelSeries
   over PrimeSpectrum, `Order.krullDim`, `PrimeSpectrum.comap` of the quotient map, `minimalPrimes`
   correspondence)? Is there `Order.krullDim`/`ringKrullDim` API that expresses `dim` as a sup over
   minimal elements I'm missing?

2. Then pick a minimal prime `p₀` of MINIMAL height (= `height I`; exists since minimalPrimes finite &
   nonempty). For it: `dim(R/p₀) = n − height p₀ = n − height I` (prime catenary). And for every minimal
   `p`: `height p ≥ height I` ⟹ `dim(R/p) = n − height p ≤ n − height I`. So `⨆ dim(R/p) = n − height I`,
   i.e. `dim(R/I) = n − height I`, i.e. `height I + dim(R/I) = n`.

**Questions:**
(Q1) Is decomposition step 1's `≤` direction (`dim(R/I) ≤ ⨆_{p min} dim(R/p)`) the genuine work, and what
     is the SHORTEST v4.29 route to it? Is there an existing `ringKrullDim_quotient_eq_iSup`-type lemma
     under a different name (associated primes? irreducible components? `PrimeSpectrum` irreducible
     component decomposition `minimalPrimes.equivIrreducibleComponents`)?
(Q2) Can I AVOID step 1 entirely? E.g. is there a more direct additive route: take a maximal chain in
     `R/I` realizing `dim(R/I)`, its bottom prime `q` contains a minimal prime `p` with `height p ≤ height q`
     and the chain has length `≤ coheight q ≤ coheight p = dim(R/p)`... Or use
     `Order.krullDim_eq_iSup_height` / `krullDim = ⨆ coheight of minimals`?
(Q3) Is working in `WithBot ℕ∞` (ringKrullDim) vs `ℕ∞` (height, varietyDim) going to cause friction in
     the `min/max` ↔ `iInf/iSup` duality? Recommend which side to do the arithmetic on.
(Q4) Rough line-count for the cleanest version, and: is there a meaningfully shorter path that proves ONLY
     the two instances I need (`I = vanishingIdeal(fibre E)` reducible, and `I = sigmaIdeal d r` whose
     minimal primes are LANDED-characterized as the maximal orbit closures `Ō_M`, each irreducible with
     the prime catenary already applicable)? For `sigmaIdeal` I can likely get `dim Σ̄^r = card − C`
     directly from the landed `codimRep Σ̄^r = C` + the orbit-closure component structure WITHOUT the
     general radical catenary — is the general lemma still worth it for the `fibre E` instance, or should
     I prove `fibre E`'s catenary by a different route (it has NO landed component characterization)?
